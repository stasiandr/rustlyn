//! Constant evaluation.
//!
//! `const int Limit = 4 * 60;` and `enum Colour { Red, Green = 4, Blue }` both
//! need a value at compile time rather than at run time, and both get it here.
//! The folding is deliberately small: literals, the arithmetic that joins
//! them, and references to other constants. Anything else is not a constant in
//! C# either, so answering `None` is the right answer rather than a gap.
//!
//! Enum members are the reason this cannot live in the emitter. A member with
//! no initializer is one more than the member before it, which means the whole
//! run has to be evaluated in declaration order — and the semantic model wants
//! the same answers the backend does.

use std::collections::HashSet;

use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use crate::binder::Binder;
use crate::bound::{
    BoundExpression, BoundExpressionKind, ConstantValue, SpecialConstant, UnaryOperator,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

thread_local! {
    /// The constants being worked out on this thread, innermost last, each
    /// with the compilation it belongs to.
    static EVALUATING: std::cell::RefCell<Vec<(usize, SymbolId)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

impl Binder<'_> {
    /// The value of a `const` field or an enum member, if it has one.
    #[must_use]
    pub fn constant_value(&self, symbol: SymbolId) -> Option<ConstantValue> {
        if let Some(cached) = self.compilation().cached_constant(symbol) {
            return cached;
        }
        let value = self.constant_value_with(symbol, &mut HashSet::new());
        self.compilation().cache_constant(symbol, value.clone());
        value
    }

    fn constant_value_with(
        &self,
        symbol: SymbolId,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<ConstantValue> {
        // One member written in terms of another is how a flags enum is
        // written, and each of those asks again from here. Without the cache
        // on this path the walk is the whole enum every time.
        if let Some(cached) = self.compilation().cached_constant(symbol) {
            return cached;
        }
        let compilation = self.compilation();
        let symbols = compilation.symbols();
        let detail = symbols.get(symbol);
        if detail.kind != SymbolKind::Field {
            return None;
        }
        // A constant that refers to itself has no value; without this the
        // recursion would not end. The set passed down covers one fold; the
        // one kept per thread covers a fold that binds an initializer, whose
        // conversions fold again from scratch.
        let key = (std::ptr::from_ref(compilation) as usize, symbol);
        if !visiting.insert(symbol) || EVALUATING.with_borrow(|stack| stack.contains(&key)) {
            // Everything being worked out since this one was first asked
            // for is the circle it is on (CS0110).
            let circle: Vec<SymbolId> = EVALUATING.with_borrow(|stack| {
                stack.iter().position(|entry| *entry == key).map_or_else(
                    || vec![symbol],
                    |start| {
                        stack[start..]
                            .iter()
                            .filter(|(owner, _)| *owner == key.0)
                            .map(|(_, member)| *member)
                            .collect()
                    },
                )
            });
            compilation.note_circular_constants(circle);
            return None;
        }
        EVALUATING.with_borrow_mut(|stack| stack.push(key));
        let value = self.constant_value_uncached(symbol, visiting);
        EVALUATING.with_borrow_mut(|stack| stack.pop());
        value
    }

    fn constant_value_uncached(
        &self,
        symbol: SymbolId,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<ConstantValue> {
        let compilation = self.compilation();
        let symbols = compilation.symbols();
        let detail = symbols.get(symbol);

        // A field out of a referenced assembly has no syntax to fold: what it
        // holds was written into the `Constant` table when that assembly was
        // made, and read back when it was loaded.
        if let Some(value) = compilation.metadata_constant(symbol) {
            let value = value.clone();
            visiting.remove(&symbol);
            compilation.cache_constant(symbol, Some(value.clone()));
            return Some(value);
        }

        let container = detail.container?;
        let in_enum = symbols.get(container).type_kind() == Some(TypeKind::Enum);
        if !in_enum && !detail.modifiers.contains(Modifiers::CONST) {
            visiting.remove(&symbol);
            return None;
        }

        let value = if in_enum {
            self.enum_member_value(container, symbol, visiting)
        } else {
            self.initializer_value(symbol, visiting)
        };
        visiting.remove(&symbol);
        // Only once nothing above is still being worked out: a value reached
        // through a cycle is not the value.
        if visiting.is_empty() {
            self.compilation().cache_constant(symbol, value.clone());
        }
        value
    }

    /// An enum member's value: what it was given, or one more than the member
    /// before it.
    fn enum_member_value(
        &self,
        container: SymbolId,
        member: SymbolId,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<ConstantValue> {
        let symbols = self.compilation().symbols();
        // A member is a constant of the enum's underlying type, and that is
        // not always `int`: `enum BinderFlags : uint` has a member of
        // `1u << 31`, which no `int` holds.
        let underlying = self
            .enum_underlying(&crate::types::Type::named(container))
            .unwrap_or_else(|| {
                self.compilation()
                    .special_type(crate::corlib::SpecialType::Int32)
                    .map_or(crate::types::Type::Error, crate::types::Type::named)
            });
        let fields: Vec<SymbolId> = symbols
            .get(container)
            .members
            .iter()
            .copied()
            .filter(|&candidate| symbols.get(candidate).kind == SymbolKind::Field)
            .collect();
        let index = fields.iter().position(|&candidate| candidate == member)?;
        // Only the members since the last one with a value of its own count:
        // walking back to it, rather than forward from the first member,
        // never evaluates a member after it. `A = B, B = 1` is legal, and a
        // forward walk asked for `B` would evaluate `A`, which asks for `B`.
        // The value so far, as the bits of a 64-bit integer: an `enum :
        // ulong` goes past `long.MaxValue`, where `0xFFFFFFFFFFFFFFF0` is a
        // value like any other and no `long` at all.
        let unsigned_wide = self.special_of(&underlying) == Some(SpecialType::UInt64);
        let mut start = index;
        let mut previous: i64 = -1;
        loop {
            let candidate = fields[start];
            if candidate != member
                && let Some(cached) = self.compilation().cached_constant(candidate)
            {
                previous = as_bits(&cached?)?;
                start += 1;
                break;
            }
            if self.has_initializer(candidate) {
                let value = if candidate == member {
                    self.initializer_value(candidate, visiting)?
                } else {
                    self.constant_value_with(candidate, visiting)?
                };
                previous = as_bits(&value)?;
                if candidate == member {
                    return Some(integer_like(&underlying, previous, self));
                }
                start += 1;
                break;
            }
            if start == 0 {
                break;
            }
            start -= 1;
        }
        for &candidate in &fields[start..=index] {
            previous = if unsigned_wide {
                (previous as u64).checked_add(1)? as i64
            } else {
                previous.checked_add(1)?
            };
            let constant = integer_like(&underlying, previous, self);
            if candidate == member {
                return Some(constant);
            }
            // Keeping the members on the way is what stops the next question
            // walking the same run again.
            if !visiting.contains(&candidate) {
                self.compilation().cache_constant(candidate, Some(constant));
            }
        }
        None
    }

    /// Whether a field's declaration gives it a value: `= ...`.
    pub(crate) fn has_initializer(&self, field: SymbolId) -> bool {
        let compilation = self.compilation();
        let Some(&(tree, span)) = compilation.declaration_nodes(field).first() else {
            return false;
        };
        compilation
            .trees()
            .get(tree)
            .and_then(|tree| tree.root().find_node(span))
            .is_some_and(|node| node.child_of_kind(SyntaxKind::EqualsValueClause).is_some())
    }

    /// The value of a field's `= ...`, folded.
    fn initializer_value(
        &self,
        field: SymbolId,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<ConstantValue> {
        let compilation = self.compilation();
        let (tree, span) = *compilation.declaration_nodes(field).first()?;
        let node = compilation.trees().get(tree)?.root().find_node(span)?;
        // No `= ...` means no value of its own; an enum member then takes one
        // from the member before it.
        node.child_of_kind(SyntaxKind::EqualsValueClause)?;
        // Binding the initializer is what resolves the names inside it, which
        // is how one constant can be written in terms of another.
        let body = crate::body::BodyBinder::bind_member(self, tree, &node);
        let value = body
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                crate::bound::BoundStatementKind::Return(Some(value)) => Some(value.clone()),
                _ => None,
            })?;
        self.fold(&value, visiting)
    }

    /// The `decimal` or `DateTime` constant a field or a parameter has: a
    /// `const decimal` field's value, an optional `decimal` parameter's
    /// `= 1.5m`, or what a `[DecimalConstant]` or `[DateTimeConstant]` on an
    /// `[Optional]` parameter says. Metadata writes neither in a `Constant`
    /// row, since neither is a CLR primitive.
    #[must_use]
    pub fn special_constant(&self, symbol: SymbolId) -> Option<SpecialConstant> {
        self.special_constant_with(symbol, &mut HashSet::new())
    }

    fn special_constant_with(
        &self,
        symbol: SymbolId,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<SpecialConstant> {
        let compilation = self.compilation();
        if let Some(value) = compilation.metadata_special_constant(symbol) {
            return Some(value);
        }
        if !visiting.insert(symbol) {
            return None;
        }
        let symbols = compilation.symbols();
        let detail = symbols.get(symbol);
        let (tree, span) = *compilation.declaration_nodes(symbol).first()?;
        let node = compilation.trees().get(tree)?.root().find_node(span)?;
        let mut sink = crate::Diagnostics::new();
        let ty = self.type_of(symbol, &mut sink);
        let decimal = self.special_of(&ty) == Some(SpecialType::Decimal);
        match detail.kind {
            SymbolKind::Parameter => {
                if let Some(attribute) =
                    crate::declare::parameter_attribute(&node, "DecimalConstant")
                        .or_else(|| crate::declare::parameter_attribute(&node, "DateTimeConstant"))
                {
                    return self.attribute_special(tree, &node, &attribute);
                }
                if !decimal {
                    return None;
                }
                let expression = node
                    .child_of_kind(SyntaxKind::EqualsValueClause)?
                    .children()
                    .find(|child| child.kind().is_expression())?;
                let value =
                    crate::body::BodyBinder::bind_lone_expression(self, tree, &node, &expression);
                self.decimal_of(&value, visiting)
            }
            SymbolKind::Field if decimal && detail.modifiers.contains(Modifiers::CONST) => {
                node.child_of_kind(SyntaxKind::EqualsValueClause)?;
                let body = crate::body::BodyBinder::bind_member(self, tree, &node);
                let value = body
                    .statements
                    .iter()
                    .find_map(|statement| match &statement.kind {
                        crate::bound::BoundStatementKind::Return(Some(value)) => {
                            Some(value.clone())
                        }
                        _ => None,
                    })?;
                self.decimal_of(&value, visiting)
            }
            _ => None,
        }
    }

    /// A bound `decimal` expression as the constant it is, where it is one.
    pub(crate) fn decimal_constant(&self, value: &BoundExpression) -> Option<SpecialConstant> {
        self.decimal_of(value, &mut HashSet::new())
    }

    /// A bound `decimal` expression as the constant it is, where it is one:
    /// a literal (`new decimal(lo, mid, hi, negative, scale)`), a negated
    /// one, an integer constant converted, or another `decimal` constant.
    fn decimal_of(
        &self,
        value: &BoundExpression,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<SpecialConstant> {
        match &value.kind {
            BoundExpressionKind::ObjectCreation { arguments, .. } if arguments.len() == 5 => {
                let parts: Vec<i64> = arguments
                    .iter()
                    .map(|argument| as_integer(&self.folded(argument)?))
                    .collect::<Option<_>>()?;
                Some(SpecialConstant::Decimal {
                    lo: parts[0] as u32,
                    mid: parts[1] as u32,
                    hi: parts[2] as u32,
                    negative: parts[3] != 0,
                    scale: u8::try_from(parts[4]).ok()?,
                })
            }
            BoundExpressionKind::Field { field, .. } => {
                self.special_constant_with(*field, visiting)
            }
            BoundExpressionKind::Unary {
                operator: UnaryOperator::Minus,
                operand,
                ..
            } => match self.decimal_of(operand, visiting)? {
                SpecialConstant::Decimal {
                    scale,
                    negative,
                    hi,
                    mid,
                    lo,
                } => Some(SpecialConstant::Decimal {
                    scale,
                    negative: !negative,
                    hi,
                    mid,
                    lo,
                }),
                SpecialConstant::DateTime(_) => None,
            },
            BoundExpressionKind::Call {
                method, arguments, ..
            } if arguments.len() == 1
                && self.compilation().symbols().get(*method).name == "op_UnaryNegation" =>
            {
                match self.decimal_of(&arguments[0], visiting)? {
                    SpecialConstant::Decimal {
                        scale,
                        negative,
                        hi,
                        mid,
                        lo,
                    } => Some(SpecialConstant::Decimal {
                        scale,
                        negative: !negative,
                        hi,
                        mid,
                        lo,
                    }),
                    SpecialConstant::DateTime(_) => None,
                }
            }
            BoundExpressionKind::Conversion { operand, .. } => {
                if let Some(inner) = self.decimal_of(operand, visiting) {
                    return Some(inner);
                }
                let whole = as_integer(&self.folded(operand)?)?;
                let magnitude = whole.unsigned_abs();
                Some(SpecialConstant::Decimal {
                    scale: 0,
                    negative: whole < 0,
                    hi: 0,
                    mid: (magnitude >> 32) as u32,
                    lo: magnitude as u32,
                })
            }
            _ => {
                // `const decimal x = 5;` folds to the integer it was written as.
                let whole = as_integer(&self.folded(value)?)?;
                let magnitude = whole.unsigned_abs();
                Some(SpecialConstant::Decimal {
                    scale: 0,
                    negative: whole < 0,
                    hi: 0,
                    mid: (magnitude >> 32) as u32,
                    lo: magnitude as u32,
                })
            }
        }
    }

    /// Where a parameter's default value is written: its `= value`, or the
    /// argument of an `[Optional, DefaultParameterValue(value)]` on it. The tree, the
    /// parameter's syntax and the expression.
    #[must_use]
    pub fn parameter_default_syntax(
        &self,
        parameter: SymbolId,
    ) -> Option<(usize, SyntaxNode, SyntaxNode)> {
        let compilation = self.compilation();
        let (tree, span) = *compilation.declaration_nodes(parameter).first()?;
        let node = compilation.trees().get(tree)?.root().find_node(span)?;
        let expression = match node.child_of_kind(SyntaxKind::EqualsValueClause) {
            Some(clause) => clause
                .children()
                .find(|child| child.kind().is_expression())?,
            None => crate::declare::attributed_default(&node)?,
        };
        Some((tree, node, expression))
    }

    /// The `= value` of an optional parameter, bound where it is written.
    #[must_use]
    pub fn parameter_default_expression(&self, parameter: SymbolId) -> Option<BoundExpression> {
        let (tree, node, expression) = self.parameter_default_syntax(parameter)?;
        Some(crate::body::BodyBinder::bind_lone_expression(
            self,
            tree,
            &node,
            &expression,
        ))
    }

    /// The `= value` of an optional parameter as a constant of the
    /// parameter's own type, where it folds to one: `long limit = 5` is an
    /// `Int64`, and `double scale = 2` a `Double`. `None` for a default that
    /// is not a constant (`default(CancellationToken)`), which metadata
    /// records as a null.
    #[must_use]
    pub fn parameter_default(&self, parameter: SymbolId) -> Option<ConstantValue> {
        let compilation = self.compilation();
        if parameter.is_late() {
            return compilation.anonymous_delegate_default(parameter);
        }
        let (tree, node, expression) = self.parameter_default_syntax(parameter)?;
        let value = crate::body::BodyBinder::bind_lone_expression(self, tree, &node, &expression);
        let folded = self.folded(&value)?;
        let mut sink = crate::Diagnostics::new();
        let ty = self.type_of(parameter, &mut sink);
        Some(self.constant_as(folded, &ty))
    }

    /// The `decimal` or `DateTime` a `[DecimalConstant(...)]` or
    /// `[DateTimeConstant(...)]` on a parameter's syntax says — a method's,
    /// or a lambda's, which has no symbol. Its arguments are read in the
    /// constructor's parameters' order: a named one (`low: 100`) goes where
    /// its parameter is.
    #[must_use]
    pub fn attribute_special(
        &self,
        tree: usize,
        node: &SyntaxNode,
        attribute: &SyntaxNode,
    ) -> Option<SpecialConstant> {
        let name = attribute.children().next()?.text().to_string();
        let name = name
            .trim()
            .rsplit('.')
            .next()?
            .trim_end_matches("Attribute");
        let parameters: &[&str] = match name {
            "DecimalConstant" => &["scale", "sign", "hi", "mid", "low"],
            "DateTimeConstant" => &["ticks"],
            _ => return None,
        };
        let list = attribute.child_of_kind(SyntaxKind::AttributeArgumentList)?;
        let mut values = vec![None; parameters.len()];
        for (position, argument) in list
            .children()
            .filter(|child| child.kind() == SyntaxKind::AttributeArgument)
            .enumerate()
        {
            let at = match argument.child_of_kind(SyntaxKind::NameColon) {
                Some(named) => {
                    let text = named.text().to_string();
                    let written = text.trim().trim_end_matches(':').trim();
                    parameters
                        .iter()
                        .position(|parameter| *parameter == written)?
                }
                None => position,
            };
            let expression = argument
                .children()
                .find(|child| child.kind().is_expression())?;
            let value =
                crate::body::BodyBinder::bind_lone_expression(self, tree, node, &expression);
            *values.get_mut(at)? = Some(as_integer(&self.folded(&value)?)?);
        }
        let values: Vec<i64> = values.into_iter().collect::<Option<_>>()?;
        match values[..] {
            [scale, sign, hi, mid, lo] => Some(SpecialConstant::Decimal {
                scale: u8::try_from(scale).ok()?,
                negative: sign != 0,
                hi: hi as u32,
                mid: mid as u32,
                lo: lo as u32,
            }),
            [ticks] => Some(SpecialConstant::DateTime(ticks)),
            _ => None,
        }
    }

    /// A folded constant as a value of `ty`: `5` given to a `long` is an
    /// `Int64`, and `2` given to a `double` a `Double`.
    #[must_use]
    pub fn constant_as(&self, folded: ConstantValue, ty: &Type) -> ConstantValue {
        let compilation = self.compilation();
        let ty = self.enum_underlying(ty).unwrap_or_else(|| ty.clone());
        let ty = self.nullable_underlying(&ty).unwrap_or(ty);
        let special = ty.symbol().and_then(|symbol| {
            SpecialType::ALL
                .iter()
                .copied()
                .find(|special| compilation.special_type(*special) == Some(symbol))
        });
        match (&folded, special) {
            (ConstantValue::String(_) | ConstantValue::Null | ConstantValue::Boolean(_), _) => {
                folded
            }
            (ConstantValue::Double(_), Some(SpecialType::Double)) => folded,
            (ConstantValue::Single(_), Some(SpecialType::Single)) => folded,
            (ConstantValue::Double(value), Some(SpecialType::Single)) => {
                ConstantValue::Single(*value as f32)
            }
            (ConstantValue::Single(value), Some(SpecialType::Double)) => {
                ConstantValue::Double(f64::from(*value))
            }
            (_, Some(SpecialType::Double)) => {
                ConstantValue::Double(as_integer(&folded).map_or(0.0, |value| value as f64))
            }
            (_, Some(SpecialType::Single)) => {
                ConstantValue::Single(as_integer(&folded).map_or(0.0, |value| value as f32))
            }
            (_, Some(SpecialType::Byte)) => {
                ConstantValue::Int32(as_bits(&folded).unwrap_or(0) as u8 as i32)
            }
            (_, Some(SpecialType::SByte)) => {
                ConstantValue::Int32(as_bits(&folded).unwrap_or(0) as i8 as i32)
            }
            (_, Some(SpecialType::Int16)) => {
                ConstantValue::Int32(as_bits(&folded).unwrap_or(0) as i16 as i32)
            }
            (_, Some(SpecialType::UInt16)) => {
                ConstantValue::Int32(as_bits(&folded).unwrap_or(0) as u16 as i32)
            }
            _ => match as_bits(&folded) {
                Some(value) => integer_like(&ty, value, self),
                None => folded,
            },
        }
    }

    /// A floating constant as a value of the integral type `ty` (or of an
    /// enum over one): the fraction dropped. A value the type has no room
    /// for — which only `unchecked` lets through, CS0221 otherwise — and a
    /// NaN are zero, which is what Roslyn folds them to: the language
    /// leaves the result unspecified (§10.3.2), and the runtime's own
    /// answer has changed between versions. `None` where `ty` is not
    /// integral.
    fn truncated(&self, folded: &ConstantValue, ty: &Type) -> Option<ConstantValue> {
        let value = as_float(folded)?.trunc();
        let ty = self.enum_underlying(ty).unwrap_or_else(|| ty.clone());
        // The bounds as the powers of two they are: `long.MaxValue` itself
        // is no `double`, and the one next to it is one past the range.
        let two = |power: i32| 2f64.powi(power);
        let (low, past) = match self.special_of(&ty)? {
            SpecialType::SByte => (-two(7), two(7)),
            SpecialType::Byte => (0.0, two(8)),
            SpecialType::Int16 => (-two(15), two(15)),
            SpecialType::UInt16 | SpecialType::Char => (0.0, two(16)),
            SpecialType::Int32 => (-two(31), two(31)),
            SpecialType::UInt32 => (0.0, two(32)),
            SpecialType::Int64 => (-two(63), two(63)),
            SpecialType::UInt64 => (0.0, two(64)),
            _ => return None,
        };
        let bits = if value >= low && value < past {
            if low < 0.0 {
                value as i64
            } else {
                (value as u64) as i64
            }
        } else {
            0
        };
        Some(integer_like(&ty, bits, self))
    }

    /// Whether an integer constant lies outside the integral type `ty`: an
    /// unchecked conversion to it wraps, `unchecked((uint)-1)` is the `uint`
    /// 4294967295 and not the `int` it was written as.
    fn out_of_range(&self, folded: &ConstantValue, ty: &Type) -> bool {
        let ty = self.enum_underlying(ty).unwrap_or_else(|| ty.clone());
        let (low, high): (i128, i128) = match self.special_of(&ty) {
            Some(SpecialType::SByte) => (i8::MIN.into(), i8::MAX.into()),
            Some(SpecialType::Byte) => (u8::MIN.into(), u8::MAX.into()),
            Some(SpecialType::Int16) => (i16::MIN.into(), i16::MAX.into()),
            Some(SpecialType::UInt16 | SpecialType::Char) => (u16::MIN.into(), u16::MAX.into()),
            Some(SpecialType::Int32) => (i32::MIN.into(), i32::MAX.into()),
            Some(SpecialType::UInt32) => (u32::MIN.into(), u32::MAX.into()),
            Some(SpecialType::Int64) => (i64::MIN.into(), i64::MAX.into()),
            Some(SpecialType::UInt64) => (u64::MIN.into(), u64::MAX.into()),
            _ => return false,
        };
        let value: i128 = match folded {
            ConstantValue::Int32(value) => (*value).into(),
            ConstantValue::UInt32(value) => (*value).into(),
            ConstantValue::Int64(value) => (*value).into(),
            ConstantValue::UInt64(value) => (*value).into(),
            _ => return false,
        };
        value < low || value > high
    }

    /// The element count of `fixed byte Buffer[N]`, folded, for a field
    /// declared `fixed`.
    #[must_use]
    pub fn fixed_buffer_length(&self, field: SymbolId) -> Option<i64> {
        let compilation = self.compilation();
        let (tree, span) = *compilation.declaration_nodes(field).first()?;
        let node = compilation.trees().get(tree)?.root().find_node(span)?;
        let list = node.child_of_kind(SyntaxKind::BracketedArgumentList)?;
        let argument = list.child_of_kind(SyntaxKind::Argument)?;
        let expression = argument
            .children()
            .find(|child| child.kind().is_expression())?;
        let value = crate::body::BodyBinder::bind_lone_expression(self, tree, &node, &expression);
        as_integer(&self.folded(&value)?)
    }

    /// The value of an expression, where it has one at compile time.
    ///
    /// `-300` is not a literal — it is a negation of one — and the difference
    /// matters wherever the language says "constant" rather than "literal".
    #[must_use]
    pub fn folded(&self, expression: &BoundExpression) -> Option<ConstantValue> {
        self.fold(expression, &mut HashSet::new())
    }

    /// What a `case` label of a `switch` over `input` and a `goto case`
    /// in it are matched by: the constant as a value of the type it is
    /// tested in, with that type. That is the switch's own type (the
    /// underlying one of a nullable), except where getting there would box
    /// the constant — a switch over `object` tests a `(short)2` as a
    /// `short`, as Roslyn's `ConvertPatternExpression` keeps the operand of
    /// a boxing, so `case (short)2` and `case (byte)2` are two labels, and
    /// `goto case (byte)2` goes to the second.
    #[must_use]
    pub fn case_key(&self, value: &BoundExpression, input: &Type) -> Option<(Type, ConstantValue)> {
        let folded = self.folded(value)?;
        if matches!(folded, ConstantValue::Null) {
            return Some((Type::Null, folded));
        }
        let input = self
            .nullable_underlying(input)
            .unwrap_or_else(|| input.clone());
        let tested_as_itself = self.enum_underlying(&input).is_some()
            || self.native_int(&input).is_some()
            || self
                .special_of(&input)
                .is_some_and(|special| special != SpecialType::Object);
        let ty = if tested_as_itself {
            input
        } else {
            value.ty.clone()
        };
        let constant = self.constant_as(folded, &ty);
        Some((ty, constant))
    }

    /// Folds an expression to a value, or answers `None` where it is not one.
    fn fold(
        &self,
        expression: &BoundExpression,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<ConstantValue> {
        match &expression.kind {
            BoundExpressionKind::Literal(value) => Some(value.clone()),
            // `default(int)` is the constant zero of its type, and
            // `default(string)` the constant null (§12.23).
            // So is `new int()` — `case new():` on an `int` is `case 0:`.
            BoundExpressionKind::ObjectCreation {
                constructor: None,
                arguments,
                initializers,
            } if arguments.is_empty()
                && initializers.is_empty()
                && self.special_of(&expression.ty).is_some() =>
            {
                let default = BoundExpression::new(
                    BoundExpressionKind::Default(expression.ty.clone()),
                    expression.ty.clone(),
                    expression.span,
                );
                self.fold(&default, visiting)
            }
            BoundExpressionKind::Default(_) => {
                let ty = &expression.ty;
                match self.special_of(ty) {
                    Some(SpecialType::Single) => Some(ConstantValue::Single(0.0)),
                    Some(SpecialType::Double) => Some(ConstantValue::Double(0.0)),
                    Some(SpecialType::String | SpecialType::Object) => Some(ConstantValue::Null),
                    Some(SpecialType::Char) => Some(ConstantValue::Char('\0')),
                    Some(
                        SpecialType::SByte
                        | SpecialType::Byte
                        | SpecialType::Int16
                        | SpecialType::UInt16
                        | SpecialType::Int32
                        | SpecialType::UInt32
                        | SpecialType::Int64
                        | SpecialType::UInt64
                        | SpecialType::Boolean,
                    ) => Some(integer_like(ty, 0, self)),
                    Some(_) => None,
                    None if self.enum_underlying(ty).is_some() => Some(integer_like(ty, 0, self)),
                    None => None,
                }
            }
            // A conversion between two integer widths keeps the value; the
            // width is the declared type's business, not the folder's. Only
            // a narrowing makes it the narrower type's: `(int)42L` is the
            // `int` 42, which reaches a `byte` as any `int` constant that
            // fits does, and `unchecked((byte)-1)` is 255, not the `int` -1
            // it was written as.
            BoundExpressionKind::Conversion { operand, .. } => {
                let folded = self.fold(operand, visiting)?;
                // A floating constant into an integral type is cut off
                // toward zero (§10.3.2): `(int)3.7` is the `int` 3. Kept as
                // the `3.7` it was written as, `(int)3.7 + 0.5` came to 4.2
                // and `const int n = (int)3.7;` loaded a `double` where the
                // `int` goes.
                if let ConstantValue::Single(_) | ConstantValue::Double(_) = folded
                    && let Some(cut) = self.truncated(&folded, &expression.ty)
                {
                    return Some(cut);
                }
                // And between the two floating types it is the nearest the
                // target has: `(float)0.1` is `0.1f`, not the `double` it
                // was written as, which no `float` equals.
                match (&folded, self.special_of(&expression.ty)) {
                    (ConstantValue::Double(value), Some(SpecialType::Single)) => {
                        return Some(ConstantValue::Single(*value as f32));
                    }
                    (ConstantValue::Single(value), Some(SpecialType::Double)) => {
                        return Some(ConstantValue::Double(f64::from(*value)));
                    }
                    _ => {}
                }
                let target = self.special_of(&expression.ty);
                let narrowed = match folded {
                    ConstantValue::Int64(_)
                    | ConstantValue::UInt64(_)
                    | ConstantValue::UInt32(_) => matches!(
                        target,
                        Some(
                            SpecialType::Int32
                                | SpecialType::Int16
                                | SpecialType::UInt16
                                | SpecialType::SByte
                                | SpecialType::Byte
                                | SpecialType::Char
                        )
                    ),
                    ConstantValue::Int32(_) => matches!(
                        target,
                        Some(
                            SpecialType::Int16
                                | SpecialType::UInt16
                                | SpecialType::SByte
                                | SpecialType::Byte
                                | SpecialType::Char
                        )
                    ),
                    _ => false,
                } || self.out_of_range(&folded, &expression.ty);
                Some(if narrowed {
                    self.constant_as(folded, &expression.ty)
                } else {
                    folded
                })
            }
            BoundExpressionKind::Field { field, .. } => self.constant_value_with(*field, visiting),
            // `sizeof(int)` is a constant for the built-in types (§12.8.19):
            // `const int IntSize = sizeof(int) * 8;` folds.
            BoundExpressionKind::SizeOf(ty) => {
                let size = match self.special_of(ty)? {
                    SpecialType::SByte | SpecialType::Byte | SpecialType::Boolean => 1,
                    SpecialType::Int16 | SpecialType::UInt16 | SpecialType::Char => 2,
                    SpecialType::Int32 | SpecialType::UInt32 | SpecialType::Single => 4,
                    SpecialType::Int64 | SpecialType::UInt64 | SpecialType::Double => 8,
                    SpecialType::Decimal => 16,
                    _ => return None,
                };
                Some(ConstantValue::Int32(size))
            }
            BoundExpressionKind::Unary { operator, operand } => {
                let folded = self.fold(operand, visiting)?;
                if let Some(width) = self.floating_width(&expression.ty) {
                    let value = as_float(&folded)?;
                    let value = match operator {
                        UnaryOperator::Plus => value,
                        UnaryOperator::Minus => -value,
                        _ => return None,
                    };
                    return Some(floating(width, value));
                }
                // `~0xFFFFFFFFFFFFFFFF` turns bits over, whatever number
                // they spell.
                if *operator == UnaryOperator::BitwiseNot {
                    let ty = self
                        .enum_underlying(&expression.ty)
                        .unwrap_or_else(|| expression.ty.clone());
                    return Some(integer_like(&ty, !as_bits(&folded)?, self));
                }
                let value = as_integer(&folded)?;
                let value = match operator {
                    UnaryOperator::Plus => value,
                    UnaryOperator::Minus => value.checked_neg()?,
                    UnaryOperator::BitwiseNot => !value,
                    UnaryOperator::LogicalNot => match folded {
                        ConstantValue::Boolean(value) => {
                            return Some(ConstantValue::Boolean(!value));
                        }
                        _ => return None,
                    },
                };
                Some(integer_like(&expression.ty, value, self))
            }
            // `true ? "" : "ABC"` is the branch its constant condition takes.
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } => match self.fold(condition, visiting)? {
                ConstantValue::Boolean(true) => self.fold(consequence, visiting),
                ConstantValue::Boolean(false) => self.fold(alternative, visiting),
                _ => None,
            },
            // `$"a{B}"` whose holes hold nothing but constant strings, with no
            // alignment or format, is a constant itself (C# 10), and so is an
            // addition of such.
            BoundExpressionKind::InterpolatedString(parts) => {
                let mut text = String::new();
                for part in parts {
                    match &part.kind {
                        BoundExpressionKind::Literal(ConstantValue::String(piece)) => {
                            text.push_str(piece);
                        }
                        BoundExpressionKind::StringInsert {
                            value,
                            alignment: None,
                            format: None,
                        } => match self.fold(value, visiting)? {
                            ConstantValue::String(piece) => text.push_str(&piece),
                            _ => return None,
                        },
                        _ => return None,
                    }
                }
                Some(ConstantValue::String(text))
            }
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Add,
                left,
                right,
            } if expression.is_interpolated_string() => {
                let right = self.fold(right, visiting)?;
                match (self.fold(left, visiting)?, right) {
                    (ConstantValue::String(left), ConstantValue::String(right)) => {
                        Some(ConstantValue::String(left + &right))
                    }
                    _ => None,
                }
            }
            BoundExpressionKind::Binary {
                operator,
                left,
                right,
            } => {
                // The right first: in a long `a + b + c` it is the leaf, and a
                // chain that is not constant is turned down at once instead of
                // being folded again, all of it, at every operator.
                let right = self.fold(right, visiting)?;
                let left = self.fold(left, visiting)?;
                // Comparisons, `&&` and `||` of constants are constants too
                // (§12.25): `if (Interval % Step != 0)` never runs its body.
                if let Some(value) = compare(*operator, &left, &right) {
                    return Some(ConstantValue::Boolean(value));
                }
                // `"a" + "b"` is the constant `"ab"`, and a `null` among
                // strings is the empty one (§12.12.5).
                if *operator == BinaryOperator::Add
                    && self.special_of(&expression.ty) == Some(SpecialType::String)
                {
                    let text = |value: &ConstantValue| match value {
                        ConstantValue::String(text) => Some(text.clone()),
                        ConstantValue::Null => Some(String::new()),
                        _ => None,
                    };
                    return Some(ConstantValue::String(text(&left)? + &text(&right)?));
                }
                // `0.0 / 0.0` is a NaN and `1.0 / 0.0` an infinity, not
                // errors: floating point folds in its own width.
                if let Some(width) = self.floating_width(&expression.ty) {
                    let (left, right) = (as_float(&left)?, as_float(&right)?);
                    let value = match (width, operator) {
                        (Width::Single, BinaryOperator::Add) => {
                            f64::from(left as f32 + right as f32)
                        }
                        (Width::Single, BinaryOperator::Subtract) => {
                            f64::from(left as f32 - right as f32)
                        }
                        (Width::Single, BinaryOperator::Multiply) => {
                            f64::from(left as f32 * right as f32)
                        }
                        (Width::Single, BinaryOperator::Divide) => {
                            f64::from(left as f32 / right as f32)
                        }
                        (Width::Single, BinaryOperator::Modulo) => {
                            f64::from(left as f32 % right as f32)
                        }
                        (Width::Double, BinaryOperator::Add) => left + right,
                        (Width::Double, BinaryOperator::Subtract) => left - right,
                        (Width::Double, BinaryOperator::Multiply) => left * right,
                        (Width::Double, BinaryOperator::Divide) => left / right,
                        (Width::Double, BinaryOperator::Modulo) => left % right,
                        _ => return None,
                    };
                    return Some(floating(width, value));
                }
                // What the operator comes to as a number, and then as the
                // type holds it: past the type's range it wraps, which is
                // what `unchecked` asks for — anywhere else the binder has
                // reported CS0220, and the value is nobody's.
                let ty = self
                    .enum_underlying(&expression.ty)
                    .unwrap_or_else(|| expression.ty.clone());
                let exact = match integers(
                    *operator,
                    as_exact(&left)?,
                    as_exact(&right)?,
                    self.special_of(&ty),
                )? {
                    Integers::Value(exact) => exact,
                    // Not a constant, and CS0020 where it was written.
                    Integers::DivisionByZero => return None,
                };
                Some(integer_like(&ty, exact as i64, self))
            }
            _ => None,
        }
    }
}

/// The value of a comparison, `&&` or `||` of two constants, or `None` for
/// any other operator or operands it does not apply to. The operands have
/// been converted to one type already: two integers, two floating-point
/// numbers (where a NaN equals nothing), two strings, or `null`s.
fn compare(operator: BinaryOperator, left: &ConstantValue, right: &ConstantValue) -> Option<bool> {
    use std::cmp::Ordering;
    if let (ConstantValue::Boolean(left), ConstantValue::Boolean(right)) = (left, right) {
        match operator {
            BinaryOperator::LogicalAnd => return Some(*left && *right),
            BinaryOperator::LogicalOr => return Some(*left || *right),
            _ => {}
        }
    }
    if !matches!(
        operator,
        BinaryOperator::Equality
            | BinaryOperator::Inequality
            | BinaryOperator::LessThan
            | BinaryOperator::GreaterThan
            | BinaryOperator::LessThanOrEqual
            | BinaryOperator::GreaterThanOrEqual
    ) {
        return None;
    }
    let ordering = match (left, right) {
        (ConstantValue::String(left), ConstantValue::String(right)) => Some(left.cmp(right)),
        (ConstantValue::Null, ConstantValue::Null) => Some(Ordering::Equal),
        (ConstantValue::Null, ConstantValue::String(_))
        | (ConstantValue::String(_), ConstantValue::Null) => Some(Ordering::Less),
        (ConstantValue::Single(_) | ConstantValue::Double(_), _)
        | (_, ConstantValue::Single(_) | ConstantValue::Double(_)) => {
            as_float(left)?.partial_cmp(&as_float(right)?)
        }
        _ => Some(as_exact(left)?.cmp(&as_exact(right)?)),
    };
    let strings = matches!(left, ConstantValue::String(_) | ConstantValue::Null)
        || matches!(right, ConstantValue::String(_) | ConstantValue::Null);
    Some(match operator {
        BinaryOperator::Equality => ordering == Some(Ordering::Equal),
        BinaryOperator::Inequality => ordering != Some(Ordering::Equal),
        // Strings and nulls are only ever compared for equality.
        _ if strings => return None,
        BinaryOperator::LessThan => ordering? == Ordering::Less,
        BinaryOperator::GreaterThan => ordering? == Ordering::Greater,
        BinaryOperator::LessThanOrEqual => ordering? != Ordering::Greater,
        _ => ordering? != Ordering::Less,
    })
}

/// Which floating-point type a constant is folded in.
#[derive(Clone, Copy)]
enum Width {
    Single,
    Double,
}

impl Binder<'_> {
    fn floating_width(&self, ty: &crate::types::Type) -> Option<Width> {
        match self.special_of(ty)? {
            crate::corlib::SpecialType::Single => Some(Width::Single),
            crate::corlib::SpecialType::Double => Some(Width::Double),
            _ => None,
        }
    }
}

/// A number as a `double`, whatever constant it is.
fn as_float(value: &ConstantValue) -> Option<f64> {
    Some(match value {
        ConstantValue::Single(value) => f64::from(*value),
        ConstantValue::Double(value) => *value,
        ConstantValue::UInt64(value) => *value as f64,
        other => as_integer(other)? as f64,
    })
}

fn floating(width: Width, value: f64) -> ConstantValue {
    match width {
        Width::Single => ConstantValue::Single(value as f32),
        Width::Double => ConstantValue::Double(value),
    }
}

/// The integer inside a constant, where there is one.
fn as_integer(value: &ConstantValue) -> Option<i64> {
    Some(match value {
        ConstantValue::Int32(value) => i64::from(*value),
        ConstantValue::UInt32(value) => i64::from(*value),
        ConstantValue::Int64(value) => *value,
        ConstantValue::UInt64(value) => i64::try_from(*value).ok()?,
        ConstantValue::Char(value) => i64::from(u32::from(*value)),
        ConstantValue::Boolean(value) => i64::from(*value),
        _ => return None,
    })
}

/// The number an integer constant is, exactly: a `ulong` past
/// `long.MaxValue` is itself, where [`as_integer`] refuses it and
/// [`as_bits`] reads it as negative.
pub(crate) fn as_exact(value: &ConstantValue) -> Option<i128> {
    match value {
        ConstantValue::UInt64(value) => Some(i128::from(*value)),
        other => as_integer(other).map(i128::from),
    }
}

/// What an integer operator on two constants comes to.
pub(crate) enum Integers {
    /// The number, exactly: it may lie outside the type it is worked out
    /// in, which is an overflow (CS0220) unless `unchecked` wraps it.
    Value(i128),
    /// `/` or `%` by a constant zero (CS0020).
    DivisionByZero,
}

/// The range of an integral type an operator works in, or `None` for a
/// type no predefined integer operator gives.
pub(crate) fn integer_range(special: Option<SpecialType>) -> Option<(i128, i128)> {
    Some(match special? {
        SpecialType::Int32 => (i32::MIN.into(), i32::MAX.into()),
        SpecialType::UInt32 => (u32::MIN.into(), u32::MAX.into()),
        SpecialType::Int64 => (i64::MIN.into(), i64::MAX.into()),
        SpecialType::UInt64 => (u64::MIN.into(), u64::MAX.into()),
        _ => return None,
    })
}

/// An integer operator applied to two constants as the numbers they are,
/// in the type `special` (the operator's own: `int`, `uint`, `long` or
/// `ulong`; anything else counts as `int`). `None` for an operator that is
/// not integer arithmetic, or a product no 128 bits hold.
pub(crate) fn integers(
    operator: BinaryOperator,
    left: i128,
    right: i128,
    special: Option<SpecialType>,
) -> Option<Integers> {
    let wide = matches!(special, Some(SpecialType::Int64 | SpecialType::UInt64));
    let unsigned = matches!(special, Some(SpecialType::UInt32 | SpecialType::UInt64));
    // A shift counts modulo the width of what is shifted (§12.11): `1 <<
    // 33` on an `int` is `2`.
    let count = (right & if wide { 63 } else { 31 }) as u32;
    Some(Integers::Value(match operator {
        BinaryOperator::Add => left + right,
        BinaryOperator::Subtract => left - right,
        BinaryOperator::Multiply => left.checked_mul(right)?,
        BinaryOperator::Divide | BinaryOperator::Modulo if right == 0 => {
            return Some(Integers::DivisionByZero);
        }
        BinaryOperator::Divide => left / right,
        BinaryOperator::Modulo => left % right,
        BinaryOperator::BitwiseAnd => left & right,
        BinaryOperator::BitwiseOr => left | right,
        BinaryOperator::ExclusiveOr => left ^ right,
        BinaryOperator::LeftShift => left << count,
        // The sign comes along for a signed type; an unsigned one has
        // none, its number being its bits.
        BinaryOperator::RightShift => left >> count,
        // `>>>` shifts the bits of the type, sign bit and all.
        BinaryOperator::UnsignedRightShift => match (wide, unsigned) {
            (_, true) => left >> count,
            (true, false) => i128::from((left as i64 as u64) >> count),
            (false, false) => i128::from((left as i32 as u32) >> count),
        },
        _ => return None,
    }))
}

/// An integer constant's two's-complement bits, for a conversion that keeps
/// as many of them as its type has: unlike [`as_integer`], a `ulong` past
/// `long.MaxValue` is not refused, as `unchecked((byte)ulong.MaxValue)`
/// is 255.
fn as_bits(value: &ConstantValue) -> Option<i64> {
    match value {
        ConstantValue::UInt64(value) => Some(*value as i64),
        other => as_integer(other),
    }
}

/// Puts an integer back into the shape the expression's type calls for.
fn integer_like(ty: &crate::types::Type, value: i64, binder: &Binder<'_>) -> ConstantValue {
    use crate::corlib::SpecialType;
    let special = ty.symbol().and_then(|symbol| {
        SpecialType::ALL
            .iter()
            .copied()
            .find(|special| binder.compilation().special_type(*special) == Some(symbol))
    });
    match special {
        Some(SpecialType::Int64) => ConstantValue::Int64(value),
        Some(SpecialType::UInt64) => ConstantValue::UInt64(value as u64),
        Some(SpecialType::UInt32) => ConstantValue::UInt32(value as u32),
        Some(SpecialType::Boolean) => ConstantValue::Boolean(value != 0),
        // A `char` is the low 16 bits; a surrogate, which a Rust `char`
        // cannot hold, stays its number.
        Some(SpecialType::Char) => char::from_u32(u32::from(value as u16)).map_or(
            ConstantValue::Int32(i32::from(value as u16)),
            ConstantValue::Char,
        ),
        _ => ConstantValue::Int32(value as i32),
    }
}
