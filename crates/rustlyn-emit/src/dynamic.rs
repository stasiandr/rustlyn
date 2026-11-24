//! `dynamic`: operations the runtime binds, through call sites.
//!
//! An operation on a `dynamic` value is compiled to a call through a
//! `CallSite<TDelegate>` kept in a static field (§12.3.3 leaves the how to the
//! implementation; this is Roslyn's). The field starts out null; the first
//! time the operation runs, the site is made from a `CallSiteBinder` that the
//! C# runtime binder (`Microsoft.CSharp.RuntimeBinder.Binder`) builds from what
//! the source wrote — the member's name, the operator, how each argument was
//! passed — and from then on the call goes through the site's `Target`
//! delegate, which caches what the binder decided for the types it has seen.
//!
//! The fields live in a static class nested in the type whose member holds
//! the operation, one class per body, named `<>o__N` as Roslyn names its own.

use rustlyn_semantics::{
    BinaryOperator, BoundDynamic, BoundExpression, BoundExpressionKind, DynamicOperation,
    DynamicUnary, RefKind, Type,
};

use crate::codegen::BodyEmitter;
use crate::emitter::{
    EmitError, Emitter, FieldPlan, MethodPlan, MethodSource, ParameterPlan, TypePlan,
    delegate_constructor_signature,
};
use crate::il::{Instruction, Token};
use crate::metadata::{field_attributes, method_attributes, method_impl, table};
use crate::signature::{ElementType, SigType, field_signature, method_signature, type_def_or_ref};

/// `Microsoft.CSharp.RuntimeBinder.CSharpBinderFlags`.
mod binder_flags {
    pub(super) const CHECKED_CONTEXT: i32 = 1;
    pub(super) const INVOKE_SIMPLE_NAME: i32 = 2;
    pub(super) const INVOKE_SPECIAL_NAME: i32 = 4;
    pub(super) const BINARY_OPERATION_LOGICAL: i32 = 8;
    pub(super) const CONVERT_EXPLICIT: i32 = 16;
    pub(super) const VALUE_FROM_COMPOUND_ASSIGNMENT: i32 = 128;
    pub(super) const RESULT_DISCARDED: i32 = 256;
}

/// `Microsoft.CSharp.RuntimeBinder.CSharpArgumentInfoFlags`.
mod argument_flags {
    pub(super) const USE_COMPILE_TIME_TYPE: i32 = 1;
    pub(super) const CONSTANT: i32 = 2;
    pub(super) const NAMED_ARGUMENT: i32 = 4;
    pub(super) const IS_REF: i32 = 8;
    pub(super) const IS_OUT: i32 = 16;
    pub(super) const IS_STATIC_TYPE: i32 = 32;
}

const BINDER: &str = "Microsoft.CSharp.RuntimeBinder.Binder";
const ARGUMENT_INFO: &str = "Microsoft.CSharp.RuntimeBinder.CSharpArgumentInfo";
const CALL_SITE: &str = "System.Runtime.CompilerServices.CallSite";
const CALL_SITE_BINDER: &str = "System.Runtime.CompilerServices.CallSiteBinder";

/// A row the sites need that nothing in the source declares.
#[derive(Clone, Debug)]
pub(crate) enum SiteRow {
    /// The class a body keeps its sites in, nested in the body's type, and
    /// how many type parameters it declares: those of the type and of the
    /// method the body belongs to, which a site's delegate may mention.
    Container {
        enclosing: Token,
        name: String,
        arity: u32,
    },
    /// The delegate a site is called through when something is passed to it
    /// by reference, which no `Func` can say.
    Delegate(String),
}

/// The container being filled for the body being emitted.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct SiteContainer {
    /// Which of `Emitter::dynamic_containers` it is, once the body has made
    /// one.
    pub(crate) index: Option<usize>,
    /// How many of its type parameters stand for the type's (`!0`...) and
    /// how many for the method's (`!!0`...), in that order.
    pub(crate) type_arity: u32,
    pub(crate) method_arity: u32,
}

/// One value a site is called with.
pub(crate) enum Operand<'e> {
    /// An expression, evaluated where the call needs it.
    Value(&'e BoundExpression),
    /// A value already held in a slot, of this type.
    Held(u16, Type),
    /// `typeof(T)`: the receiver of a static member reached through its type.
    TypeOf(Type),
}

impl Operand<'_> {
    /// The type the site's delegate takes this operand as.
    fn static_type(&self) -> Option<Type> {
        match self {
            Self::Value(value) => match &value.kind {
                BoundExpressionKind::RefArgument { operand, .. } => Some(operand.ty.clone()),
                _ => Some(value.ty.clone()),
            },
            Self::Held(_, ty) => Some(ty.clone()),
            Self::TypeOf(_) => None,
        }
    }

    fn ref_kind(&self) -> RefKind {
        match self {
            Self::Value(value) => match &value.kind {
                BoundExpressionKind::RefArgument { kind, .. } => *kind,
                _ => RefKind::None,
            },
            _ => RefKind::None,
        }
    }

    /// What the runtime binder is told about the operand.
    fn flags(&self, name: Option<&str>) -> i32 {
        let mut flags = 0;
        if name.is_some() {
            flags |= argument_flags::NAMED_ARGUMENT;
        }
        match self.ref_kind() {
            RefKind::Out => flags |= argument_flags::IS_OUT | argument_flags::USE_COMPILE_TIME_TYPE,
            RefKind::Ref | RefKind::In => {
                flags |= argument_flags::IS_REF | argument_flags::USE_COMPILE_TIME_TYPE;
            }
            RefKind::None => {}
        }
        match self {
            Self::TypeOf(_) => {
                flags |= argument_flags::IS_STATIC_TYPE | argument_flags::USE_COMPILE_TIME_TYPE;
            }
            Self::Value(value) => {
                // A constant keeps its value for the binder, and its type
                // unless it is the `null` literal, which has none.
                if value.constant().is_some() {
                    flags |= argument_flags::CONSTANT;
                }
                if !matches!(value.ty, Type::Dynamic | Type::Null) {
                    flags |= argument_flags::USE_COMPILE_TIME_TYPE;
                }
            }
            Self::Held(_, ty) => {
                if !matches!(ty, Type::Dynamic | Type::Null) {
                    flags |= argument_flags::USE_COMPILE_TIME_TYPE;
                }
            }
        }
        flags
    }
}

/// A `dynamic` member or element with its receiver and arguments already
/// evaluated, each into a slot, for an operation that reads it and writes it.
struct HeldAccess {
    receiver: Operand<'static>,
    arguments: Vec<Operand<'static>>,
    names: Vec<Option<String>>,
}

/// What a compound assignment or an increment does to the value it reads.
pub(crate) enum Change<'e> {
    /// `x op= value`.
    Binary(BinaryOperator, &'e BoundExpression),
    /// `x++` or `--x`; the flag says whether the value is the one after.
    Increment(DynamicUnary, bool),
}

/// Which `Binder` factory makes the site's binder, and with what.
pub(crate) enum SiteBinder<'e> {
    InvokeMember {
        flags: i32,
        name: &'e str,
        type_arguments: &'e [Type],
    },
    GetMember {
        flags: i32,
        name: &'e str,
    },
    SetMember {
        flags: i32,
        name: &'e str,
    },
    GetIndex,
    SetIndex {
        flags: i32,
    },
    Invoke {
        flags: i32,
    },
    InvokeConstructor,
    BinaryOperation {
        flags: i32,
        expression_type: i32,
    },
    UnaryOperation {
        flags: i32,
        expression_type: i32,
    },
    Convert {
        flags: i32,
        target: &'e Type,
    },
    /// Whether the member of that name on the receiver is an event.
    IsEvent {
        name: &'e str,
    },
}

/// The `System.Linq.Expressions.ExpressionType` of a binary operator.
fn binary_expression_type(operator: BinaryOperator, compound: bool) -> Result<i32, EmitError> {
    use BinaryOperator as B;
    Ok(match (operator, compound) {
        (B::Add, false) => 0,
        (B::BitwiseAnd | B::LogicalAnd, false) => 2,
        (B::Divide, false) => 12,
        (B::Equality, false) => 13,
        (B::ExclusiveOr, false) => 14,
        (B::GreaterThan, false) => 15,
        (B::GreaterThanOrEqual, false) => 16,
        (B::LeftShift, false) => 19,
        (B::LessThan, false) => 20,
        (B::LessThanOrEqual, false) => 21,
        (B::Modulo, false) => 25,
        (B::Multiply, false) => 26,
        (B::Inequality, false) => 35,
        (B::BitwiseOr | B::LogicalOr, false) => 36,
        (B::RightShift, false) => 41,
        (B::Subtract, false) => 42,
        (B::Add, true) => 63,
        (B::BitwiseAnd, true) => 64,
        (B::Divide, true) => 65,
        (B::ExclusiveOr, true) => 66,
        (B::LeftShift, true) => 67,
        (B::Modulo, true) => 68,
        (B::Multiply, true) => 69,
        (B::BitwiseOr, true) => 70,
        (B::RightShift, true) => 72,
        (B::Subtract, true) => 73,
        (other, _) => {
            return Err(EmitError::new(format!(
                "the operator {other:?} on a `dynamic` operand cannot be emitted yet"
            )));
        }
    })
}

/// The `ExpressionType` of a unary operation.
const fn unary_expression_type(operator: DynamicUnary) -> i32 {
    match operator {
        DynamicUnary::Minus => 28,
        DynamicUnary::Plus => 29,
        DynamicUnary::LogicalNot => 34,
        DynamicUnary::Decrement => 49,
        DynamicUnary::Increment => 54,
        DynamicUnary::BitwiseNot => 82,
        DynamicUnary::IsTrue => 83,
        DynamicUnary::IsFalse => 84,
    }
}

impl Emitter<'_> {
    /// A `class` signature for a framework type.
    fn class_sig(&mut self, qualified: &str) -> SigType {
        SigType::Named {
            value_type: false,
            coded: self
                .references
                .type_ref_coded(&mut self.metadata, qualified),
        }
    }

    fn value_sig(&mut self, qualified: &str) -> SigType {
        SigType::Named {
            value_type: true,
            coded: self
                .references
                .type_ref_coded(&mut self.metadata, qualified),
        }
    }

    /// `IEnumerable<T>` over a framework class.
    fn enumerable_of(&mut self, element: &str) -> SigType {
        let element = self.class_sig(element);
        SigType::Constructed {
            value_type: false,
            coded: self.references.type_ref_coded(
                &mut self.metadata,
                "System.Collections.Generic.IEnumerable`1",
            ),
            arguments: vec![element],
        }
    }

    /// The type a site's delegate takes or gives back for a value of `ty`.
    fn site_sig(&mut self, ty: &Type) -> Result<SigType, EmitError> {
        match ty {
            Type::Dynamic | Type::Null | Type::Error => Ok(SigType::Primitive(ElementType::Object)),
            other => self.sig_type(other),
        }
    }

    /// The field a new site of the body being emitted is kept in, of type
    /// `CallSite<delegate>`.
    fn site_field(&mut self, delegate: &SigType, enclosing: Token) -> Result<Token, EmitError> {
        let index = match self.dynamic_current.index {
            Some(index) => index,
            None => {
                // The class takes every type parameter the body can name:
                // the ones its type declares — a display class's own, when it
                // is one's body — and the method's.
                let symbol = self
                    .dynamic_enclosing
                    .ok_or_else(|| EmitError::new("a dynamic operation outside any type"))?;
                let type_arity = if self.display_generics.is_empty() {
                    self.compilation
                        .symbols()
                        .get(symbol)
                        .as_named_type()
                        .map_or(0, |detail| detail.type_parameters.len())
                } else {
                    self.display_generics.len()
                } as u32;
                let method_arity = self.method_generics.len() as u32;
                self.dynamic_current.type_arity = type_arity;
                self.dynamic_current.method_arity = method_arity;
                let token = Token::new(table::TYPE_DEF, self.next_type);
                self.next_type += 1;
                let number = self
                    .dynamic_containers
                    .iter()
                    .filter(|(_, row)| {
                        matches!(row, SiteRow::Container { enclosing: at, .. } if *at == enclosing)
                    })
                    .count();
                self.dynamic_containers.push((
                    TypePlan {
                        symbol,
                        token,
                        fields: Vec::new(),
                        methods: Vec::new(),
                        properties: Vec::new(),
                        display: None,
                        iterator: None,
                        machine: None,
                        nested: None,
                    },
                    SiteRow::Container {
                        enclosing,
                        name: format!("<>o__{number}"),
                        arity: type_arity + method_arity,
                    },
                ));
                let index = self.dynamic_containers.len() - 1;
                self.dynamic_current.index = Some(index);
                index
            }
        };
        let token = Token::new(table::FIELD, self.next_field);
        self.next_field += 1;
        let call_site = self.references.type_ref_coded(
            &mut self.metadata,
            "System.Runtime.CompilerServices.CallSite`1",
        );
        let SiteContainer {
            type_arity,
            method_arity,
            ..
        } = self.dynamic_current;
        // Declared in the class's own terms: the method's `!!0` is the
        // class's parameter after the type's.
        let field_type = SigType::Constructed {
            value_type: false,
            coded: call_site,
            arguments: vec![in_container_terms(delegate, type_arity)],
        };
        let container = &mut self.dynamic_containers[index].0;
        let container_token = container.token;
        let name = format!("<>p__{}", container.fields.len());
        container.fields.push(FieldPlan {
            token,
            name: name.clone(),
            ty: Type::Error,
            flags: field_attributes::PUBLIC | field_attributes::STATIC,
            symbol: None,
            constant: None,
            sig: Some(field_type.clone()),
        });
        if type_arity + method_arity == 0 {
            return Ok(token);
        }
        // A generic class is reached through its construction over the
        // body's own parameters.
        let arguments = (0..type_arity)
            .map(SigType::TypeParameter)
            .chain((0..method_arity).map(SigType::MethodTypeParameter))
            .collect();
        let constructed = SigType::Constructed {
            value_type: false,
            coded: type_def_or_ref(0, container_token.0 & 0x00FF_FFFF),
            arguments,
        };
        let mut blob = Vec::new();
        constructed.write(&mut blob);
        let spec = self.references.type_spec(&mut self.metadata, &blob);
        Ok(self.references.member_of_spec(
            &mut self.metadata,
            spec,
            &name,
            &field_signature(&field_type),
        ))
    }
}

impl Emitter<'_> {
    /// The delegate a site with these parameters (the `CallSite` first) is
    /// called through, with its `Invoke` where it is one made here: a
    /// `Func` or an `Action` of them, or, where one is passed by reference,
    /// a delegate made for exactly that signature.
    fn site_delegate(
        &mut self,
        parameters: Vec<SigType>,
        returns: Option<SigType>,
    ) -> Result<(SigType, Option<Token>), EmitError> {
        let by_reference = parameters
            .iter()
            .any(|parameter| matches!(parameter, SigType::ByRef(_)));
        if !by_reference {
            let mut arguments = parameters;
            let name = match returns {
                Some(returns) => {
                    arguments.push(returns);
                    format!("System.Func`{}", arguments.len())
                }
                None => format!("System.Action`{}", arguments.len()),
            };
            if arguments.len() > 17 {
                return Err(EmitError::new(
                    "a dynamic operation with more operands than a `Func` takes cannot be emitted yet",
                ));
            }
            return Ok((
                SigType::Constructed {
                    value_type: false,
                    coded: self.references.type_ref_coded(&mut self.metadata, &name),
                    arguments,
                },
                None,
            ));
        }
        let returns_sig = returns
            .clone()
            .unwrap_or(SigType::Primitive(ElementType::Void));
        let invoke = method_signature(true, &returns_sig, &parameters);
        if let Some((found, token)) = self.site_delegates.get(&invoke) {
            return Ok((found.clone(), Some(*token)));
        }
        let token = Token::new(table::TYPE_DEF, self.next_type);
        self.next_type += 1;
        let constructor = Token::new(table::METHOD_DEF, self.next_method);
        let invoke_token = Token::new(table::METHOD_DEF, self.next_method + 1);
        self.next_method += 2;
        let name = format!(
            "<>{}{}",
            if returns.is_some() { "F" } else { "A" },
            self.site_delegates.len()
        );
        let runtime = method_attributes::PUBLIC | method_attributes::HIDE_BY_SIG;
        let named = |name: &str| ParameterPlan {
            by_ref: false,
            symbol: None,
            name: name.to_string(),
            ty: Type::Void,
        };
        let symbol = self
            .dynamic_enclosing
            .ok_or_else(|| EmitError::new("a dynamic operation outside any type"))?;
        let plan = TypePlan {
            symbol,
            token,
            fields: Vec::new(),
            methods: vec![
                MethodPlan {
                    source: MethodSource::DefaultConstructor,
                    token: constructor,
                    name: ".ctor".to_string(),
                    flags: runtime
                        | method_attributes::SPECIAL_NAME
                        | method_attributes::RT_SPECIAL_NAME,
                    instance: true,
                    return_type: Type::Void,
                    parameters: vec![named("object"), named("method")],
                    type_parameters: Vec::new(),
                    impl_flags: method_impl::RUNTIME,
                    signature: Some(delegate_constructor_signature()),
                },
                MethodPlan {
                    source: MethodSource::DefaultConstructor,
                    token: invoke_token,
                    name: "Invoke".to_string(),
                    flags: runtime | method_attributes::VIRTUAL | method_attributes::NEW_SLOT,
                    instance: true,
                    return_type: Type::Void,
                    parameters: (0..parameters.len())
                        .map(|index| named(&format!("arg{}", index + 1)))
                        .collect(),
                    type_parameters: Vec::new(),
                    impl_flags: method_impl::RUNTIME,
                    signature: Some(invoke.clone()),
                },
            ],
            properties: Vec::new(),
            display: None,
            iterator: None,
            machine: None,
            nested: None,
        };
        self.dynamic_containers
            .push((plan, SiteRow::Delegate(name)));
        let sig = SigType::Named {
            value_type: false,
            coded: type_def_or_ref(0, token.0 & 0x00FF_FFFF),
        };
        self.site_delegates
            .insert(invoke, (sig.clone(), invoke_token));
        Ok((sig, Some(invoke_token)))
    }
}

impl BodyEmitter<'_, '_> {
    /// Emits an operation on a `dynamic` value. `used` says whether its value
    /// is wanted; a call whose value is not says so to the binder, and its
    /// site gives back nothing.
    pub(crate) fn emit_dynamic(
        &mut self,
        dynamic: &BoundDynamic,
        ty: &Type,
        used: bool,
    ) -> Result<bool, EmitError> {
        let names: Vec<Option<&str>> = dynamic
            .names
            .iter()
            .map(|name| name.as_deref())
            .chain(std::iter::repeat(None))
            .take(dynamic.arguments.len())
            .collect();
        let arguments: Vec<Operand<'_>> = dynamic.arguments.iter().map(Operand::Value).collect();
        let receiver = dynamic
            .receiver
            .as_ref()
            .map(|receiver| match receiver.kind {
                BoundExpressionKind::TypeExpression(_) => Operand::TypeOf(receiver.ty.clone()),
                _ => Operand::Value(receiver),
            });
        let checked = if self.checked {
            binder_flags::CHECKED_CONTEXT
        } else {
            0
        };
        match &dynamic.operation {
            DynamicOperation::InvokeMember {
                name,
                type_arguments,
                simple_name,
            } => {
                let mut flags = 0;
                if *simple_name {
                    flags |= binder_flags::INVOKE_SIMPLE_NAME;
                }
                if !used {
                    flags |= binder_flags::RESULT_DISCARDED;
                }
                let result = if used { ty.clone() } else { Type::Void };
                self.emit_site(
                    &SiteBinder::InvokeMember {
                        flags,
                        name,
                        type_arguments,
                    },
                    receiver.as_ref(),
                    &arguments,
                    &names,
                    None,
                    &result,
                )?;
                Ok(used)
            }
            DynamicOperation::Invoke => {
                let mut flags = 0;
                if !used {
                    flags |= binder_flags::RESULT_DISCARDED;
                }
                let result = if used { ty.clone() } else { Type::Void };
                self.emit_site(
                    &SiteBinder::Invoke { flags },
                    receiver.as_ref(),
                    &arguments,
                    &names,
                    None,
                    &result,
                )?;
                Ok(used)
            }
            DynamicOperation::GetMember(name) => {
                self.emit_site(
                    &SiteBinder::GetMember { flags: 0, name },
                    receiver.as_ref(),
                    &[],
                    &[],
                    None,
                    ty,
                )?;
                Ok(true)
            }
            DynamicOperation::GetIndex => {
                self.emit_site(
                    &SiteBinder::GetIndex,
                    receiver.as_ref(),
                    &arguments,
                    &names,
                    None,
                    ty,
                )?;
                Ok(true)
            }
            DynamicOperation::InvokeConstructor => {
                let made = Operand::TypeOf(ty.clone());
                self.emit_site(
                    &SiteBinder::InvokeConstructor,
                    Some(&made),
                    &arguments,
                    &names,
                    None,
                    ty,
                )?;
                Ok(true)
            }
            DynamicOperation::Binary { operator, compound } => {
                let mut flags = checked;
                if matches!(
                    operator,
                    BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr
                ) {
                    flags |= binder_flags::BINARY_OPERATION_LOGICAL;
                }
                let expression_type = binary_expression_type(*operator, *compound)?;
                self.emit_site(
                    &SiteBinder::BinaryOperation {
                        flags,
                        expression_type,
                    },
                    None,
                    &[
                        receiver
                            .ok_or_else(|| EmitError::new("a binary operation with no left"))?,
                        arguments
                            .into_iter()
                            .next()
                            .ok_or_else(|| EmitError::new("a binary operation with no right"))?,
                    ],
                    &[None, None],
                    None,
                    ty,
                )?;
                Ok(true)
            }
            DynamicOperation::Unary(operator) => {
                self.emit_site(
                    &SiteBinder::UnaryOperation {
                        flags: checked,
                        expression_type: unary_expression_type(*operator),
                    },
                    None,
                    &[receiver.ok_or_else(|| EmitError::new("a unary operation with nothing"))?],
                    &[None],
                    None,
                    ty,
                )?;
                Ok(true)
            }
            DynamicOperation::Convert { explicit } => {
                let mut flags = checked;
                if *explicit {
                    flags |= binder_flags::CONVERT_EXPLICIT;
                }
                self.emit_site(
                    &SiteBinder::Convert { flags, target: ty },
                    None,
                    &[receiver.ok_or_else(|| EmitError::new("a conversion of nothing"))?],
                    &[None],
                    None,
                    ty,
                )?;
                Ok(true)
            }
        }
    }

    /// `operand.GetAwaiter()` for an `await` on a `dynamic` operand: the
    /// awaiter, an `object`, is left on the stack (Roslyn's
    /// `MakeCallMaybeDynamic`).
    pub(crate) fn emit_dynamic_get_awaiter(
        &mut self,
        operand: &BoundExpression,
    ) -> Result<(), EmitError> {
        self.emit_site(
            &SiteBinder::InvokeMember {
                flags: 0,
                name: "GetAwaiter",
                type_arguments: &[],
            },
            Some(&Operand::Value(operand)),
            &[],
            &[],
            None,
            &Type::Dynamic,
        )
    }

    /// `(bool)awaiter.IsCompleted` on a `dynamic` awaiter held in `awaiter`:
    /// a site reading the member, held in a temporary, and a site converting
    /// it explicitly, whatever the context's checking (Roslyn's
    /// `GenerateGetIsCompleted`).
    pub(crate) fn emit_dynamic_is_completed(&mut self, awaiter: u16) -> Result<(), EmitError> {
        let boolean = self
            .emitter
            .compilation
            .special_type(rustlyn_semantics::SpecialType::Boolean)
            .map(Type::named)
            .ok_or_else(|| EmitError::new("the compilation has no `System.Boolean`"))?;
        self.emit_site(
            &SiteBinder::GetMember {
                flags: 0,
                name: "IsCompleted",
            },
            Some(&Operand::Held(awaiter, Type::Dynamic)),
            &[],
            &[],
            None,
            &Type::Dynamic,
        )?;
        let member = self.temporary(&Type::Dynamic)?;
        self.stream.emit(Instruction::StoreLocal(member));
        self.emit_site(
            &SiteBinder::Convert {
                flags: binder_flags::CONVERT_EXPLICIT,
                target: &boolean,
            },
            None,
            &[Operand::Held(member, Type::Dynamic)],
            &[None],
            None,
            &boolean,
        )
    }

    /// `awaiter.GetResult()` on a `dynamic` awaiter held in `awaiter`, whose
    /// value is left on the stack where it is `used`, and is otherwise said
    /// to be discarded, as a call's is.
    pub(crate) fn emit_dynamic_get_result(
        &mut self,
        awaiter: u16,
        used: bool,
    ) -> Result<(), EmitError> {
        let (flags, result) = if used {
            (0, Type::Dynamic)
        } else {
            (binder_flags::RESULT_DISCARDED, Type::Void)
        };
        self.emit_site(
            &SiteBinder::InvokeMember {
                flags,
                name: "GetResult",
                type_arguments: &[],
            },
            Some(&Operand::Held(awaiter, Type::Dynamic)),
            &[],
            &[],
            None,
            &result,
        )
    }

    /// Assigns through a `dynamic` member or element: `d.X = value`,
    /// `d[i] = value`. The value of the assignment is what the site gives
    /// back.
    pub(crate) fn emit_dynamic_assignment(
        &mut self,
        target: &BoundDynamic,
        value: Operand<'_>,
        compound: bool,
        used: bool,
    ) -> Result<(), EmitError> {
        let mut flags = 0;
        if compound {
            flags |= binder_flags::VALUE_FROM_COMPOUND_ASSIGNMENT;
            if self.checked {
                flags |= binder_flags::CHECKED_CONTEXT;
            }
        }
        let names: Vec<Option<&str>> = target
            .names
            .iter()
            .map(|name| name.as_deref())
            .chain(std::iter::repeat(None))
            .take(target.arguments.len())
            .collect();
        let arguments: Vec<Operand<'_>> = target.arguments.iter().map(Operand::Value).collect();
        let receiver = target.receiver.as_ref().map(Operand::Value);
        let binder = match &target.operation {
            DynamicOperation::GetMember(name) => SiteBinder::SetMember { flags, name },
            DynamicOperation::GetIndex => SiteBinder::SetIndex { flags },
            _ => {
                return Err(EmitError::new(
                    "this `dynamic` expression cannot be assigned to",
                ));
            }
        };
        let arguments = match target.operation {
            DynamicOperation::GetMember(_) => Vec::new(),
            _ => arguments,
        };
        self.emit_site(
            &binder,
            receiver.as_ref(),
            &arguments,
            &names,
            Some(&value),
            &Type::Dynamic,
        )?;
        if !used {
            self.stream.emit(Instruction::Pop);
        }
        Ok(())
    }

    /// `x op= y`, `x++` and the rest where the runtime binds the operation:
    /// the target is read once, the site computes the new value, and it is
    /// stored back — through the runtime binder too, where the target is a
    /// member or an element of a `dynamic` value.
    pub(crate) fn emit_dynamic_compound(
        &mut self,
        target: &BoundExpression,
        change: Change<'_>,
        used: bool,
    ) -> Result<(), EmitError> {
        let after = match change {
            Change::Binary(..) => true,
            Change::Increment(_, prefix) => prefix,
        };
        if let BoundExpressionKind::Dynamic(access) = &target.kind
            && let DynamicOperation::GetMember(name) = &access.operation
            && let Change::Binary(
                operator @ (BinaryOperator::Add | BinaryOperator::Subtract),
                value,
            ) = change
        {
            return self.emit_dynamic_event_or_member(access, name, operator, value, used);
        }
        if let BoundExpressionKind::Dynamic(access) = &target.kind {
            let HeldAccess {
                receiver,
                arguments,
                names,
            } = self.hold_access(access)?;
            let names: Vec<Option<&str>> = names.iter().map(|name| name.as_deref()).collect();
            let (get, set) = match &access.operation {
                DynamicOperation::GetMember(name) => (
                    SiteBinder::GetMember { flags: 0, name },
                    SiteBinder::SetMember {
                        flags: self.compound_flags(),
                        name,
                    },
                ),
                DynamicOperation::GetIndex => (
                    SiteBinder::GetIndex,
                    SiteBinder::SetIndex {
                        flags: self.compound_flags(),
                    },
                ),
                _ => {
                    return Err(EmitError::new(
                        "this `dynamic` expression cannot be assigned to",
                    ));
                }
            };
            self.emit_site(
                &get,
                Some(&receiver),
                &arguments,
                &names,
                None,
                &Type::Dynamic,
            )?;
            let current = self.temporary(&Type::Dynamic)?;
            self.stream.emit(Instruction::StoreLocal(current));
            self.emit_change(&change, Operand::Held(current, Type::Dynamic))?;
            let changed = self.temporary(&Type::Dynamic)?;
            self.stream.emit(Instruction::StoreLocal(changed));
            self.emit_site(
                &set,
                Some(&receiver),
                &arguments,
                &names,
                Some(&Operand::Held(changed, Type::Dynamic)),
                &Type::Dynamic,
            )?;
            self.stream.emit(Instruction::Pop);
            if used {
                self.stream.emit(Instruction::LoadLocal(if after {
                    changed
                } else {
                    current
                }));
            }
            return Ok(());
        }

        // A variable, a field or an element: read, operate, convert back to
        // what it holds, store.
        let stored = target.ty.clone();
        let place = self.place(target)?;
        self.emit_place_load(&place)?;
        let current = self.temporary(&stored)?;
        self.stream.emit(Instruction::StoreLocal(current));
        self.emit_change(&change, Operand::Held(current, stored.clone()))?;
        if !matches!(stored, Type::Dynamic) && !self.is_object(&stored) {
            let changed = self.temporary(&Type::Dynamic)?;
            self.stream.emit(Instruction::StoreLocal(changed));
            self.emit_site(
                &SiteBinder::Convert {
                    flags: 0,
                    target: &stored,
                },
                None,
                &[Operand::Held(changed, Type::Dynamic)],
                &[None],
                None,
                &stored,
            )?;
        }
        let result = self.temporary(&stored)?;
        self.stream.emit(Instruction::Dup);
        self.stream.emit(Instruction::StoreLocal(result));
        self.store_into(&place, &stored)?;
        if used {
            self.stream
                .emit(Instruction::LoadLocal(if after { result } else { current }));
        }
        Ok(())
    }

    /// `d.E += h` and `d.E -= h`, which subscribe where `E` turns out to be
    /// an event and add to the member otherwise, as Roslyn lowers them: the
    /// receiver, then whether the member is an event, then the member read
    /// only where it is not, then the value — each once.
    fn emit_dynamic_event_or_member(
        &mut self,
        access: &BoundDynamic,
        name: &str,
        operator: BinaryOperator,
        value: &BoundExpression,
        used: bool,
    ) -> Result<(), EmitError> {
        let HeldAccess { receiver, .. } = self.hold_access(access)?;
        let boolean = self
            .emitter
            .compilation
            .type_by_metadata_name("System.Boolean")
            .map(Type::named)
            .ok_or_else(|| EmitError::new("no System.Boolean to ask an event about"))?;
        self.emit_site(
            &SiteBinder::IsEvent { name },
            Some(&receiver),
            &[],
            &[],
            None,
            &boolean,
        )?;
        let is_event = self.temporary(&boolean)?;
        self.stream.emit(Instruction::StoreLocal(is_event));
        let current = self.temporary(&Type::Dynamic)?;
        let read = self.stream.label();
        self.stream.emit(Instruction::LoadLocal(is_event));
        self.stream.emit(Instruction::BranchIfTrue(read));
        self.emit_site(
            &SiteBinder::GetMember { flags: 0, name },
            Some(&receiver),
            &[],
            &[],
            None,
            &Type::Dynamic,
        )?;
        self.stream.emit(Instruction::StoreLocal(current));
        self.stream.mark(read);
        let given = value.ty.clone();
        let held = self.temporary(&given)?;
        self.emit_expression(value, true)?;
        self.stream.emit(Instruction::StoreLocal(held));
        let (not_event, end) = (self.stream.label(), self.stream.label());
        self.stream.emit(Instruction::LoadLocal(is_event));
        self.stream.emit(Instruction::BranchIfFalse(not_event));
        let accessor = if operator == BinaryOperator::Add {
            format!("add_{name}")
        } else {
            format!("remove_{name}")
        };
        self.emit_site(
            &SiteBinder::InvokeMember {
                flags: binder_flags::INVOKE_SPECIAL_NAME | binder_flags::RESULT_DISCARDED,
                name: &accessor,
                type_arguments: &[],
            },
            Some(&receiver),
            &[Operand::Held(held, given.clone())],
            &[None],
            None,
            &Type::Void,
        )?;
        if used {
            self.stream.emit(Instruction::LoadNull);
        }
        self.stream.emit(Instruction::Branch(end));
        self.stream.mark(not_event);
        let checked = if self.checked {
            binder_flags::CHECKED_CONTEXT
        } else {
            0
        };
        self.emit_site(
            &SiteBinder::BinaryOperation {
                flags: checked,
                expression_type: binary_expression_type(operator, true)?,
            },
            None,
            &[
                Operand::Held(current, Type::Dynamic),
                Operand::Held(held, given),
            ],
            &[None, None],
            None,
            &Type::Dynamic,
        )?;
        let changed = self.temporary(&Type::Dynamic)?;
        self.stream.emit(Instruction::StoreLocal(changed));
        self.emit_site(
            &SiteBinder::SetMember {
                flags: self.compound_flags(),
                name,
            },
            Some(&receiver),
            &[],
            &[],
            Some(&Operand::Held(changed, Type::Dynamic)),
            &Type::Dynamic,
        )?;
        self.stream.emit(Instruction::Pop);
        if used {
            self.stream.emit(Instruction::LoadLocal(changed));
        }
        self.stream.mark(end);
        Ok(())
    }

    /// `d.X ??= y` and `d[i] ??= y`: the member is read once, and written
    /// only where it was null.
    pub(crate) fn emit_dynamic_coalesce_assignment(
        &mut self,
        access: &BoundDynamic,
        value: &BoundExpression,
        used: bool,
    ) -> Result<(), EmitError> {
        let HeldAccess {
            receiver,
            arguments,
            names,
        } = self.hold_access(access)?;
        let names: Vec<Option<&str>> = names.iter().map(|name| name.as_deref()).collect();
        let (get, set) = match &access.operation {
            DynamicOperation::GetMember(name) => (
                SiteBinder::GetMember { flags: 0, name },
                SiteBinder::SetMember { flags: 0, name },
            ),
            DynamicOperation::GetIndex => (SiteBinder::GetIndex, SiteBinder::SetIndex { flags: 0 }),
            _ => {
                return Err(EmitError::new(
                    "this `dynamic` expression cannot be assigned to",
                ));
            }
        };
        let get_arguments: &[Operand<'_>] = if matches!(get, SiteBinder::GetMember { .. }) {
            &[]
        } else {
            &arguments
        };
        self.emit_site(
            &get,
            Some(&receiver),
            get_arguments,
            &names,
            None,
            &Type::Dynamic,
        )?;
        let result = self.temporary(&Type::Dynamic)?;
        self.stream.emit(Instruction::StoreLocal(result));
        let done = self.stream.label();
        self.stream.emit(Instruction::LoadLocal(result));
        self.stream.emit(Instruction::BranchIfTrue(done));
        self.emit_site(
            &set,
            Some(&receiver),
            get_arguments,
            &names,
            Some(&Operand::Value(value)),
            &Type::Dynamic,
        )?;
        self.stream.emit(Instruction::StoreLocal(result));
        self.stream.mark(done);
        if used {
            self.stream.emit(Instruction::LoadLocal(result));
        }
        Ok(())
    }

    /// The receiver and arguments of a `dynamic` member or element, each
    /// evaluated once into a slot.
    fn hold_access(&mut self, access: &BoundDynamic) -> Result<HeldAccess, EmitError> {
        let receiver = access
            .receiver
            .as_ref()
            .ok_or_else(|| EmitError::new("a dynamic member with nothing to be one of"))?;
        let receiver_slot = self.temporary(&receiver.ty)?;
        self.emit_expression(receiver, true)?;
        self.stream.emit(Instruction::StoreLocal(receiver_slot));
        let mut arguments = Vec::with_capacity(access.arguments.len());
        for argument in &access.arguments {
            let slot = self.temporary(&argument.ty)?;
            self.emit_expression(argument, true)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            arguments.push(Operand::Held(slot, argument.ty.clone()));
        }
        let names = access
            .names
            .iter()
            .cloned()
            .chain(std::iter::repeat(None))
            .take(arguments.len())
            .collect();
        Ok(HeldAccess {
            receiver: Operand::Held(receiver_slot, receiver.ty.clone()),
            arguments,
            names,
        })
    }

    fn compound_flags(&self) -> i32 {
        binder_flags::VALUE_FROM_COMPOUND_ASSIGNMENT
            | if self.checked {
                binder_flags::CHECKED_CONTEXT
            } else {
                0
            }
    }

    fn is_object(&self, ty: &Type) -> bool {
        self.emitter
            .compilation
            .type_by_metadata_name("System.Object")
            .is_some_and(|object| *ty == Type::named(object))
    }

    /// The new value a compound assignment or an increment computes from
    /// the one it read.
    fn emit_change(&mut self, change: &Change<'_>, current: Operand<'_>) -> Result<(), EmitError> {
        let checked = if self.checked {
            binder_flags::CHECKED_CONTEXT
        } else {
            0
        };
        match change {
            Change::Binary(operator, value) => {
                let expression_type = binary_expression_type(*operator, true)?;
                self.emit_site(
                    &SiteBinder::BinaryOperation {
                        flags: checked,
                        expression_type,
                    },
                    None,
                    &[current, Operand::Value(value)],
                    &[None, None],
                    None,
                    &Type::Dynamic,
                )
            }
            Change::Increment(operator, _) => self.emit_site(
                &SiteBinder::UnaryOperation {
                    flags: checked,
                    expression_type: unary_expression_type(*operator),
                },
                None,
                &[current],
                &[None],
                None,
                &Type::Dynamic,
            ),
        }
    }

    /// One call through a site: made on first use, then called through its
    /// `Target`.
    pub(crate) fn emit_site(
        &mut self,
        binder: &SiteBinder<'_>,
        receiver: Option<&Operand<'_>>,
        arguments: &[Operand<'_>],
        names: &[Option<&str>],
        right: Option<&Operand<'_>>,
        result: &Type,
    ) -> Result<(), EmitError> {
        let operands: Vec<&Operand<'_>> = receiver
            .into_iter()
            .chain(arguments.iter())
            .chain(right)
            .collect();

        // The delegate: `Func<CallSite, operands..., result>`, or an
        // `Action` where nothing comes back. A value type with a home is
        // passed as the variable it is, so a call that changes it changes it
        // (Roslyn's `GetReceiverRefKind`).
        let receiver_by_reference = receiver.is_some_and(|receiver| match receiver {
            Operand::Value(value) => self.has_home(value),
            _ => false,
        });
        let call_site = self.emitter.class_sig(CALL_SITE);
        let mut parameters = vec![call_site];
        for (index, operand) in operands.iter().enumerate() {
            let ty = match operand.static_type() {
                Some(ty) => self.emitter.site_sig(&ty)?,
                None => self.emitter.class_sig("System.Type"),
            };
            let by_reference = operand.ref_kind() != RefKind::None
                || (index == 0 && receiver.is_some() && receiver_by_reference);
            parameters.push(if by_reference {
                SigType::ByRef(Box::new(ty))
            } else {
                ty
            });
        }
        let returns_void = matches!(result, Type::Void);
        let returns = if returns_void {
            None
        } else {
            Some(self.emitter.site_sig(result)?)
        };
        if parameters
            .iter()
            .any(|parameter| matches!(parameter, SigType::ByRef(_)))
            && parameters
                .iter()
                .chain(returns.iter())
                .any(mentions_type_parameter)
        {
            return Err(EmitError::new(
                "a dynamic operation passing a value of a type parameter by reference cannot be emitted yet",
            ));
        }
        let (delegate, made_invoke) = self.emitter.site_delegate(parameters.clone(), returns)?;

        let enclosing = self
            .emitter
            .dynamic_enclosing
            .and_then(|symbol| self.emitter.types.get(&symbol).copied())
            .ok_or_else(|| EmitError::new("a dynamic operation outside any type"))?;
        let field = self.emitter.site_field(&delegate, enclosing)?;

        // `CallSite<D>`, and its `Create` and `Target`.
        let call_site_generic = self.emitter.references.type_ref_coded(
            &mut self.emitter.metadata,
            "System.Runtime.CompilerServices.CallSite`1",
        );
        let site_type = SigType::Constructed {
            value_type: false,
            coded: call_site_generic,
            arguments: vec![delegate.clone()],
        };
        let mut blob = Vec::new();
        site_type.write(&mut blob);
        let site_spec = self
            .emitter
            .references
            .type_spec(&mut self.emitter.metadata, &blob);
        let site_binder = self.emitter.class_sig(CALL_SITE_BINDER);
        let create_sig = method_signature(
            false,
            &SigType::Constructed {
                value_type: false,
                coded: call_site_generic,
                arguments: vec![SigType::TypeParameter(0)],
            },
            &[site_binder],
        );
        let create = self.emitter.references.member_of_spec(
            &mut self.emitter.metadata,
            site_spec,
            "Create",
            &create_sig,
        );
        let target = self.emitter.references.member_of_spec(
            &mut self.emitter.metadata,
            site_spec,
            "Target",
            &field_signature(&SigType::TypeParameter(0)),
        );
        let count = parameters.len();
        let invoke = match made_invoke {
            Some(invoke) => invoke,
            None => {
                let mut blob = Vec::new();
                delegate.write(&mut blob);
                let delegate_spec = self
                    .emitter
                    .references
                    .type_spec(&mut self.emitter.metadata, &blob);
                let invoke_parameters: Vec<SigType> = (0..count)
                    .map(|index| SigType::TypeParameter(index as u32))
                    .collect();
                let invoke_returns = if returns_void {
                    SigType::Primitive(ElementType::Void)
                } else {
                    SigType::TypeParameter(count as u32)
                };
                self.emitter.references.member_of_spec(
                    &mut self.emitter.metadata,
                    delegate_spec,
                    "Invoke",
                    &method_signature(true, &invoke_returns, &invoke_parameters),
                )
            }
        };

        // `if (site == null) site = CallSite<D>.Create(binder);`
        let made = self.stream.label();
        self.stream.emit(Instruction::LoadStaticField(field));
        self.stream.emit(Instruction::BranchIfTrue(made));
        let names_for_infos: Vec<Option<&str>> = receiver
            .map(|_| None)
            .into_iter()
            .chain(names.iter().copied())
            .chain(right.map(|_| None))
            .collect();
        // A receiver passed as the variable it is says so, as a `ref`
        // argument does.
        let infos: Vec<(i32, Option<&str>)> = operands
            .iter()
            .zip(&names_for_infos)
            .enumerate()
            .map(|(index, (operand, name))| {
                let mut flags = operand.flags(*name);
                if index == 0 && receiver.is_some() && receiver_by_reference {
                    flags |= argument_flags::IS_REF | argument_flags::USE_COMPILE_TIME_TYPE;
                }
                (flags, *name)
            })
            .collect();
        self.emit_binder(binder, &infos)?;
        self.stream.call_effect(Instruction::Call(create), 1, 1);
        self.stream.emit(Instruction::StoreStaticField(field));
        self.stream.mark(made);

        // `site.Target(site, operands...)`
        self.stream.emit(Instruction::LoadStaticField(field));
        self.stream.emit(Instruction::LoadField(target));
        self.stream.emit(Instruction::LoadStaticField(field));
        for (index, operand) in operands.iter().enumerate() {
            match operand {
                Operand::Value(value)
                    if index == 0 && receiver.is_some() && receiver_by_reference =>
                {
                    self.emit_reference(value)?;
                }
                Operand::Value(value) => {
                    self.emit_expression(value, true)?;
                }
                Operand::Held(slot, _) => self.stream.emit(Instruction::LoadLocal(*slot)),
                Operand::TypeOf(ty) => self.emit_type_of(ty)?,
            }
        }
        self.stream.call_effect(
            Instruction::CallVirtual(invoke),
            count + 1,
            usize::from(!returns_void),
        );
        Ok(())
    }

    /// `typeof(T)`: `ldtoken` and `Type.GetTypeFromHandle`.
    pub(crate) fn emit_type_of(&mut self, ty: &Type) -> Result<(), EmitError> {
        let token = self.emitter.type_token(ty)?;
        let handle = self.emitter.value_sig("System.RuntimeTypeHandle");
        let returns = self.emitter.class_sig("System.Type");
        let member = self.emitter.framework_member(
            "System.Type",
            "GetTypeFromHandle",
            false,
            &returns,
            &[handle],
        );
        self.stream.emit(Instruction::LoadToken(token));
        self.stream.call_effect(Instruction::Call(member), 1, 1);
        Ok(())
    }

    /// The binder for a site: `Binder.X(flags, ..., context, argumentInfos)`.
    fn emit_binder(
        &mut self,
        binder: &SiteBinder<'_>,
        infos: &[(i32, Option<&str>)],
    ) -> Result<(), EmitError> {
        let binder_flags = self
            .emitter
            .value_sig("Microsoft.CSharp.RuntimeBinder.CSharpBinderFlags");
        let expression_type = self
            .emitter
            .value_sig("System.Linq.Expressions.ExpressionType");
        let string = SigType::Primitive(ElementType::String);
        let type_sig = self.emitter.class_sig("System.Type");
        let types = self.emitter.enumerable_of("System.Type");
        let info_list = self.emitter.enumerable_of(ARGUMENT_INFO);
        let returns = self.emitter.class_sig(CALL_SITE_BINDER);
        let context = self.context_type();

        let (name, parameters): (&str, Vec<SigType>) = match binder {
            SiteBinder::InvokeMember {
                flags,
                name,
                type_arguments,
            } => {
                self.stream.emit(Instruction::LoadInt32(*flags));
                let text = self.emitter.metadata.user_string(name);
                self.stream.emit(Instruction::LoadString(text));
                if type_arguments.is_empty() {
                    self.stream.emit(Instruction::LoadNull);
                } else {
                    let type_token = self.emitter.type_token(&self.system_type()?)?;
                    self.stream
                        .emit(Instruction::LoadInt32(type_arguments.len() as i32));
                    self.stream.emit(Instruction::NewArray(type_token));
                    for (index, argument) in type_arguments.iter().enumerate() {
                        self.stream.emit(Instruction::Dup);
                        self.stream.emit(Instruction::LoadInt32(index as i32));
                        self.emit_type_of(argument)?;
                        self.stream.emit(Instruction::StoreElementRef);
                    }
                }
                self.emit_type_of(&context)?;
                self.emit_argument_infos(infos)?;
                (
                    "InvokeMember",
                    vec![binder_flags, string, types, type_sig, info_list],
                )
            }
            SiteBinder::GetMember { flags, name } | SiteBinder::SetMember { flags, name } => {
                self.stream.emit(Instruction::LoadInt32(*flags));
                let text = self.emitter.metadata.user_string(name);
                self.stream.emit(Instruction::LoadString(text));
                self.emit_type_of(&context)?;
                self.emit_argument_infos(infos)?;
                (
                    if matches!(binder, SiteBinder::GetMember { .. }) {
                        "GetMember"
                    } else {
                        "SetMember"
                    },
                    vec![binder_flags, string, type_sig, info_list],
                )
            }
            SiteBinder::GetIndex
            | SiteBinder::SetIndex { .. }
            | SiteBinder::Invoke { .. }
            | SiteBinder::InvokeConstructor => {
                let (flags, name) = match binder {
                    SiteBinder::GetIndex => (0, "GetIndex"),
                    SiteBinder::SetIndex { flags } => (*flags, "SetIndex"),
                    SiteBinder::Invoke { flags } => (*flags, "Invoke"),
                    _ => (0, "InvokeConstructor"),
                };
                self.stream.emit(Instruction::LoadInt32(flags));
                self.emit_type_of(&context)?;
                self.emit_argument_infos(infos)?;
                (name, vec![binder_flags, type_sig, info_list])
            }
            SiteBinder::BinaryOperation {
                flags,
                expression_type: operation,
            }
            | SiteBinder::UnaryOperation {
                flags,
                expression_type: operation,
            } => {
                self.stream.emit(Instruction::LoadInt32(*flags));
                self.stream.emit(Instruction::LoadInt32(*operation));
                self.emit_type_of(&context)?;
                self.emit_argument_infos(infos)?;
                (
                    if matches!(binder, SiteBinder::BinaryOperation { .. }) {
                        "BinaryOperation"
                    } else {
                        "UnaryOperation"
                    },
                    vec![binder_flags, expression_type, type_sig, info_list],
                )
            }
            SiteBinder::Convert { flags, target } => {
                self.stream.emit(Instruction::LoadInt32(*flags));
                self.emit_type_of(target)?;
                self.emit_type_of(&context)?;
                ("Convert", vec![binder_flags, type_sig.clone(), type_sig])
            }
            SiteBinder::IsEvent { name } => {
                self.stream.emit(Instruction::LoadInt32(0));
                let text = self.emitter.metadata.user_string(name);
                self.stream.emit(Instruction::LoadString(text));
                self.emit_type_of(&context)?;
                ("IsEvent", vec![binder_flags, string, type_sig])
            }
        };
        let pops = parameters.len();
        let member = self
            .emitter
            .framework_member(BINDER, name, false, &returns, &parameters);
        self.stream.call_effect(Instruction::Call(member), pops, 1);
        Ok(())
    }

    /// `new CSharpArgumentInfo[] { CSharpArgumentInfo.Create(flags, name), ... }`.
    fn emit_argument_infos(&mut self, infos: &[(i32, Option<&str>)]) -> Result<(), EmitError> {
        let info = self.emitter.class_sig(ARGUMENT_INFO);
        let info_type = self
            .emitter
            .references
            .type_ref(&mut self.emitter.metadata, ARGUMENT_INFO);
        let flags_sig = self
            .emitter
            .value_sig("Microsoft.CSharp.RuntimeBinder.CSharpArgumentInfoFlags");
        let create = self.emitter.framework_member(
            ARGUMENT_INFO,
            "Create",
            false,
            &info,
            &[flags_sig, SigType::Primitive(ElementType::String)],
        );
        self.stream.emit(Instruction::LoadInt32(infos.len() as i32));
        self.stream.emit(Instruction::NewArray(info_type));
        for (index, (flags, name)) in infos.iter().enumerate() {
            let name = *name;
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadInt32(index as i32));
            self.stream.emit(Instruction::LoadInt32(*flags));
            match name {
                Some(name) => {
                    let text = self.emitter.metadata.user_string(name);
                    self.stream.emit(Instruction::LoadString(text));
                }
                None => self.stream.emit(Instruction::LoadNull),
            }
            self.stream.call_effect(Instruction::Call(create), 2, 1);
            self.stream.emit(Instruction::StoreElementRef);
        }
        Ok(())
    }

    /// The type the runtime binder checks accessibility from: the one whose
    /// member holds the operation.
    fn context_type(&self) -> Type {
        self.emitter
            .dynamic_enclosing
            .map_or(Type::Error, |enclosing| {
                self.emitter.binder.self_type(enclosing)
            })
    }
}

impl BodyEmitter<'_, '_> {
    /// Whether a receiver of a value type is a variable a call can change,
    /// rather than a value that would be copied anyway.
    fn has_home(&self, value: &BoundExpression) -> bool {
        if !self.emitter.is_value_type(&value.ty) || matches!(value.ty, Type::TypeParameter(_)) {
            return false;
        }
        match &value.kind {
            BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::ArrayAccess { .. } => true,
            BoundExpressionKind::Field { field, .. } => !self
                .emitter
                .compilation
                .symbols()
                .get(*field)
                .modifiers
                .contains(rustlyn_semantics::Modifiers::READONLY),
            // `GetS(ref s).M(d)`: what a `ref` return hands back is where the
            // value lives, writable unless it is a `ref readonly` one.
            BoundExpressionKind::Call { method: member, .. }
            | BoundExpressionKind::Property {
                property: member, ..
            }
            | BoundExpressionKind::IndexerAccess {
                indexer: member, ..
            } => {
                let symbol = self.emitter.compilation.symbols().get(*member);
                let readonly = symbol
                    .as_method()
                    .map(|detail| detail.returns_readonly)
                    .or_else(|| symbol.as_property().map(|detail| detail.returns_readonly))
                    .unwrap_or(false);
                matches!(self.emitter.type_of(*member), Type::ByRef(_)) && !readonly
            }
            _ => false,
        }
    }
}

/// A signature written in a body, as the class of its sites declares it: the
/// method's `!!j` is the class's `!(type_arity + j)`.
fn in_container_terms(sig: &SigType, type_arity: u32) -> SigType {
    let inner = |sig: &SigType| Box::new(in_container_terms(sig, type_arity));
    match sig {
        SigType::MethodTypeParameter(index) => SigType::TypeParameter(type_arity + index),
        SigType::Array(element) => SigType::Array(inner(element)),
        SigType::MultiArray(element, rank) => SigType::MultiArray(inner(element), *rank),
        SigType::ByRef(element) => SigType::ByRef(inner(element)),
        SigType::Pointer(element) => SigType::Pointer(inner(element)),
        SigType::Pinned(element) => SigType::Pinned(inner(element)),
        SigType::Required {
            modifier,
            inner: element,
        } => SigType::Required {
            modifier: *modifier,
            inner: inner(element),
        },
        SigType::Optional {
            modifier,
            inner: element,
        } => SigType::Optional {
            modifier: *modifier,
            inner: inner(element),
        },
        SigType::FunctionPointer {
            convention,
            returns,
            parameters,
        } => SigType::FunctionPointer {
            convention: *convention,
            returns: inner(returns),
            parameters: parameters
                .iter()
                .map(|parameter| in_container_terms(parameter, type_arity))
                .collect(),
        },
        SigType::Constructed {
            value_type,
            coded,
            arguments,
        } => SigType::Constructed {
            value_type: *value_type,
            coded: *coded,
            arguments: arguments
                .iter()
                .map(|argument| in_container_terms(argument, type_arity))
                .collect(),
        },
        other => other.clone(),
    }
}

/// Whether `dynamic` appears anywhere in a type.
pub(crate) fn mentions_dynamic_type(ty: &Type) -> bool {
    match ty {
        Type::Dynamic => true,
        Type::Named { type_arguments, .. } => type_arguments.iter().any(mentions_dynamic_type),
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            mentions_dynamic_type(element)
        }
        Type::Tuple(elements) => elements
            .iter()
            .any(|element| mentions_dynamic_type(&element.ty)),
        _ => false,
    }
}

/// The flags of `[Dynamic]` for a type: one per type and type argument, in
/// pre-order, true where it is `dynamic`.
pub(crate) fn dynamic_flags(ty: &Type, flags: &mut Vec<bool>) {
    flags.push(matches!(ty, Type::Dynamic));
    match ty {
        Type::Named { type_arguments, .. } => {
            for argument in type_arguments {
                dynamic_flags(argument, flags);
            }
        }
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            dynamic_flags(element, flags);
        }
        Type::Tuple(elements) => {
            for element in elements {
                dynamic_flags(&element.ty, flags);
            }
        }
        _ => {}
    }
}

/// Whether a signature names a type parameter anywhere in it.
fn mentions_type_parameter(sig: &SigType) -> bool {
    match sig {
        SigType::TypeParameter(_) | SigType::MethodTypeParameter(_) => true,
        SigType::Array(inner)
        | SigType::MultiArray(inner, _)
        | SigType::ByRef(inner)
        | SigType::Pointer(inner)
        | SigType::Pinned(inner) => mentions_type_parameter(inner),
        SigType::Required { inner, .. } | SigType::Optional { inner, .. } => {
            mentions_type_parameter(inner)
        }
        SigType::FunctionPointer {
            returns,
            parameters,
            ..
        } => mentions_type_parameter(returns) || parameters.iter().any(mentions_type_parameter),
        SigType::Constructed { arguments, .. } => arguments.iter().any(mentions_type_parameter),
        SigType::Primitive(_) | SigType::Named { .. } => false,
    }
}
