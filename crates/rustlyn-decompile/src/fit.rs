//! Casts C# asks for where IL does not.
//!
//! On the evaluation stack an `int` and a `uint`, or an enum and its
//! number, are the same thing, so IL converts between them without a word;
//! C# converts only where no information can be lost. A value stored,
//! returned or passed where C# would not convert it by itself gets the cast
//! written out, and an operator whose operands differ in sign gets the
//! signed one cast, so that C# does not widen the operation to 64 bits.

use rustlyn_metadata::signature::TypeSig;

use crate::ir::{BinOp, Expr, Stmt};
use crate::simplify::{Typer, implicit_numeric};
use crate::stack::{coerce_expr, substitute};

/// Casts the numbers and enums calls are given, before the calls are
/// folded into what no longer says what they take (`Add` into a collection
/// initializer); everything else waits for `fit_types`, so as not to hide
/// the shapes the simplifier looks for.
pub fn fit_arguments(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) {
    for stmt in stmts.iter_mut() {
        stmt.map_exprs(&mut |expr| {
            if let Expr::Call { method, args, .. } = expr {
                for (at, arg) in args.iter_mut().enumerate() {
                    if let Some(param) = method.sig.parameters.get(at) {
                        let param = substitute(param, &method.declaring, &method.type_args);
                        // A constant for a `bool` is one too: `d[k] = 1`,
                        // an indexer's setter, is `d[k] = true`; and so is
                        // `c ? 1 : 0` given for a `T` that is `bool`, as an
                        // interpolation hands one to `AppendFormatted<bool>`.
                        let numeric_for_bool = param == TypeSig::Boolean
                            && (arg.is_constant()
                                || matches!(arg, Expr::Conditional(..))
                                || typer.type_of(arg).is_some_and(|ty| {
                                    ty != TypeSig::Boolean && is_integral(typer, &ty)
                                }));
                        if is_integral(typer, &param) || numeric_for_bool {
                            fit_value(typer, arg, &param);
                        }
                    }
                }
            }
        });
    }
}

/// Writes the casts out, in the statements and every expression in them.
pub fn fit_types(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) {
    for stmt in stmts.iter_mut() {
        stmt.map_exprs(&mut |expr| fit_expr(typer, expr));
    }
    fit_switches(typer, stmts);
    fit_conditions(typer, stmts);
    let returns = typer.ctx.returns.clone();
    fit_returns(typer, stmts, &returns);
}

/// What an `if` or a loop tests is a `bool`.
fn fit_conditions(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) {
    for stmt in stmts.iter_mut() {
        match stmt {
            Stmt::If { condition, .. }
            | Stmt::While { condition, .. }
            | Stmt::DoWhile { condition, .. }
            | Stmt::For { condition, .. } => fit_value(typer, condition, &TypeSig::Boolean),
            Stmt::LocalFunction { .. } => continue,
            _ => {}
        }
        for block in stmt.blocks_mut() {
            fit_conditions(typer, block);
        }
    }
}

/// A switch on a number whose labels are members of an enum switches on
/// the enum: the variable the source switched on was a copy.
fn fit_switches(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) {
    for stmt in stmts.iter_mut() {
        if let Stmt::Switch { value, cases } = stmt
            && let Some(Some(Expr::EnumMember(ty, _))) = cases
                .iter()
                .flat_map(|case| case.labels.iter())
                .find(|label| label.is_some())
            && let Some(subject) = typer.type_of(value)
            && subject != *ty
            && typer.ctx.resolver.enum_underlying(&subject).is_none()
            && is_integral(typer, &subject)
        {
            let inner = std::mem::replace(value, Expr::Int(0));
            *value = cast(ty.clone(), inner);
        }
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        for block in stmt.blocks_mut() {
            fit_switches(typer, block);
        }
    }
}

/// The returns of a body, of the type it returns: a local function's of
/// its own.
fn fit_returns(typer: &Typer<'_, '_>, stmts: &mut [Stmt], returns: &TypeSig) {
    for stmt in stmts.iter_mut() {
        if let Stmt::LocalFunction {
            returns: own, body, ..
        } = stmt
        {
            let own = own.clone();
            fit_returns(typer, body, &own);
            continue;
        }
        if let Stmt::Return(Some(value)) = stmt {
            fit_value(typer, value, returns);
        }
        for block in stmt.blocks_mut() {
            fit_returns(typer, block, returns);
        }
    }
}

fn fit_expr(typer: &Typer<'_, '_>, expr: &mut Expr) {
    // C# has no `-` for a `ulong`: what IL negates is `0 - x`.
    if let Expr::Unary(crate::ir::UnOp::Neg, inner) = expr
        && typer.type_of(inner) == Some(TypeSig::UInt64)
    {
        let inner = std::mem::replace(inner.as_mut(), Expr::Int(0));
        *expr = Expr::Binary(BinOp::Sub, Box::new(Expr::Int(0)), Box::new(inner));
        return;
    }
    // `e + E.B` adds a number: the member is its value.
    if let Expr::Binary(BinOp::Add, left, right) = expr
        && let Expr::EnumMember(member_of, name) = right.as_ref()
        && typer.type_of(left).is_some_and(|ty| ty == *member_of)
        && let Some(members) = typer.ctx.resolver.enum_of(member_of)
        && let Some((_, number)) = members.iter().find(|(n, _)| n == name)
    {
        **right = Expr::Int(*number);
        return;
    }
    // An enum is multiplied, divided and shifted as its number.
    if let Expr::Binary(
        BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Shl | BinOp::Shr | BinOp::UShr,
        left,
        right,
    ) = expr
    {
        as_number(typer, left);
        as_number(typer, right);
        // A shift counts in an `int`.
        if let Expr::Binary(BinOp::Shl | BinOp::Shr | BinOp::UShr, _, count) = expr
            && !count.is_constant()
            && matches!(
                typer.type_of(count),
                Some(
                    TypeSig::UInt32
                        | TypeSig::Int64
                        | TypeSig::UInt64
                        | TypeSig::IntPtr
                        | TypeSig::UIntPtr
                )
            )
        {
            let inner = std::mem::replace(count.as_mut(), Expr::Int(0));
            **count = cast(TypeSig::Int32, inner);
        }
    }
    // `t ?? "null"`, two unrelated references, is an `object`.
    if let Expr::Binary(BinOp::Coalesce, left, right) = expr
        && let (Some(a), Some(TypeSig::String)) = (typer.type_of(left), typer.type_of(right))
        && !matches!(
            a,
            TypeSig::String | TypeSig::Object | TypeSig::Var(_) | TypeSig::MVar(_)
        )
        && !typer.ctx.resolver.is_value_type(&a)
        && !typer.ctx.resolver.is_interface(&a)
    {
        let inner = std::mem::replace(right.as_mut(), Expr::Int(0));
        **right = cast(TypeSig::Object, inner);
        return;
    }
    // `a ?? b` of two unrelated classes is of the class both derive from.
    if let Expr::Binary(BinOp::Coalesce, left, right) = expr
        && let (Some(a), Some(b)) = (typer.type_of(left), typer.type_of(right))
        && a != b
        && let Some(common) = typer.ctx.resolver.common_base(&a, &b)
        && common != a
        && common != b
    {
        let inner = std::mem::replace(right.as_mut(), Expr::Int(0));
        **right = cast(common, inner);
        return;
    }
    // `s ?? n`, a reference or a value, is an `object`.
    if let Expr::Binary(BinOp::Coalesce, left, right) = expr
        && let (Some(a), Some(b)) = (typer.type_of(left), typer.type_of(right))
        && !typer.ctx.resolver.is_value_type(&a)
        && !matches!(a, TypeSig::Var(_) | TypeSig::MVar(_))
        && typer.ctx.resolver.is_value_type(&b)
        && !matches!(b, TypeSig::Generic { .. })
    {
        let inner = std::mem::replace(right.as_mut(), Expr::Int(0));
        **right = cast(TypeSig::Object, inner);
        return;
    }
    // What is tested is a `bool`.
    match expr {
        Expr::Conditional(condition, ..) | Expr::Unary(crate::ir::UnOp::Not, condition) => {
            fit_value(typer, condition, &TypeSig::Boolean);
        }
        Expr::Binary(BinOp::LogicalAnd | BinOp::LogicalOr, left, right) => {
            fit_value(typer, left, &TypeSig::Boolean);
            fit_value(typer, right, &TypeSig::Boolean);
        }
        _ => {}
    }
    // `flags | n`: C# combines two of an enum, the number made one.
    if let Expr::Binary(BinOp::And | BinOp::Or | BinOp::Xor, left, right) = expr
        && let (Some(a), Some(b)) = (
            typer.type_of(left).map(dereferenced),
            typer.type_of(right).map(dereferenced),
        )
    {
        let is_enum = |ty: &TypeSig| typer.ctx.resolver.enum_underlying(ty).is_some();
        let number = |ty: &TypeSig| !is_enum(ty) && is_integral(typer, ty);
        // Two enums of different types: the right is made the left's.
        if is_enum(&a) && is_enum(&b) && a != b {
            let inner = std::mem::replace(right.as_mut(), Expr::Int(0));
            **right = cast(a, inner);
            return;
        }
        if is_enum(&a) && number(&b) {
            enum_operand(typer, right, &a);
            return;
        }
        if is_enum(&b) && number(&a) {
            enum_operand(typer, left, &b);
            return;
        }
    }
    if let Expr::Binary(
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor,
        ..,
    ) = expr
    {
        // `u & i` is a `long` in C#: the operation IL does is on the
        // unsigned type, which the signed operand is cast to.
        let Some(result @ (TypeSig::UInt32 | TypeSig::UInt64 | TypeSig::UIntPtr)) =
            typer.type_of(expr)
        else {
            return;
        };
        // Constants alone, one negative: wrapping it to unsigned would
        // overflow at compile time. The bits are the same either way, so
        // the operation is done signed, the zero-extended side made so.
        if result == TypeSig::UInt64
            && let Expr::Binary(_, left, right) = expr
            && left.is_constant()
            && right.is_constant()
        {
            let negative = |e: &Expr| {
                matches!(e, Expr::Int(n) | Expr::Long(n) if *n < 0)
                    || matches!(e, Expr::Cast(TypeSig::Int64, inner) if matches!(inner.as_ref(), Expr::Int(n) if *n < 0))
            };
            if negative(left) || negative(right) {
                for side in [left, right] {
                    if let Expr::Cast(TypeSig::UInt64, inner) = side.as_mut()
                        && matches!(inner.as_ref(), Expr::Int(n) | Expr::Long(n) if *n >= 0)
                    {
                        let inner = std::mem::replace(inner.as_mut(), Expr::Int(0));
                        **side = cast(TypeSig::Int64, inner);
                    }
                }
                return;
            }
        }
        let signed: Vec<bool> = match &*expr {
            Expr::Binary(_, left, right) => [left, right]
                .iter()
                .map(|side| {
                    !side.is_constant()
                        && matches!(
                            typer.type_of(side),
                            Some(
                                TypeSig::SByte
                                    | TypeSig::Int16
                                    | TypeSig::Int32
                                    | TypeSig::Int64
                                    | TypeSig::IntPtr
                            )
                        )
                })
                .collect(),
            _ => return,
        };
        if let Expr::Binary(_, left, right) = expr {
            for (side, signed) in [left, right].into_iter().zip(signed) {
                // A negative constant is the unsigned value it wraps to.
                let negative = matches!(side.as_ref(), Expr::Int(n) | Expr::Long(n) if *n < 0);
                if signed || negative {
                    let inner = std::mem::replace(side.as_mut(), Expr::Int(0));
                    **side = cast(result.clone(), inner);
                }
            }
        }
        return;
    }
    // `ulong` and `long` have no comparison in common: the one IL did is
    // said with a cast, to unsigned when it was unsigned or an equality.
    if let Expr::Compare {
        op,
        left,
        right,
        float: false,
        unordered,
    } = expr
    {
        // Two values of a type parameter are compared as references: C#
        // has no `==` for an unconstrained `T`.
        let parameter =
            |ty: Option<TypeSig>| matches!(ty, Some(TypeSig::Var(_) | TypeSig::MVar(_)));
        if (parameter(typer.type_of(left)) || parameter(typer.type_of(right)))
            && matches!(op, crate::ir::Cmp::Eq | crate::ir::Cmp::Ne)
            && !matches!(left.as_ref(), Expr::Null)
            && !matches!(right.as_ref(), Expr::Null)
        {
            for side in [left, right] {
                if !matches!(side.as_ref(), Expr::Cast(TypeSig::Object, _)) {
                    let inner = std::mem::replace(side.as_mut(), Expr::Int(0));
                    **side = cast(TypeSig::Object, inner);
                }
            }
            return;
        }
        let (Some(a), Some(b)) = (typer.type_of(left), typer.type_of(right)) else {
            return;
        };
        // A negated comparison of a type with operators of its own is the
        // operator it has, negated: `!(a <= b)`, where `a > b` is not there.
        let operator = |op: crate::ir::Cmp| match op {
            crate::ir::Cmp::Eq => "op_Equality",
            crate::ir::Cmp::Ne => "op_Inequality",
            crate::ir::Cmp::Lt => "op_LessThan",
            crate::ir::Cmp::Le => "op_LessThanOrEqual",
            crate::ir::Cmp::Gt => "op_GreaterThan",
            crate::ir::Cmp::Ge => "op_GreaterThanOrEqual",
        };
        let opposite = |op: crate::ir::Cmp| match op {
            crate::ir::Cmp::Eq => crate::ir::Cmp::Ne,
            crate::ir::Cmp::Ne => crate::ir::Cmp::Eq,
            crate::ir::Cmp::Lt => crate::ir::Cmp::Ge,
            crate::ir::Cmp::Le => crate::ir::Cmp::Gt,
            crate::ir::Cmp::Gt => crate::ir::Cmp::Le,
            crate::ir::Cmp::Ge => crate::ir::Cmp::Lt,
        };
        let resolver = typer.ctx.resolver;
        if a == b
            && resolver.as_primitive(&a).is_none()
            && resolver.enum_underlying(&a).is_none()
            && !matches!(a, TypeSig::Pointer(_) | TypeSig::Var(_) | TypeSig::MVar(_))
            && resolver.declares_method(&a, operator(opposite(*op)))
            && !resolver.declares_method(&a, operator(*op))
        {
            let flipped = Expr::Compare {
                op: opposite(*op),
                left: left.clone(),
                right: right.clone(),
                float: false,
                unordered: *unordered,
            };
            *expr = Expr::Unary(crate::ir::UnOp::Not, Box::new(flipped));
            return;
        }
        // An enum compared with a number is compared as its number.
        let enum_a = typer.ctx.resolver.enum_underlying(&a).is_some();
        let enum_b = typer.ctx.resolver.enum_underlying(&b).is_some();
        if enum_a != enum_b {
            let (side, other) = if enum_a { (left, &b) } else { (right, &a) };
            if is_integral(typer, other) {
                as_number(typer, side);
            }
            return;
        }
        // A negative constant compared with an unsigned value is the value
        // it wraps to, when the comparison is unsigned; a signed one takes
        // the unsigned value as signed.
        let unsigned_compare = *unordered || matches!(op, crate::ir::Cmp::Eq | crate::ir::Cmp::Ne);
        let negative = |e: &Expr| matches!(e, Expr::Int(n) | Expr::Long(n) if *n < 0);
        let signed_of = |ty: &TypeSig| match ty {
            TypeSig::UInt32 => Some(TypeSig::Int32),
            TypeSig::UInt64 => Some(TypeSig::Int64),
            TypeSig::UIntPtr => Some(TypeSig::IntPtr),
            _ => None,
        };
        if negative(left)
            && let Some(signed) = signed_of(&b)
        {
            if unsigned_compare {
                let inner = std::mem::replace(left.as_mut(), Expr::Int(0));
                **left = cast(b.clone(), inner);
            } else {
                let inner = std::mem::replace(right.as_mut(), Expr::Int(0));
                **right = cast(signed, inner);
            }
            return;
        }
        if negative(right)
            && let Some(signed) = signed_of(&a)
        {
            if unsigned_compare {
                let inner = std::mem::replace(right.as_mut(), Expr::Int(0));
                **right = cast(a.clone(), inner);
            } else {
                let inner = std::mem::replace(left.as_mut(), Expr::Int(0));
                **left = cast(signed, inner);
            }
            return;
        }
        let pair = (a == TypeSig::UInt64 && b == TypeSig::Int64)
            || (a == TypeSig::Int64 && b == TypeSig::UInt64);
        if !pair {
            return;
        }
        let to_unsigned = *unordered || matches!(op, crate::ir::Cmp::Eq | crate::ir::Cmp::Ne);
        let (from, to) = if to_unsigned {
            (TypeSig::Int64, TypeSig::UInt64)
        } else {
            (TypeSig::UInt64, TypeSig::Int64)
        };
        for side in [left, right] {
            if typer.type_of(side).as_ref() == Some(&from) {
                if side.is_constant() {
                    let coerced = coerce_expr(typer.ctx.resolver, (**side).clone(), &to);
                    **side = coerced;
                } else {
                    let inner = std::mem::replace(side.as_mut(), Expr::Int(0));
                    **side = cast(to.clone(), inner);
                }
            }
        }
        return;
    }
    match expr {
        Expr::Compound(
            op @ (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor),
            target,
            value,
        ) => {
            if let Some(ty) = typer.type_of(target).map(dereferenced) {
                // `e += 1` on an enum adds a number.
                let ty = match typer.ctx.resolver.enum_underlying(&ty) {
                    Some(underlying) if matches!(op, BinOp::Add | BinOp::Sub) => {
                        if let Expr::Cast(cast_to, inner) = value.as_ref()
                            && inner.is_constant()
                            && *cast_to == ty
                        {
                            let inner = (**inner).clone();
                            **value = inner;
                        }
                        // A member the constant was taken for is its value.
                        if let Expr::EnumMember(member_of, name) = value.as_ref()
                            && *member_of == ty
                            && let Some(members) = typer.ctx.resolver.enum_of(&ty)
                            && let Some((_, number)) = members.iter().find(|(n, _)| n == name)
                        {
                            **value = Expr::Int(*number);
                        }
                        underlying
                    }
                    _ => ty,
                };
                fit(typer, value, &ty);
            }
        }
        Expr::Assign(target, value) => {
            // A store through a `ref` or `out` parameter is of its element.
            if let Some(ty) = typer.type_of(target) {
                let ty = match ty {
                    TypeSig::ByRef(inner) => *inner,
                    other => other,
                };
                fit(typer, value, &ty);
            }
        }
        Expr::Call {
            method,
            args,
            receiver,
        } => {
            // A member a class implements only explicitly is reached
            // through the interface.
            // `x?.M()` casts `x`.
            let mut receiver = match receiver.as_deref_mut() {
                Some(Expr::MaybeNull(inner)) => Some(inner),
                _ => receiver.as_mut(),
            };
            if let Some(receiver) = receiver.as_deref_mut()
                && !matches!(receiver.as_ref(), Expr::Cast(..))
                && typer.ctx.resolver.is_interface(&method.declaring)
                && let Some(ty) = typer.type_of(receiver)
                && !typer.ctx.resolver.is_interface(&ty)
                && (typer.ctx.resolver.implements_explicitly(&ty, &method.name)
                    // An array implements the collection interfaces
                    // explicitly.
                    || matches!(ty, TypeSig::Vector(_) | TypeSig::Array { .. }))
            {
                let inner = std::mem::replace(receiver.as_mut(), Expr::Int(0));
                **receiver = cast(method.declaring.clone(), inner);
            }
            if let Some(receiver) = receiver.as_deref_mut() {
                assigned_receiver(typer, receiver);
                // `int`'s method on a `char`: IL had no conversion to make.
                if method.sig.instance
                    && let Some(wanted) = typer.ctx.resolver.as_primitive(&method.declaring)
                    && is_integral(typer, &wanted)
                    && let Some(given) = typer.type_of(receiver)
                    && is_integral(typer, &given)
                    && typer.ctx.resolver.as_primitive(&given).is_some()
                    && typer.ctx.resolver.as_primitive(&given) != Some(wanted.clone())
                {
                    let inner = std::mem::replace(receiver.as_mut(), Expr::Int(0));
                    **receiver = cast(wanted, inner);
                }
            }
            // A struct's method is called on the struct: a value that
            // converts to it, `T[]` to `Memory<T>`, is converted first.
            if let Some(receiver) = receiver
                && method.sig.instance
                && typer.ctx.resolver.is_value_type(&method.declaring)
                && let Some(TypeSig::Vector(_)) = typer.type_of(receiver)
            {
                let inner = std::mem::replace(receiver.as_mut(), Expr::Int(0));
                **receiver = cast(method.declaring.clone(), inner);
            }
            for (at, arg) in args.iter_mut().enumerate() {
                if let Some(declared) = method.sig.parameters.get(at) {
                    let param = substitute(declared, &method.declaring, &method.type_args);
                    fit_value(typer, arg, &param);
                    pick_overload(typer, method, at, arg, &param);
                    // A constant given for a `T` the call infers from its
                    // other arguments has to be of that type already.
                    // So does one where an overload taking an `int`
                    // could be picked instead.
                    let small = matches!(
                        param,
                        TypeSig::Byte | TypeSig::SByte | TypeSig::Int16 | TypeSig::UInt16
                    );
                    if ((matches!(declared, TypeSig::MVar(_))
                        && is_integral(typer, &param)
                        && param != TypeSig::Int32
                        && param != TypeSig::Int64)
                        || (small && typer.ctx.resolver.is_overloaded(method)))
                        && matches!(arg, Expr::Int(_) | Expr::Long(_))
                    {
                        let inner = std::mem::replace(arg, Expr::Int(0));
                        *arg = cast(param, inner);
                    }
                }
            }
        }
        Expr::Property {
            receiver: Some(receiver),
            declaring,
            name,
            ..
        } => {
            let receiver = match receiver.as_mut() {
                Expr::MaybeNull(inner) => inner,
                _ => receiver,
            };
            assigned_receiver(typer, receiver);
            if !matches!(receiver.as_ref(), Expr::Cast(..))
                && typer.ctx.resolver.is_interface(declaring)
                && let Some(ty) = typer.type_of(receiver)
                && !typer.ctx.resolver.is_interface(&ty)
                && (typer
                    .ctx
                    .resolver
                    .implements_explicitly(&ty, &format!("get_{name}"))
                    || matches!(ty, TypeSig::Vector(_) | TypeSig::Array { .. }))
            {
                let inner = std::mem::replace(receiver.as_mut(), Expr::Int(0));
                **receiver = cast(declaring.clone(), inner);
            }
        }
        Expr::NewArray {
            element,
            items: Some(items),
            ..
        } => {
            let element = element.clone();
            for item in items.iter_mut() {
                fit_value(typer, item, &element);
            }
        }
        // An index is an `int`: an enum used as one is its number.
        Expr::Index { indices, .. } => {
            for index in indices.iter_mut() {
                as_number(typer, index);
            }
        }
        Expr::Indexer { receiver, args } => {
            let spanned = typer.type_of(receiver).is_some_and(|ty| {
                matches!(ty, TypeSig::Vector(_) | TypeSig::Array { .. }) || span_like(typer, &ty)
            });
            if spanned {
                for index in args.iter_mut() {
                    as_number(typer, index);
                }
            }
        }
        Expr::New { ctor, args, .. } => {
            for (at, arg) in args.iter_mut().enumerate() {
                if let Some(param) = ctor.sig.parameters.get(at) {
                    let param = substitute(param, &ctor.declaring, &[]);
                    fit_value(typer, arg, &param);
                    pick_overload(typer, ctor, at, arg, &param);
                }
            }
        }
        _ => {}
    }
}

/// `(x = new D()).M()`: an assignment is of its variable's type, which
/// may not have what the value's has; the value's type is said.
fn assigned_receiver(typer: &Typer<'_, '_>, receiver: &mut Box<Expr>) {
    if let Expr::Assign(target, value) = receiver.as_ref()
        && let (Some(variable), Some(assigned)) = (typer.type_of(target), typer.type_of(value))
        // An `out` parameter's is what it refers to.
        && let variable = match variable {
            TypeSig::ByRef(inner) => *inner,
            other => other,
        }
        && variable != assigned
        && !typer.ctx.resolver.is_value_type(&assigned)
    {
        let inner = std::mem::replace(receiver.as_mut(), Expr::Int(0));
        **receiver = cast(assigned, inner);
    }
}

/// A reference given where another overload takes exactly its type is
/// cast to the parameter, which says the overload IL calls:
/// `this(n, (IEnumerable<string>)names)`, `Write((object)s)`.
fn pick_overload(
    typer: &Typer<'_, '_>,
    method: &crate::names::MethodRef,
    at: usize,
    arg: &mut Expr,
    param: &TypeSig,
) {
    let resolver = typer.ctx.resolver;
    if arg.is_constant()
        || matches!(
            arg,
            Expr::Null
                | Expr::Cast(..)
                | Expr::Lambda { .. }
                | Expr::Delegate { .. }
                // A `Type`, which the typer does not name.
                | Expr::TypeOf(_)
                | Expr::Box(..)
        )
        || matches!(param, TypeSig::ByRef(_) | TypeSig::Pointer(_))
        || resolver.is_value_type(param)
    {
        return;
    }
    let Some(from) = typer.type_of(arg) else {
        return;
    };
    if from == *param
        || resolver.is_value_type(&from)
        || matches!(from, TypeSig::Var(_) | TypeSig::MVar(_))
        || !resolver.another_overload_takes(method, at, &from)
    {
        return;
    }
    let inner = std::mem::replace(arg, Expr::Int(0));
    *arg = cast(param.clone(), inner);
}

/// A number, a `char` or an enum: what IL treats as one.
fn is_integral(typer: &Typer<'_, '_>, ty: &TypeSig) -> bool {
    matches!(
        ty,
        TypeSig::IntPtr
            | TypeSig::UIntPtr
            | TypeSig::SByte
            | TypeSig::Byte
            | TypeSig::Int16
            | TypeSig::UInt16
            | TypeSig::Char
            | TypeSig::Int32
            | TypeSig::UInt32
            | TypeSig::Int64
            | TypeSig::UInt64
    ) || typer.ctx.resolver.enum_underlying(ty).is_some()
}

/// Casts a value to the type it goes into, when C# would not convert it.
fn fit(typer: &Typer<'_, '_>, value: &mut Box<Expr>, to: &TypeSig) {
    fit_value(typer, value.as_mut(), to);
}

pub(crate) fn fit_value(typer: &Typer<'_, '_>, value: &mut Expr, to: &TypeSig) {
    // `x = y` is of `x`'s type, which may be wider than what `y` was, and
    // than what is wanted.
    if let Expr::Assign(target, assigned) = value
        && !typer.ctx.resolver.is_value_type(to)
        && let (Some(variable), Some(given)) = (typer.type_of(target), typer.type_of(assigned))
        && variable != *to
        && given == *to
    {
        let inner = std::mem::replace(value, Expr::Int(0));
        *value = cast(to.clone(), inner);
        return;
    }
    // A `T?` takes what a `T` does.
    if let TypeSig::Generic {
        definition,
        arguments,
    } = to
        && let [inner] = arguments.as_slice()
        && matches!(definition.as_ref(), TypeSig::ValueType(token)
            if typer.ctx.resolver.raw_name(*token).as_deref() == Some("System.Nullable`1"))
    {
        fit_value(typer, value, inner);
        return;
    }
    // A tuple's items go into its type's arguments.
    if let Expr::Tuple(items) = value
        && let TypeSig::Generic { arguments, .. } = to
        && items.len() == arguments.len()
    {
        for (item, ty) in items.iter_mut().zip(arguments) {
            fit_value(typer, item, ty);
        }
        return;
    }
    // A pointer and a native integer are one thing to IL, and a pointer
    // of one type another's; C# converts to `void*` alone.
    let pointerish =
        |ty: &TypeSig| matches!(ty, TypeSig::Pointer(_) | TypeSig::IntPtr | TypeSig::UIntPtr);
    let from_pointer = matches!(
        typer.type_of(value),
        Some(TypeSig::Pointer(_) | TypeSig::ByRef(_))
    );
    if matches!(to, TypeSig::Pointer(_)) || (pointerish(to) && from_pointer) {
        // `&x` given for a pointer is a pointer to what `x` is.
        let from = match (typer.type_of(value), &*value) {
            (Some(TypeSig::ByRef(inner)), Expr::Unary(crate::ir::UnOp::AddressOf, _)) => {
                Some(TypeSig::Pointer(inner))
            }
            (other, _) => other,
        };
        if let Some(from) = from
            && pointerish(&from)
            && from != *to
            // Any pointer is a `void*` to C#, a number not.
            && !(matches!(to, TypeSig::Pointer(inner) if **inner == TypeSig::Void)
                && matches!(from, TypeSig::Pointer(_)))
            && (matches!(from, TypeSig::Pointer(_)) || matches!(to, TypeSig::Pointer(_)))
            && !value.is_constant()
        {
            // `(char*)0`, not `(char*)(nuint)0`.
            let inner = match std::mem::replace(value, Expr::Int(0)) {
                Expr::Cast(TypeSig::IntPtr | TypeSig::UIntPtr, constant)
                    if constant.is_constant() && matches!(to, TypeSig::Pointer(_)) =>
                {
                    *constant
                }
                other => other,
            };
            *value = cast(to.clone(), inner);
        }
        return;
    }
    // `(ushort)x` stored in a `char` is `(char)x`: IL has one conversion
    // for both.
    if *to == TypeSig::Char
        && let Expr::Cast(TypeSig::UInt16, inner) = value
    {
        let inner = std::mem::replace(inner.as_mut(), Expr::Int(0));
        *value = cast(TypeSig::Char, inner);
        return;
    }
    // A `bool` and a number are one thing to IL too.
    if *to == TypeSig::Boolean {
        match value {
            Expr::Int(n) | Expr::Long(n) => *value = Expr::Bool(*n != 0),
            Expr::Conditional(_, a, b) => {
                fit_value(typer, a, to);
                fit_value(typer, b, to);
            }
            other
                if typer
                    .type_of(other)
                    .is_some_and(|from| from != TypeSig::Boolean && is_integral(typer, &from)) =>
            {
                let inner = std::mem::replace(other, Expr::Int(0));
                *other = Expr::compare(crate::ir::Cmp::Ne, inner, Expr::Int(0));
            }
            _ => {}
        }
        return;
    }
    if is_integral(typer, to)
        && typer.type_of(value) == Some(TypeSig::Boolean)
        && !value.is_constant()
    {
        let inner = std::mem::replace(value, Expr::Int(0));
        *value = Expr::Conditional(
            Box::new(inner),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(0)),
        );
        return;
    }
    if !is_integral(typer, to) {
        return;
    }
    // Each branch of `c ? a : b` goes where it does. A constant in one
    // is an `int` to C#, and makes the whole an `int` where the other
    // is of a smaller type: it is cast.
    if let Expr::Conditional(_, a, b) = value {
        let small = matches!(
            to,
            TypeSig::Byte | TypeSig::SByte | TypeSig::Int16 | TypeSig::UInt16 | TypeSig::Char
        );
        for branch in [&mut *a, &mut *b] {
            fit_value(typer, branch, to);
            if small && matches!(branch.as_ref(), Expr::Int(_)) {
                let inner = std::mem::replace(branch.as_mut(), Expr::Int(0));
                **branch = cast(to.clone(), inner);
            }
        }
        // `c ? 1 : 0` is an `int` whatever it goes into: one constant
        // says the type.
        if !small
            && *to != TypeSig::Int32
            && matches!(a.as_ref(), Expr::Int(_))
            && matches!(b.as_ref(), Expr::Int(_))
        {
            let inner = std::mem::replace(a.as_mut(), Expr::Int(0));
            **a = cast(to.clone(), inner);
        }
        return;
    }
    let Some(from) = typer.type_of(value) else {
        return;
    };
    if from == *to || !is_integral(typer, &from) || implicit_numeric(&from, to) {
        return;
    }
    // A member of one enum where another is wanted.
    if let Expr::EnumMember(member_of, _) = value
        && *member_of != *to
        && typer.ctx.resolver.enum_underlying(to).is_some()
    {
        let inner = std::mem::replace(value, Expr::Int(0));
        *value = cast(to.clone(), inner);
        return;
    }
    if value.is_constant() {
        let coerced = coerce_expr(typer.ctx.resolver, value.clone(), to);
        // A constant stored into a smaller type is what fits of it:
        // `65520` in a `short` is `-16`.
        let coerced = match coerced {
            Expr::Int(n) => Expr::Int(match to {
                TypeSig::Int16 => i64::from(n as i16),
                TypeSig::SByte => i64::from(n as i8),
                TypeSig::Byte if n > 0 => i64::from(n as u8),
                TypeSig::UInt16 if n > 0 => i64::from(n as u16),
                _ => n,
            }),
            other => other,
        };
        // A negative constant stored unsigned is the value it wraps to,
        // which the cast says: `uint.MaxValue`.
        *value = match coerced {
            Expr::Int(n) | Expr::Long(n)
                if n < 0
                    && matches!(
                        to,
                        TypeSig::Byte | TypeSig::UInt16 | TypeSig::UInt32 | TypeSig::UInt64
                    ) =>
            {
                cast(to.clone(), Expr::Int(n))
            }
            other => other,
        };
        return;
    }
    let inner = std::mem::replace(value, Expr::Int(0));
    *value = cast(to.clone(), inner);
}

/// What a `ref` variable refers to, read.
fn dereferenced(ty: TypeSig) -> TypeSig {
    match ty {
        TypeSig::ByRef(inner) => *inner,
        other => other,
    }
}

/// A number combined with an enum by `&`, `|` or `^`, made one of it: a
/// constant as its members where it can be.
fn enum_operand(typer: &Typer<'_, '_>, side: &mut Box<Expr>, ty: &TypeSig) {
    if side.is_constant() {
        let coerced = coerce_expr(typer.ctx.resolver, (**side).clone(), ty);
        **side = match coerced {
            constant @ (Expr::Int(_) | Expr::Long(_)) => cast(ty.clone(), constant),
            other => other,
        };
        return;
    }
    let inner = std::mem::replace(side.as_mut(), Expr::Int(0));
    **side = cast(ty.clone(), inner);
}

/// An enum where a number is wanted: its number.
fn as_number(typer: &Typer<'_, '_>, value: &mut Expr) {
    if let Some(ty) = typer.type_of(value)
        && let Some(underlying) = typer.ctx.resolver.enum_underlying(&ty)
    {
        let inner = std::mem::replace(value, Expr::Int(0));
        *value = cast(underlying, inner);
    }
}

/// `Span<T>` or `ReadOnlySpan<T>`, indexed by an `int`.
fn span_like(typer: &Typer<'_, '_>, ty: &TypeSig) -> bool {
    let TypeSig::Generic { definition, .. } = ty else {
        return false;
    };
    let (TypeSig::ValueType(token) | TypeSig::Class(token)) = definition.as_ref() else {
        return false;
    };
    matches!(
        typer.ctx.resolver.raw_name(*token).as_deref(),
        Some("System.Span`1" | "System.ReadOnlySpan`1")
    )
}

/// `(T)e`, through a cast `e` already has when that one only widened.
fn cast(to: TypeSig, value: Expr) -> Expr {
    Expr::Cast(to, Box::new(value))
}
