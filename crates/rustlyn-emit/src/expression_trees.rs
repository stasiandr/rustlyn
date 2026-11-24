//! Expression trees: a lambda converted to `Expression<TDelegate>`.
//!
//! Such a lambda is not compiled into a method. It is compiled into code
//! that *describes* it (§12.19.3): a call to `Expression.Parameter` per
//! parameter, a factory call per node of the body — `Expression.Add`,
//! `Expression.Property`, `Expression.Call` — and `Expression.Lambda<T>`
//! around the lot. What the program then holds is data about the lambda,
//! which a query provider can read, or which `Compile()` can turn back into
//! code.
//!
//! Members are named the way reflection names them: a `MethodInfo` is
//! `ldtoken` on the method and `MethodBase.GetMethodFromHandle`, a
//! `FieldInfo` is the same through `FieldInfo.GetFieldFromHandle`, and a
//! `Type` is `Type.GetTypeFromHandle`, as `typeof` is.

use rustlyn_semantics::{
    BinaryOperator, BoundExpression, BoundExpressionKind, BoundStatementKind, ConstantValue,
    ConversionKind, LocalId, SpecialType, SymbolId, SymbolKind, Type, UnaryOperator,
};

use crate::codegen::BodyEmitter;
use crate::emitter::EmitError;
use crate::il::{Instruction, Token};
use crate::signature::{ElementType, SigType, generic_method_signature};

const EXPRESSION: &str = "System.Linq.Expressions.Expression";

/// The parameters of the lambdas being described, innermost last: each is a
/// local of the lambda's body and a slot holding its `ParameterExpression`.
#[derive(Default)]
struct Tree {
    parameters: Vec<(LocalId, u16)>,
}

impl BodyEmitter<'_, '_> {
    /// Whether a type is `Expression<TDelegate>`: a lambda converted to it
    /// is described rather than compiled.
    pub(crate) fn is_expression_tree_type(&self, ty: &Type) -> bool {
        let symbols = self.emitter.compilation.symbols();
        matches!(ty, Type::Named { symbol, type_arguments }
            if type_arguments.len() == 1
                && symbols.qualified_name(*symbol) == "System.Linq.Expressions.Expression`1")
    }

    /// Leaves an `Expression<TDelegate>` describing lambda `index` on the
    /// stack.
    pub(crate) fn emit_expression_tree(
        &mut self,
        tree_type: &Type,
        index: usize,
    ) -> Result<(), EmitError> {
        let Type::Named { type_arguments, .. } = tree_type else {
            return Err(EmitError::new("an expression tree of no delegate type"));
        };
        let delegate = type_arguments[0].clone();
        let mut tree = Tree::default();
        self.emit_lambda_tree(index, &delegate, &mut tree)
    }

    /// `Expression.Lambda<TDelegate>(body, parameters)` for one lambda,
    /// whose parameters are in view for its body and for any lambda inside.
    fn emit_lambda_tree(
        &mut self,
        index: usize,
        delegate: &Type,
        tree: &mut Tree,
    ) -> Result<(), EmitError> {
        let lambda =
            self.body.lambdas.get(index).cloned().ok_or_else(|| {
                EmitError::new("an expression tree of a lambda that was never bound")
            })?;
        let opened = tree.parameters.len();
        let parameter_expression = self.tree_named("ParameterExpression");
        let string = SigType::Primitive(ElementType::String);
        let system_type = self.reflection_named("System.Type");
        let parameter_factory = self.emitter.framework_member(
            EXPRESSION,
            "Parameter",
            false,
            &parameter_expression,
            &[system_type.clone(), string.clone()],
        );
        for local in &lambda.parameters {
            let symbol = self
                .body
                .locals
                .get(local.0 as usize)
                .cloned()
                .ok_or_else(|| EmitError::new("a lambda parameter with no local"))?;
            self.push_type(&symbol.ty)?;
            let name = self.emitter.metadata.user_string(&symbol.name);
            self.stream.emit(Instruction::LoadString(name));
            self.stream
                .call_effect(Instruction::Call(parameter_factory), 2, 1);
            let slot = self.locals.len() as u16;
            self.locals.push(parameter_expression.clone());
            self.local_types.push(Type::Error);
            self.stream.emit(Instruction::StoreLocal(slot));
            tree.parameters.push((*local, slot));
        }

        // The body: an expression, or a block that only returns one. A
        // statement body cannot be a tree (§12.19.3), and the binder said so.
        let mut body = tree_body(&lambda.body).ok_or_else(|| {
            EmitError::new("a lambda with a statement body cannot be an expression tree")
        })?;
        // `(a, b) => null` for a `Func<A, B, R>` is a constant `R`: the tree
        // checks its body against what the delegate returns.
        if matches!(body.kind, BoundExpressionKind::Literal(ConstantValue::Null))
            && matches!(body.ty, Type::Null)
            && let Some(owner) = delegate.symbol()
            && let Some(invoke) = self
                .emitter
                .compilation
                .symbols()
                .lookup(owner, "Invoke")
                .first()
                .copied()
        {
            let substitution = self.emitter.binder.type_substitution(delegate);
            let returns = self.emitter.type_of(invoke).substitute(&substitution);
            if !matches!(returns, Type::Void) && !returns.is_error() {
                body.ty = returns;
            }
        }
        self.emit_tree_node(&body, tree)?;

        // `new ParameterExpression[] { p1, p2 }`.
        let own = &tree.parameters[opened..];
        let element = self.emitter.references.type_ref(
            &mut self.emitter.metadata,
            "System.Linq.Expressions.ParameterExpression",
        );
        self.stream.emit(Instruction::LoadInt32(own.len() as i32));
        self.stream.emit(Instruction::NewArray(element));
        for (position, (_, slot)) in own.iter().enumerate() {
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadInt32(position as i32));
            self.stream.emit(Instruction::LoadLocal(*slot));
            self.stream.emit(Instruction::StoreElementRef);
        }

        // `Expression.Lambda<TDelegate>(Expression, ParameterExpression[])`.
        let expression = self.tree_named("Expression");
        let returns = SigType::Constructed {
            value_type: false,
            coded: self.emitter.references.type_ref_coded(
                &mut self.emitter.metadata,
                "System.Linq.Expressions.Expression`1",
            ),
            arguments: vec![SigType::MethodTypeParameter(0)],
        };
        let signature = generic_method_signature(
            false,
            1,
            &returns,
            &[expression, SigType::Array(Box::new(parameter_expression))],
        );
        let member = self.emitter.references.member_ref(
            &mut self.emitter.metadata,
            EXPRESSION,
            "Lambda",
            &signature,
        );
        let instantiated = self
            .emitter
            .method_instantiation(member, std::slice::from_ref(delegate))?;
        self.stream
            .call_effect(Instruction::Call(instantiated), 2, 1);
        tree.parameters.truncate(opened);
        Ok(())
    }

    /// Leaves the `Expression` describing one node on the stack.
    fn emit_tree_node(&mut self, node: &BoundExpression, tree: &mut Tree) -> Result<(), EmitError> {
        match &node.kind {
            BoundExpressionKind::Local(local) => {
                if let Some((_, slot)) = tree
                    .parameters
                    .iter()
                    .rev()
                    .find(|(parameter, _)| parameter == local)
                {
                    self.stream.emit(Instruction::LoadLocal(*slot));
                    return Ok(());
                }
                // A variable of the method around the lambda: the tree
                // reads it off the class the closure keeps it in, so that
                // it sees the value the variable has when the tree is run.
                let Some(capture) = self.captured_local_public(*local) else {
                    return Err(EmitError::new(
                        "a variable used in an expression tree that the lambda does not capture",
                    ));
                };
                self.emit_captured_field(capture.0, capture.1, node)
            }
            BoundExpressionKind::Parameter(parameter) => {
                let Some(capture) = self.captured_parameter_public(*parameter) else {
                    return Err(EmitError::new(
                        "a parameter used in an expression tree that the lambda does not capture",
                    ));
                };
                self.emit_captured_field(capture.0, capture.1, node)
            }
            BoundExpressionKind::Literal(ConstantValue::Null) => {
                self.stream.emit(Instruction::LoadNull);
                let ty = if matches!(node.ty, Type::Null) || node.ty.is_error() {
                    self.object_type()?
                } else {
                    node.ty.clone()
                };
                self.push_type(&ty)?;
                self.constant_factory(true)
            }
            BoundExpressionKind::Literal(_)
            | BoundExpressionKind::This
            | BoundExpressionKind::TypeOf(_)
            | BoundExpressionKind::SizeOf(_) => {
                // A value the tree holds as it is: `Expression.Constant`.
                self.emit_expression(node, true)?;
                self.box_if_needed(&node.ty)?;
                self.push_type(&node.ty)?;
                self.constant_factory(true)
            }
            // A method group made a delegate is, in a tree, the method
            // asked for one: `Convert(M.CreateDelegate(typeof(D), target),
            // D)`, the method held as a constant `MethodInfo` (as `csc`
            // writes it).
            BoundExpressionKind::DelegateCreation {
                method,
                receiver,
                type_arguments,
                ..
            } => {
                let receiver_type = receiver.as_ref().map(|receiver| receiver.ty.clone());
                let token = self.method_token_on(*method, receiver_type.as_ref())?;
                let token = if type_arguments.is_empty() {
                    token
                } else {
                    self.emitter.method_instantiation(token, type_arguments)?
                };
                let declaring = self.declaring_type_of(*method, receiver_type.as_ref());
                // `Expression.Constant((object)methodInfo, typeof(MethodInfo))`.
                self.push_method_info(token, &declaring, "System.Reflection.MethodInfo")?;
                let method_info_type = self
                    .emitter
                    .compilation
                    .type_by_metadata_name("System.Reflection.MethodInfo")
                    .map(Type::named)
                    .ok_or_else(|| EmitError::new("`MethodInfo` is not referenced"))?;
                self.push_type(&method_info_type)?;
                self.constant_factory(true)?;
                // `MethodInfo.CreateDelegate(Type, object)`, named for the call.
                let system_type = self.reflection_named("System.Type");
                let delegate = self.reflection_named("System.Delegate");
                let create = self.emitter.framework_member(
                    "System.Reflection.MethodInfo",
                    "CreateDelegate",
                    true,
                    &delegate,
                    &[system_type.clone(), SigType::Primitive(ElementType::Object)],
                );
                self.push_method_info(create, &method_info_type, "System.Reflection.MethodInfo")?;
                // Its arguments: the delegate's type, and the target.
                let element = self
                    .emitter
                    .references
                    .type_ref(&mut self.emitter.metadata, EXPRESSION);
                self.stream.emit(Instruction::LoadInt32(2));
                self.stream.emit(Instruction::NewArray(element));
                self.stream.emit(Instruction::Dup);
                self.stream.emit(Instruction::LoadInt32(0));
                self.push_type(&node.ty)?;
                let type_type = self
                    .emitter
                    .compilation
                    .type_by_metadata_name("System.Type")
                    .map(Type::named)
                    .ok_or_else(|| EmitError::new("`Type` is not referenced"))?;
                self.push_type(&type_type)?;
                self.constant_factory(true)?;
                self.stream.emit(Instruction::StoreElementRef);
                self.stream.emit(Instruction::Dup);
                self.stream.emit(Instruction::LoadInt32(1));
                match receiver.as_deref() {
                    Some(target)
                        if !matches!(target.kind, BoundExpressionKind::TypeExpression(_)) =>
                    {
                        self.emit_tree_node(target, tree)?;
                    }
                    _ => {
                        self.stream.emit(Instruction::LoadNull);
                        let object = self.object_type()?;
                        self.push_type(&object)?;
                        self.constant_factory(true)?;
                    }
                }
                self.stream.emit(Instruction::StoreElementRef);
                let call = self.tree_named("MethodCallExpression");
                let expression = self.tree_named("Expression");
                let method_info = self.reflection_named("System.Reflection.MethodInfo");
                let factory = self.emitter.framework_member(
                    EXPRESSION,
                    "Call",
                    false,
                    &call,
                    &[
                        expression.clone(),
                        method_info,
                        SigType::Array(Box::new(expression)),
                    ],
                );
                self.stream.call_effect(Instruction::Call(factory), 3, 1);
                self.push_type(&node.ty)?;
                self.unary_type_factory("Convert", "UnaryExpression")
            }
            // `$"a: {a}"` in a tree is the `string.Format("a: {0}", a)` it
            // means, as `csc` writes it there: a tree has no interpolation.
            // The binder writes it so; this is for one it did not.
            BoundExpressionKind::InterpolatedString(parts) => {
                let mut format = String::new();
                let mut holes: Vec<&BoundExpression> = Vec::new();
                for part in parts {
                    match &part.kind {
                        BoundExpressionKind::Literal(ConstantValue::String(text)) => {
                            format.push_str(&text.replace('{', "{{").replace('}', "}}"));
                        }
                        BoundExpressionKind::StringInsert {
                            value,
                            alignment,
                            format: clauses,
                        } => {
                            format.push('{');
                            format.push_str(&holes.len().to_string());
                            format.push_str(&rustlyn_semantics::composite_clauses(
                                *alignment,
                                clauses.as_deref(),
                            ));
                            format.push('}');
                            holes.push(value);
                        }
                        _ => {
                            format.push('{');
                            format.push_str(&holes.len().to_string());
                            format.push('}');
                            holes.push(part);
                        }
                    }
                }
                if holes.len() > 3 {
                    return Err(EmitError::new(
                        "an interpolated string of more than three holes cannot be written in an expression tree yet",
                    ));
                }
                let string = SigType::Primitive(ElementType::String);
                let object = SigType::Primitive(ElementType::Object);
                let mut parameters = vec![string.clone()];
                parameters.extend(std::iter::repeat_n(object, holes.len()));
                let format_method = self.emitter.framework_member(
                    "System.String",
                    "Format",
                    false,
                    &string,
                    &parameters,
                );
                let string_type = self
                    .emitter
                    .compilation
                    .special_type(rustlyn_semantics::SpecialType::String)
                    .map(Type::named)
                    .ok_or_else(|| EmitError::new("`string` is not referenced"))?;
                // `Expression.Call(null, Format, [Constant(format), holes...])`.
                self.stream.emit(Instruction::LoadNull);
                self.push_method_info(format_method, &string_type, "System.Reflection.MethodInfo")?;
                let element = self
                    .emitter
                    .references
                    .type_ref(&mut self.emitter.metadata, EXPRESSION);
                self.stream
                    .emit(Instruction::LoadInt32(holes.len() as i32 + 1));
                self.stream.emit(Instruction::NewArray(element));
                self.stream.emit(Instruction::Dup);
                self.stream.emit(Instruction::LoadInt32(0));
                let token = self.emitter.metadata.user_string(&format);
                self.stream.emit(Instruction::LoadString(token));
                self.push_type(&string_type)?;
                self.constant_factory(true)?;
                self.stream.emit(Instruction::StoreElementRef);
                let object_type = self.object_type()?;
                for (position, hole) in holes.iter().enumerate() {
                    self.stream.emit(Instruction::Dup);
                    self.stream
                        .emit(Instruction::LoadInt32(position as i32 + 1));
                    self.emit_tree_node(hole, tree)?;
                    // A value is boxed on its way to `object`, which a tree
                    // says with a `Convert`; a reference needs nothing.
                    if !hole
                        .ty
                        .is_reference_type(self.emitter.compilation.symbols())
                    {
                        self.push_type(&object_type)?;
                        self.unary_type_factory("Convert", "UnaryExpression")?;
                    }
                    self.stream.emit(Instruction::StoreElementRef);
                }
                let call = self.tree_named("MethodCallExpression");
                let expression = self.tree_named("Expression");
                let method_info = self.reflection_named("System.Reflection.MethodInfo");
                let factory = self.emitter.framework_member(
                    EXPRESSION,
                    "Call",
                    false,
                    &call,
                    &[
                        expression.clone(),
                        method_info,
                        SigType::Array(Box::new(expression)),
                    ],
                );
                self.stream.call_effect(Instruction::Call(factory), 3, 1);
                Ok(())
            }
            BoundExpressionKind::Default(ty) => {
                self.push_type(ty)?;
                let default = self.tree_named("DefaultExpression");
                let system_type = self.reflection_named("System.Type");
                let factory = self.emitter.framework_member(
                    EXPRESSION,
                    "Default",
                    false,
                    &default,
                    &[system_type],
                );
                self.stream.call_effect(Instruction::Call(factory), 1, 1);
                Ok(())
            }
            BoundExpressionKind::Conversion {
                operand,
                conversion,
                written,
            } => {
                // A reference converts to what it already is without a node
                // of its own, unless the program wrote the cast (Roslyn's
                // `VisitConversion`): `F(arg)` on an `object` parameter.
                if matches!(conversion, ConversionKind::Identity)
                    || (matches!(conversion, ConversionKind::ImplicitReference) && !*written)
                    || node.ty == operand.ty
                    || node.ty.is_error()
                {
                    return self.emit_tree_node(operand, tree);
                }
                if matches!(conversion, ConversionKind::TupleElements) {
                    return Err(EmitError::new(
                        "a tuple conversion cannot be written in an expression tree yet",
                    ));
                }
                self.emit_tree_node(operand, tree)?;
                self.push_type(&node.ty)?;
                let name = if self.checked && matches!(conversion, ConversionKind::Numeric) {
                    "ConvertChecked"
                } else {
                    "Convert"
                };
                self.unary_type_factory(name, "UnaryExpression")
            }
            BoundExpressionKind::Field { receiver, field } => {
                let receiver_type = receiver.as_ref().map(|receiver| receiver.ty.clone());
                self.emit_tree_receiver(receiver.as_deref(), tree)?;
                let token = self.field_token_on(*field, receiver_type.as_ref())?;
                let declaring = self.declaring_type_of(*field, receiver_type.as_ref());
                self.push_field_info(token, &declaring)?;
                let member = self.tree_named("MemberExpression");
                let expression = self.tree_named("Expression");
                let field_info = self.reflection_named("System.Reflection.FieldInfo");
                let factory = self.emitter.framework_member(
                    EXPRESSION,
                    "Field",
                    false,
                    &member,
                    &[expression, field_info],
                );
                self.stream.call_effect(Instruction::Call(factory), 2, 1);
                Ok(())
            }
            BoundExpressionKind::Property { receiver, property } => {
                let receiver_type = receiver.as_ref().map(|receiver| receiver.ty.clone());
                let declaring = self.declaring_type_of(*property, receiver_type.as_ref());
                self.emit_tree_receiver_as(receiver.as_deref(), &declaring, tree)?;
                let getter =
                    self.emitter
                        .property_accessor(*property, receiver_type.as_ref(), false)?;
                self.push_method_info(getter, &declaring, "System.Reflection.MethodInfo")?;
                let member = self.tree_named("MemberExpression");
                let expression = self.tree_named("Expression");
                let method_info = self.reflection_named("System.Reflection.MethodInfo");
                let factory = self.emitter.framework_member(
                    EXPRESSION,
                    "Property",
                    false,
                    &member,
                    &[expression, method_info],
                );
                self.stream.call_effect(Instruction::Call(factory), 2, 1);
                Ok(())
            }
            BoundExpressionKind::IndexerAccess {
                receiver,
                indexer,
                arguments,
            } => {
                let getter = self
                    .emitter
                    .property_accessor(*indexer, Some(&receiver.ty), false)?;
                let declaring = self.declaring_type_of(*indexer, Some(&receiver.ty));
                self.emit_tree_call(Some(receiver), getter, &declaring, arguments, tree)
            }
            BoundExpressionKind::Call {
                receiver,
                method,
                type_arguments,
                arguments,
                ..
            } => {
                let symbols = self.emitter.compilation.symbols();
                let is_static = symbols
                    .get(*method)
                    .modifiers
                    .contains(rustlyn_semantics::Modifiers::STATIC);
                // A call to an operator the type declared is written as the
                // operator it is, with the method behind it named:
                // `Expression.Add(l, r, op_Addition)`, `Expression.Convert(x,
                // T, op_Implicit)`, as a query provider expects to find it.
                let name = symbols.get(*method).name.clone();
                if is_static
                    && type_arguments.is_empty()
                    && let Some((factory, unary)) = operator_factory(&name, arguments.len())
                {
                    let receiver_type = receiver.as_ref().map(|receiver| receiver.ty.clone());
                    let token = self.method_token_on(*method, receiver_type.as_ref())?;
                    let declaring = self.declaring_type_of(*method, receiver_type.as_ref());
                    for argument in arguments {
                        self.emit_tree_node(argument, tree)?;
                    }
                    let converts = factory == "Convert";
                    // A comparison's factory also asks whether a lifted
                    // comparison gives `null` (it does not in C#).
                    let compares = matches!(
                        factory,
                        "Equal"
                            | "NotEqual"
                            | "LessThan"
                            | "GreaterThan"
                            | "LessThanOrEqual"
                            | "GreaterThanOrEqual"
                    );
                    if converts {
                        self.push_type(&node.ty)?;
                    }
                    if compares {
                        self.stream.emit(Instruction::LoadInt32(0));
                    }
                    self.push_method_info(token, &declaring, "System.Reflection.MethodInfo")?;
                    let expression = self.tree_named("Expression");
                    let method_info = self.reflection_named("System.Reflection.MethodInfo");
                    let system_type = self.reflection_named("System.Type");
                    let (returns, parameters): (SigType, Vec<SigType>) = if converts {
                        (
                            self.tree_named("UnaryExpression"),
                            vec![expression, system_type, method_info],
                        )
                    } else if unary {
                        (
                            self.tree_named("UnaryExpression"),
                            vec![expression, method_info],
                        )
                    } else if compares {
                        (
                            self.tree_named("BinaryExpression"),
                            vec![
                                expression.clone(),
                                expression,
                                SigType::Primitive(ElementType::Boolean),
                                method_info,
                            ],
                        )
                    } else {
                        (
                            self.tree_named("BinaryExpression"),
                            vec![expression.clone(), expression, method_info],
                        )
                    };
                    let made = self.emitter.framework_member(
                        EXPRESSION,
                        factory,
                        false,
                        &returns,
                        &parameters,
                    );
                    self.stream
                        .call_effect(Instruction::Call(made), parameters.len(), 1);
                    return Ok(());
                }
                let receiver_type = receiver.as_ref().map(|receiver| receiver.ty.clone());
                let mut token = self.method_token_on(*method, receiver_type.as_ref())?;
                if !type_arguments.is_empty() {
                    token = self.emitter.method_instantiation(token, type_arguments)?;
                }
                let declaring = self.declaring_type_of(*method, receiver_type.as_ref());
                let instance = if is_static { None } else { receiver.as_deref() };
                self.emit_tree_call(instance, token, &declaring, arguments, tree)
            }
            BoundExpressionKind::ObjectCreation {
                constructor,
                arguments,
                initializers,
            } => {
                match constructor {
                    Some(constructor) => {
                        let token = self.method_token_on(*constructor, Some(&node.ty))?;
                        self.push_method_info(
                            token,
                            &node.ty,
                            "System.Reflection.ConstructorInfo",
                        )?;
                        self.emit_tree_array(arguments, tree)?;
                        let new = self.tree_named("NewExpression");
                        let expression = self.tree_named("Expression");
                        let constructor_info =
                            self.reflection_named("System.Reflection.ConstructorInfo");
                        let factory = self.emitter.framework_member(
                            EXPRESSION,
                            "New",
                            false,
                            &new,
                            &[constructor_info, SigType::Array(Box::new(expression))],
                        );
                        self.stream.call_effect(Instruction::Call(factory), 2, 1);
                    }
                    // `new S()` on a struct with no constructor: a `New` of
                    // the type alone.
                    None => {
                        self.push_type(&node.ty)?;
                        let new = self.tree_named("NewExpression");
                        let system_type = self.reflection_named("System.Type");
                        let factory = self.emitter.framework_member(
                            EXPRESSION,
                            "New",
                            false,
                            &new,
                            &[system_type],
                        );
                        self.stream.call_effect(Instruction::Call(factory), 1, 1);
                    }
                }
                if initializers.is_empty() {
                    return Ok(());
                }
                self.emit_tree_initializers(initializers, tree)
            }
            BoundExpressionKind::TupleCreation(values) => {
                let token = self.emitter.tuple_constructor(&node.ty)?;
                self.push_method_info(token, &node.ty, "System.Reflection.ConstructorInfo")?;
                self.emit_tree_array(values, tree)?;
                let new = self.tree_named("NewExpression");
                let expression = self.tree_named("Expression");
                let constructor_info = self.reflection_named("System.Reflection.ConstructorInfo");
                let factory = self.emitter.framework_member(
                    EXPRESSION,
                    "New",
                    false,
                    &new,
                    &[constructor_info, SigType::Array(Box::new(expression))],
                );
                self.stream.call_effect(Instruction::Call(factory), 2, 1);
                Ok(())
            }
            BoundExpressionKind::ArrayCreation {
                element,
                lengths,
                elements,
            } => {
                self.push_type(element)?;
                let array = self.tree_named("NewArrayExpression");
                let expression = self.tree_named("Expression");
                let system_type = self.reflection_named("System.Type");
                let (name, items) = if lengths.is_empty() || !elements.is_empty() {
                    ("NewArrayInit", elements)
                } else {
                    ("NewArrayBounds", lengths)
                };
                self.emit_tree_array(items, tree)?;
                let factory = self.emitter.framework_member(
                    EXPRESSION,
                    name,
                    false,
                    &array,
                    &[system_type, SigType::Array(Box::new(expression))],
                );
                self.stream.call_effect(Instruction::Call(factory), 2, 1);
                Ok(())
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                if indices.len() != 1 {
                    return Err(EmitError::new(
                        "a multidimensional array access cannot be written in an expression tree yet",
                    ));
                }
                self.emit_tree_node(array, tree)?;
                self.emit_tree_node(&indices[0], tree)?;
                self.binary_factory("ArrayIndex")
            }
            BoundExpressionKind::ArrayLength { array } => {
                self.emit_tree_node(array, tree)?;
                self.unary_factory("ArrayLength")
            }
            BoundExpressionKind::Unary { operator, operand } => {
                self.emit_tree_node(operand, tree)?;
                match operator {
                    UnaryOperator::Plus => Ok(()),
                    UnaryOperator::Minus => self.unary_factory(if self.checked {
                        "NegateChecked"
                    } else {
                        "Negate"
                    }),
                    UnaryOperator::BitwiseNot => self.unary_factory("OnesComplement"),
                    UnaryOperator::LogicalNot => self.unary_factory("Not"),
                }
            }
            BoundExpressionKind::Binary {
                operator,
                left,
                right,
            } => self.emit_tree_binary(*operator, left, right, &node.ty, tree),
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } => {
                // `x || y` on a type that declares `|` and `true` (§12.14.3),
                // which the binder wrote as `T.true(x) ? x : T.|(x, y)`: a
                // tree says `Expression.OrElse(x, y, op_BitwiseOr)`, as
                // Roslyn writes it (and the runtime checks the operators).
                if let Some((factory, left, right, method, owner)) =
                    user_defined_logic(self.emitter.compilation.symbols(), condition, alternative)
                {
                    let owner = owner.cloned();
                    self.emit_tree_node(left, tree)?;
                    self.emit_tree_node(right, tree)?;
                    let token = self.method_token_on(method, owner.as_ref())?;
                    let declaring = self.declaring_type_of(method, owner.as_ref());
                    self.push_method_info(token, &declaring, "System.Reflection.MethodInfo")?;
                    let binary = self.tree_named("BinaryExpression");
                    let expression = self.tree_named("Expression");
                    let method_info = self.reflection_named("System.Reflection.MethodInfo");
                    let made = self.emitter.framework_member(
                        EXPRESSION,
                        factory,
                        false,
                        &binary,
                        &[expression.clone(), expression, method_info],
                    );
                    self.stream.call_effect(Instruction::Call(made), 3, 1);
                    return Ok(());
                }
                self.emit_tree_node(condition, tree)?;
                self.emit_tree_node(consequence, tree)?;
                self.emit_tree_node(alternative, tree)?;
                let conditional = self.tree_named("ConditionalExpression");
                let expression = self.tree_named("Expression");
                let factory = self.emitter.framework_member(
                    EXPRESSION,
                    "Condition",
                    false,
                    &conditional,
                    &[expression.clone(), expression.clone(), expression],
                );
                self.stream.call_effect(Instruction::Call(factory), 3, 1);
                Ok(())
            }
            BoundExpressionKind::TypeTest { operand, target } => {
                self.emit_tree_node(operand, tree)?;
                self.push_type(target)?;
                self.unary_type_factory("TypeIs", "TypeBinaryExpression")
            }
            BoundExpressionKind::TryCast { operand, target } => {
                self.emit_tree_node(operand, tree)?;
                self.push_type(target)?;
                self.unary_type_factory("TypeAs", "UnaryExpression")
            }
            BoundExpressionKind::Lambda(index) => {
                // A lambda inside the tree: described in turn, and quoted
                // where the outer one wanted a tree of it rather than a
                // delegate.
                let quoted = self.is_expression_tree_type(&node.ty);
                let delegate = match &node.ty {
                    Type::Named { type_arguments, .. } if quoted => type_arguments[0].clone(),
                    other => other.clone(),
                };
                self.emit_lambda_tree(*index, &delegate, tree)?;
                if quoted {
                    self.unary_factory("Quote")?;
                }
                Ok(())
            }
            BoundExpressionKind::Sequence(steps) if steps.len() == 1 => {
                self.emit_tree_node(&steps[0], tree)
            }
            // The binder's lifted user-defined operator, `l` and `r` held and
            // tested for values, is the operator on the two as they were:
            // `Expression.Add(l, r, op_Addition)` lifts itself.
            BoundExpressionKind::Sequence(steps) if lifted_operator(steps).is_some() => {
                let Some(call) = lifted_operator(steps) else {
                    unreachable!("the shape was just matched");
                };
                let call = BoundExpression::new(call, node.ty.clone(), node.span);
                self.emit_tree_node(&call, tree)
            }
            other => Err(EmitError::new(format!(
                "cannot write {} in an expression tree yet",
                kind_name(other)
            ))),
        }
    }

    /// The receiver of a member access in a tree: the object's description,
    /// or `null` for a static member.
    fn emit_tree_receiver(
        &mut self,
        receiver: Option<&BoundExpression>,
        tree: &mut Tree,
    ) -> Result<(), EmitError> {
        match receiver {
            Some(receiver) if !matches!(receiver.kind, BoundExpressionKind::TypeExpression(_)) => {
                self.emit_tree_node(receiver, tree)
            }
            _ => {
                self.stream.emit(Instruction::LoadNull);
                Ok(())
            }
        }
    }

    /// The same, for a member `declaring` declares: a `T` that may be a
    /// struct reaches an interface's member through a `Convert` to that
    /// interface, as Roslyn writes it — `Convert(x, IWithIntProperty)
    /// .IntProperty` — where a `T` known to be a class needs none.
    fn emit_tree_receiver_as(
        &mut self,
        receiver: Option<&BoundExpression>,
        declaring: &Type,
        tree: &mut Tree,
    ) -> Result<(), EmitError> {
        self.emit_tree_receiver(receiver, tree)?;
        let symbols = self.emitter.compilation.symbols();
        if let Some(receiver) = receiver
            && matches!(receiver.ty, Type::TypeParameter(_))
            && !receiver.ty.is_reference_type(symbols)
            && declaring.symbol().is_some_and(|symbol| {
                symbols.get(symbol).type_kind() == Some(rustlyn_semantics::TypeKind::Interface)
            })
        {
            self.push_type(declaring)?;
            self.unary_type_factory("Convert", "UnaryExpression")?;
        }
        Ok(())
    }

    /// `Expression.Call(instance, method, arguments)`.
    fn emit_tree_call(
        &mut self,
        instance: Option<&BoundExpression>,
        method: Token,
        declaring: &Type,
        arguments: &[BoundExpression],
        tree: &mut Tree,
    ) -> Result<(), EmitError> {
        self.emit_tree_receiver_as(instance, declaring, tree)?;
        self.push_method_info(method, declaring, "System.Reflection.MethodInfo")?;
        self.emit_tree_array(arguments, tree)?;
        let call = self.tree_named("MethodCallExpression");
        let expression = self.tree_named("Expression");
        let method_info = self.reflection_named("System.Reflection.MethodInfo");
        let factory = self.emitter.framework_member(
            EXPRESSION,
            "Call",
            false,
            &call,
            &[
                expression.clone(),
                method_info,
                SigType::Array(Box::new(expression)),
            ],
        );
        self.stream.call_effect(Instruction::Call(factory), 3, 1);
        Ok(())
    }

    /// A binary operator's node: `Expression.Add(left, right)` and the like,
    /// with `string.Concat` named where `+` joins strings.
    fn emit_tree_binary(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        result: &Type,
        tree: &mut Tree,
    ) -> Result<(), EmitError> {
        let string_special = |emitter: &crate::emitter::Emitter, ty: &Type| {
            emitter.special_type_of(ty) == Some(SpecialType::String)
        };
        if operator == BinaryOperator::Add && string_special(self.emitter, result) {
            // `a + b` on strings is `string.Concat`, which the tree names
            // as the method behind the `+`.
            let string = SigType::Primitive(ElementType::String);
            let object = SigType::Primitive(ElementType::Object);
            let both_strings =
                string_special(self.emitter, &left.ty) && string_special(self.emitter, &right.ty);
            let object_type = self.object_type()?;
            for side in [left, right] {
                self.emit_tree_node(side, tree)?;
                // `Concat(object, object)` takes each side as an object.
                if !both_strings {
                    self.push_type(&object_type)?;
                    self.unary_type_factory("Convert", "UnaryExpression")?;
                }
            }
            let parameter = if both_strings { string.clone() } else { object };
            let concat = self.emitter.framework_member(
                "System.String",
                "Concat",
                false,
                &string,
                &[parameter.clone(), parameter],
            );
            let string_type = self.emitter.compilation.special_type(SpecialType::String);
            let declaring = string_type.map_or(Type::Error, Type::named);
            self.push_method_info(concat, &declaring, "System.Reflection.MethodInfo")?;
            let binary = self.tree_named("BinaryExpression");
            let expression = self.tree_named("Expression");
            let method_info = self.reflection_named("System.Reflection.MethodInfo");
            let factory = self.emitter.framework_member(
                EXPRESSION,
                "Add",
                false,
                &binary,
                &[expression.clone(), expression, method_info],
            );
            self.stream.call_effect(Instruction::Call(factory), 3, 1);
            return Ok(());
        }
        self.emit_tree_node(left, tree)?;
        self.emit_tree_node(right, tree)?;
        let checked = self.checked;
        let name = match operator {
            BinaryOperator::Add if checked => "AddChecked",
            BinaryOperator::Add => "Add",
            BinaryOperator::Subtract if checked => "SubtractChecked",
            BinaryOperator::Subtract => "Subtract",
            BinaryOperator::Multiply if checked => "MultiplyChecked",
            BinaryOperator::Multiply => "Multiply",
            BinaryOperator::Divide => "Divide",
            BinaryOperator::Modulo => "Modulo",
            BinaryOperator::LeftShift => "LeftShift",
            BinaryOperator::RightShift | BinaryOperator::UnsignedRightShift => "RightShift",
            BinaryOperator::BitwiseAnd => "And",
            BinaryOperator::BitwiseOr => "Or",
            BinaryOperator::ExclusiveOr => "ExclusiveOr",
            BinaryOperator::LogicalAnd => "AndAlso",
            BinaryOperator::LogicalOr => "OrElse",
            BinaryOperator::Equality => "Equal",
            BinaryOperator::Inequality => "NotEqual",
            BinaryOperator::LessThan => "LessThan",
            BinaryOperator::GreaterThan => "GreaterThan",
            BinaryOperator::LessThanOrEqual => "LessThanOrEqual",
            BinaryOperator::GreaterThanOrEqual => "GreaterThanOrEqual",
            BinaryOperator::Coalesce => "Coalesce",
        };
        self.binary_factory(name)
    }

    /// The description of a captured variable: the field of the closure
    /// class that holds it, read off that object as a constant.
    fn emit_captured_field(
        &mut self,
        holder: crate::codegen::Holder,
        field: Token,
        node: &BoundExpression,
    ) -> Result<(), EmitError> {
        // A field of a generic closure class is a `MemberRef`, and a handle
        // to it cannot be resolved without the type; the value as it is now
        // has to do there.
        if field.0 >> 24 != 0x04 {
            self.emit_expression(node, true)?;
            self.box_if_needed(&node.ty)?;
            self.push_type(&node.ty)?;
            return self.constant_factory(true);
        }
        self.push_holder_public(holder);
        self.constant_factory(false)?;
        self.stream.emit(Instruction::LoadToken(field));
        let handle = SigType::Named {
            value_type: true,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.RuntimeFieldHandle"),
        };
        let field_info = self.reflection_named("System.Reflection.FieldInfo");
        let from_handle = self.emitter.framework_member(
            "System.Reflection.FieldInfo",
            "GetFieldFromHandle",
            false,
            &field_info,
            &[handle],
        );
        self.stream
            .call_effect(Instruction::Call(from_handle), 1, 1);
        let member = self.tree_named("MemberExpression");
        let expression = self.tree_named("Expression");
        let factory = self.emitter.framework_member(
            EXPRESSION,
            "Field",
            false,
            &member,
            &[expression, field_info],
        );
        self.stream.call_effect(Instruction::Call(factory), 2, 1);
        Ok(())
    }

    /// The initializer of an object whose `NewExpression` is on the stack,
    /// as Roslyn's `VisitObjectCreationContinued` writes it: `{ X = 1 }` is
    /// `Expression.MemberInit(new, bindings)`, each binding a `Bind` of the
    /// field, or of the property's setter, to what it is given; `{ 1, 2 }`
    /// is `Expression.ListInit(new, elements)`, each element an
    /// `ElementInit` of the `Add` it calls with its arguments.
    fn emit_tree_initializers(
        &mut self,
        initializers: &[BoundExpression],
        tree: &mut Tree,
    ) -> Result<(), EmitError> {
        let on_created = |value: &Option<Box<BoundExpression>>| {
            value
                .as_deref()
                .is_some_and(|value| matches!(value.kind, BoundExpressionKind::CreatedObject))
        };
        // An `Add` found as an extension takes the object as an argument,
        // which C# refuses in an expression tree (CS8075).
        let adds = initializers.iter().all(|initializer| {
            matches!(&initializer.kind, BoundExpressionKind::Call { receiver, .. } if on_created(receiver))
        });
        // `A = { X = 1 }` and `A = { 1 }` write into what `A` holds, which
        // `MemberBind` and `ListBind` would describe.
        let binds = initializers.iter().all(|initializer| {
            matches!(&initializer.kind, BoundExpressionKind::Assignment { target, .. }
                if matches!(&target.kind,
                    BoundExpressionKind::Field { receiver, .. }
                    | BoundExpressionKind::Property { receiver, .. } if on_created(receiver)))
        });
        let (element_name, factory_name, made_name) = match (adds, binds) {
            (true, _) => ("ElementInit", "ListInit", "ListInitExpression"),
            (_, true) => ("MemberBinding", "MemberInit", "MemberInitExpression"),
            _ => {
                return Err(EmitError::new(
                    "a nested object or collection initializer cannot be written in an expression tree yet",
                ));
            }
        };
        let element = self.emitter.references.type_ref(
            &mut self.emitter.metadata,
            &format!("System.Linq.Expressions.{element_name}"),
        );
        self.stream
            .emit(Instruction::LoadInt32(initializers.len() as i32));
        self.stream.emit(Instruction::NewArray(element));
        for (position, initializer) in initializers.iter().enumerate() {
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadInt32(position as i32));
            match &initializer.kind {
                BoundExpressionKind::Call {
                    receiver: Some(receiver),
                    method,
                    type_arguments,
                    arguments,
                    ..
                } => {
                    let mut token = self.method_token_on(*method, Some(&receiver.ty))?;
                    if !type_arguments.is_empty() {
                        token = self.emitter.method_instantiation(token, type_arguments)?;
                    }
                    let declaring = self.declaring_type_of(*method, Some(&receiver.ty));
                    self.push_method_info(token, &declaring, "System.Reflection.MethodInfo")?;
                    self.emit_tree_array(arguments, tree)?;
                    let element_init = self.tree_named("ElementInit");
                    let method_info = self.reflection_named("System.Reflection.MethodInfo");
                    let expression = self.tree_named("Expression");
                    let factory = self.emitter.framework_member(
                        EXPRESSION,
                        "ElementInit",
                        false,
                        &element_init,
                        &[method_info, SigType::Array(Box::new(expression))],
                    );
                    self.stream.call_effect(Instruction::Call(factory), 2, 1);
                }
                BoundExpressionKind::Assignment { target, value } => {
                    // A field is bound as the `MemberInfo` it is, a property
                    // through its setter.
                    let member_info = match &target.kind {
                        BoundExpressionKind::Field {
                            field,
                            receiver: Some(receiver),
                        } => {
                            let token = self.field_token_on(*field, Some(&receiver.ty))?;
                            let declaring = self.declaring_type_of(*field, Some(&receiver.ty));
                            self.push_field_info(token, &declaring)?;
                            self.reflection_named("System.Reflection.MemberInfo")
                        }
                        BoundExpressionKind::Property {
                            property,
                            receiver: Some(receiver),
                        } => {
                            let setter = self.emitter.property_accessor(
                                *property,
                                Some(&receiver.ty),
                                true,
                            )?;
                            let declaring = self.declaring_type_of(*property, Some(&receiver.ty));
                            self.push_method_info(
                                setter,
                                &declaring,
                                "System.Reflection.MethodInfo",
                            )?;
                            self.reflection_named("System.Reflection.MethodInfo")
                        }
                        _ => {
                            return Err(EmitError::new(
                                "an initializer of this member cannot be written in an expression tree yet",
                            ));
                        }
                    };
                    self.emit_tree_node(value, tree)?;
                    let assignment = self.tree_named("MemberAssignment");
                    let expression = self.tree_named("Expression");
                    let factory = self.emitter.framework_member(
                        EXPRESSION,
                        "Bind",
                        false,
                        &assignment,
                        &[member_info, expression],
                    );
                    self.stream.call_effect(Instruction::Call(factory), 2, 1);
                }
                _ => {
                    return Err(EmitError::new(
                        "this initializer cannot be written in an expression tree yet",
                    ));
                }
            }
            self.stream.emit(Instruction::StoreElementRef);
        }
        let new = self.tree_named("NewExpression");
        let element_type = self.tree_named(element_name);
        let made = self.tree_named(made_name);
        let factory = self.emitter.framework_member(
            EXPRESSION,
            factory_name,
            false,
            &made,
            &[new, SigType::Array(Box::new(element_type))],
        );
        self.stream.call_effect(Instruction::Call(factory), 2, 1);
        Ok(())
    }

    /// `new Expression[] { ... }` of the descriptions of some expressions.
    fn emit_tree_array(
        &mut self,
        items: &[BoundExpression],
        tree: &mut Tree,
    ) -> Result<(), EmitError> {
        let element = self
            .emitter
            .references
            .type_ref(&mut self.emitter.metadata, EXPRESSION);
        self.stream.emit(Instruction::LoadInt32(items.len() as i32));
        self.stream.emit(Instruction::NewArray(element));
        for (position, item) in items.iter().enumerate() {
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadInt32(position as i32));
            self.emit_tree_node(item, tree)?;
            self.stream.emit(Instruction::StoreElementRef);
        }
        Ok(())
    }

    /// `Expression.Constant(object)` or `Expression.Constant(object, Type)`,
    /// with the value (and the type) already on the stack.
    fn constant_factory(&mut self, typed: bool) -> Result<(), EmitError> {
        let constant = self.tree_named("ConstantExpression");
        let object = SigType::Primitive(ElementType::Object);
        let system_type = self.reflection_named("System.Type");
        let parameters: Vec<SigType> = if typed {
            vec![object, system_type]
        } else {
            vec![object]
        };
        let factory =
            self.emitter
                .framework_member(EXPRESSION, "Constant", false, &constant, &parameters);
        self.stream
            .call_effect(Instruction::Call(factory), parameters.len(), 1);
        Ok(())
    }

    /// A factory taking one `Expression`: `Negate`, `Not`, `Quote`, ...
    fn unary_factory(&mut self, name: &str) -> Result<(), EmitError> {
        let unary = self.tree_named("UnaryExpression");
        let expression = self.tree_named("Expression");
        let factory = self
            .emitter
            .framework_member(EXPRESSION, name, false, &unary, &[expression]);
        self.stream.call_effect(Instruction::Call(factory), 1, 1);
        Ok(())
    }

    /// A factory taking an `Expression` and a `Type`: `Convert`, `TypeIs`,
    /// `TypeAs`.
    fn unary_type_factory(&mut self, name: &str, returns: &str) -> Result<(), EmitError> {
        let result = self.tree_named(returns);
        let expression = self.tree_named("Expression");
        let system_type = self.reflection_named("System.Type");
        let factory = self.emitter.framework_member(
            EXPRESSION,
            name,
            false,
            &result,
            &[expression, system_type],
        );
        self.stream.call_effect(Instruction::Call(factory), 2, 1);
        Ok(())
    }

    /// A factory taking two `Expression`s and giving a `BinaryExpression`.
    fn binary_factory(&mut self, name: &str) -> Result<(), EmitError> {
        let binary = self.tree_named("BinaryExpression");
        let expression = self.tree_named("Expression");
        let factory = self.emitter.framework_member(
            EXPRESSION,
            name,
            false,
            &binary,
            &[expression.clone(), expression],
        );
        self.stream.call_effect(Instruction::Call(factory), 2, 1);
        Ok(())
    }

    /// `typeof(ty)` on the stack: `ldtoken` and `Type.GetTypeFromHandle`.
    fn push_type(&mut self, ty: &Type) -> Result<(), EmitError> {
        let token = self.emitter.type_token(ty)?;
        let handle = SigType::Named {
            value_type: true,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.RuntimeTypeHandle"),
        };
        let system_type = self.reflection_named("System.Type");
        let member = self.emitter.framework_member(
            "System.Type",
            "GetTypeFromHandle",
            false,
            &system_type,
            &[handle],
        );
        self.stream.emit(Instruction::LoadToken(token));
        self.stream.call_effect(Instruction::Call(member), 1, 1);
        Ok(())
    }

    /// A `MethodInfo` (or `ConstructorInfo`) on the stack: `ldtoken` on the
    /// method and on the type declaring it, and
    /// `MethodBase.GetMethodFromHandle(RuntimeMethodHandle,
    /// RuntimeTypeHandle)`, which is the form that resolves a member of a
    /// generic type.
    fn push_method_info(
        &mut self,
        method: Token,
        declaring: &Type,
        wanted: &str,
    ) -> Result<(), EmitError> {
        let type_token = self.emitter.type_token(declaring)?;
        let method_handle = SigType::Named {
            value_type: true,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.RuntimeMethodHandle"),
        };
        let type_handle = SigType::Named {
            value_type: true,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.RuntimeTypeHandle"),
        };
        let method_base = self.reflection_named("System.Reflection.MethodBase");
        let from_handle = self.emitter.framework_member(
            "System.Reflection.MethodBase",
            "GetMethodFromHandle",
            false,
            &method_base,
            &[method_handle, type_handle],
        );
        self.stream.emit(Instruction::LoadToken(method));
        self.stream.emit(Instruction::LoadToken(type_token));
        self.stream
            .call_effect(Instruction::Call(from_handle), 2, 1);
        let wanted_token = self
            .emitter
            .references
            .type_ref(&mut self.emitter.metadata, wanted);
        self.stream.emit(Instruction::CastClass(wanted_token));
        Ok(())
    }

    /// A `FieldInfo` on the stack, the same way.
    fn push_field_info(&mut self, field: Token, declaring: &Type) -> Result<(), EmitError> {
        let type_token = self.emitter.type_token(declaring)?;
        let field_handle = SigType::Named {
            value_type: true,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.RuntimeFieldHandle"),
        };
        let type_handle = SigType::Named {
            value_type: true,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.RuntimeTypeHandle"),
        };
        let field_info = self.reflection_named("System.Reflection.FieldInfo");
        let from_handle = self.emitter.framework_member(
            "System.Reflection.FieldInfo",
            "GetFieldFromHandle",
            false,
            &field_info,
            &[field_handle, type_handle],
        );
        self.stream.emit(Instruction::LoadToken(field));
        self.stream.emit(Instruction::LoadToken(type_token));
        self.stream
            .call_effect(Instruction::Call(from_handle), 2, 1);
        Ok(())
    }

    /// The type a member is declared on, as reflection wants it named: the
    /// construction the receiver reaches it through, or the declaring type
    /// itself.
    fn declaring_type_of(&self, member: SymbolId, receiver: Option<&Type>) -> Type {
        let symbols = self.emitter.compilation.symbols();
        let container = symbols.get(member).container;
        if let Some(through) = self.emitter.through(member, receiver) {
            return through;
        }
        if let Some(receiver) = receiver
            && receiver.symbol().is_some()
            && receiver.symbol() == container
        {
            return receiver.clone();
        }
        match container {
            Some(container) if symbols.get(container).kind == SymbolKind::NamedType => self
                .emitter
                .own_construction(container)
                .filter(|_| receiver.is_none())
                .unwrap_or_else(|| Type::named(container)),
            _ => receiver.cloned().unwrap_or(Type::Error),
        }
    }

    /// `System.Object` as a type.
    fn object_type(&self) -> Result<Type, EmitError> {
        self.emitter
            .compilation
            .special_type(SpecialType::Object)
            .map(Type::named)
            .ok_or_else(|| EmitError::new("the compilation has no `System.Object`"))
    }

    /// A class of `System.Linq.Expressions`, as a signature names it.
    fn tree_named(&mut self, short: &str) -> SigType {
        SigType::Named {
            value_type: false,
            coded: self.emitter.references.type_ref_coded(
                &mut self.emitter.metadata,
                &format!("System.Linq.Expressions.{short}"),
            ),
        }
    }

    /// A class named in full, as a signature names it.
    fn reflection_named(&mut self, qualified: &str) -> SigType {
        SigType::Named {
            value_type: false,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, qualified),
        }
    }
}

/// The one expression a lambda's body is, where it is one: written after
/// the arrow, or the only thing a block returns.
fn tree_body(body: &rustlyn_semantics::BoundStatement) -> Option<BoundExpression> {
    match &body.kind {
        BoundStatementKind::Return(Some(value)) | BoundStatementKind::Expression(value) => {
            Some(value.clone())
        }
        BoundStatementKind::Block(statements) if statements.len() == 1 => tree_body(&statements[0]),
        _ => None,
    }
}

/// `(a = l, b = r, a.HasValue && b.HasValue ? op(a.GetValueOrDefault(),
/// b.GetValueOrDefault()) : default)`, the lifted form of a user-defined
/// binary operator, as the call on `l` and `r` it stands for — the value of a
/// side that is no `T?` is read as it is.
fn lifted_operator(steps: &[BoundExpression]) -> Option<BoundExpressionKind> {
    let [first, second, chosen] = steps else {
        return None;
    };
    let held = |step: &BoundExpression| match &step.kind {
        BoundExpressionKind::Assignment { target, value } => match target.kind {
            BoundExpressionKind::Local(local) => Some((local, (**value).clone())),
            _ => None,
        },
        _ => None,
    };
    let ((left_local, left), (right_local, right)) = (held(first)?, held(second)?);
    let BoundExpressionKind::Conditional { consequence, .. } = &chosen.kind else {
        return None;
    };
    let call = match &consequence.kind {
        BoundExpressionKind::Conversion { operand, .. } => operand,
        _ => consequence,
    };
    let BoundExpressionKind::Call {
        receiver,
        method,
        type_arguments,
        arguments,
        virtual_call,
    } = &call.kind
    else {
        return None;
    };
    let reads = |argument: &BoundExpression, local| match &argument.kind {
        BoundExpressionKind::Local(read) => *read == local,
        BoundExpressionKind::Call {
            receiver: Some(receiver),
            ..
        } => matches!(receiver.kind, BoundExpressionKind::Local(read) if read == local),
        _ => false,
    };
    let [left_value, right_value] = arguments.as_slice() else {
        return None;
    };
    if !reads(left_value, left_local) || !reads(right_value, right_local) {
        return None;
    }
    Some(BoundExpressionKind::Call {
        receiver: receiver.clone(),
        method: *method,
        type_arguments: type_arguments.clone(),
        arguments: vec![left, right],
        virtual_call: *virtual_call,
    })
}

/// The factory that writes a call to a user-defined operator as the
/// operator it is, and whether it takes one operand.
fn operator_factory(name: &str, arity: usize) -> Option<(&'static str, bool)> {
    Some(match (name, arity) {
        ("op_Implicit" | "op_Explicit", 1) => ("Convert", true),
        ("op_UnaryNegation", 1) => ("Negate", true),
        ("op_UnaryPlus", 1) => ("UnaryPlus", true),
        ("op_LogicalNot", 1) => ("Not", true),
        ("op_OnesComplement", 1) => ("OnesComplement", true),
        ("op_Addition", 2) => ("Add", false),
        ("op_Subtraction", 2) => ("Subtract", false),
        ("op_Multiply", 2) => ("Multiply", false),
        ("op_Division", 2) => ("Divide", false),
        ("op_Modulus", 2) => ("Modulo", false),
        ("op_Equality", 2) => ("Equal", false),
        ("op_Inequality", 2) => ("NotEqual", false),
        ("op_LessThan", 2) => ("LessThan", false),
        ("op_GreaterThan", 2) => ("GreaterThan", false),
        ("op_LessThanOrEqual", 2) => ("LessThanOrEqual", false),
        ("op_GreaterThanOrEqual", 2) => ("GreaterThanOrEqual", false),
        ("op_BitwiseAnd", 2) => ("And", false),
        ("op_BitwiseOr", 2) => ("Or", false),
        ("op_ExclusiveOr", 2) => ("ExclusiveOr", false),
        ("op_LeftShift", 2) => ("LeftShift", false),
        ("op_RightShift", 2) => ("RightShift", false),
        _ => return None,
    })
}

/// What kind of thing a node is, for saying it has no place in a tree.
fn kind_name(kind: &BoundExpressionKind) -> &'static str {
    match kind {
        BoundExpressionKind::Assignment { .. }
        | BoundExpressionKind::CompoundAssignment { .. }
        | BoundExpressionKind::Increment { .. } => "an assignment",
        BoundExpressionKind::Await { .. } => "an `await`",
        BoundExpressionKind::ConditionalAccess { .. } => "a `?.` access",
        BoundExpressionKind::InterpolatedString(_) => "an interpolated string",
        BoundExpressionKind::IsPattern { .. } | BoundExpressionKind::Switch { .. } => "a pattern",
        BoundExpressionKind::Throw(_) => "a `throw`",
        BoundExpressionKind::MethodGroup { .. } | BoundExpressionKind::DelegateCreation { .. } => {
            "a method group"
        }
        _ => "this expression",
    }
}

/// `T.true(x) ? x : T.|(x, y)`, the binder's `x || y` on a type that
/// declares the operators, as the factory a tree writes it with, its two
/// operands and the `|` (or `false` and `&`, for `&&`). `x` is either the
/// operand itself or a local it was put in first, and the test may take it
/// converted, to the `T?` a `true(T?)` takes. The type the `|` is called
/// on comes last: `C<T>` for a generic one.
#[allow(clippy::type_complexity)]
fn user_defined_logic<'e>(
    symbols: &rustlyn_semantics::Symbols,
    condition: &'e BoundExpression,
    alternative: &'e BoundExpression,
) -> Option<(
    &'static str,
    &'e BoundExpression,
    &'e BoundExpression,
    SymbolId,
    Option<&'e Type>,
)> {
    let unwrapped = |mut value: &'e BoundExpression| {
        while let BoundExpressionKind::Conversion { operand, .. } = &value.kind {
            value = operand;
        }
        value
    };
    let BoundExpressionKind::Call {
        method: test,
        arguments: tested,
        ..
    } = &unwrapped(condition).kind
    else {
        return None;
    };
    let (factory, combine) = match symbols.get(*test).name.as_str() {
        "op_True" => ("OrElse", "op_BitwiseOr"),
        "op_False" => ("AndAlso", "op_BitwiseAnd"),
        _ => return None,
    };
    let [tested] = &tested[..] else {
        return None;
    };
    let left = match &unwrapped(tested).kind {
        BoundExpressionKind::Assignment { target, value }
            if matches!(target.kind, BoundExpressionKind::Local(_)) =>
        {
            value.as_ref()
        }
        _ => unwrapped(tested),
    };
    // The `&` itself, or the binder's lifted one: `(l = x, r = y,
    // l.HasValue && r.HasValue ? T.&(l.Value, r.Value) : default)`, whose
    // right operand is what `r` is given.
    let (receiver, method, right) = match &alternative.kind {
        BoundExpressionKind::Call {
            receiver,
            method,
            arguments,
            ..
        } => match &arguments[..] {
            [_, right] => (receiver, *method, right),
            _ => return None,
        },
        BoundExpressionKind::Sequence(steps) => {
            let [_, given, chosen] = &steps[..] else {
                return None;
            };
            let BoundExpressionKind::Assignment { value: right, .. } = &given.kind else {
                return None;
            };
            let BoundExpressionKind::Conditional { consequence, .. } = &chosen.kind else {
                return None;
            };
            let BoundExpressionKind::Call {
                receiver, method, ..
            } = &unwrapped(consequence).kind
            else {
                return None;
            };
            (receiver, *method, right.as_ref())
        }
        _ => return None,
    };
    if symbols.get(method).name != combine {
        return None;
    }
    let owner = receiver.as_ref().map(|receiver| &receiver.ty);
    Some((factory, left, right, method, owner))
}
