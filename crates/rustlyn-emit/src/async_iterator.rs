//! The members an `async` iterator's machine has beyond an `async` method's.
//!
//! An `async` iterator (C# 8) is one machine doing two jobs. Its body runs
//! under `MoveNext` like any `async` method's, driven by an
//! `AsyncIteratorMethodBuilder`; and the machine is also the
//! `IAsyncEnumerator<T>` that asks for the body to run. `MoveNextAsync`
//! resumes it and hands out a `ValueTask<bool>` over the machine's promise, a
//! `ManualResetValueTaskSourceCore<bool>`, which the body sets `true` at a
//! `yield return` and `false` at its end; `DisposeAsync` resumes it in
//! dispose mode, to leave through the `finally`s it stopped inside. The
//! machine answers `IValueTaskSource<bool>` and `IValueTaskSource` itself, by
//! handing each question on to the promise.
//!
//! The shape is Roslyn's (`AsyncIteratorRewriter`), states and all: `-3`
//! before a walk, `-2` done, `-1` running, `0` and up waiting on an `await`,
//! `-4` and down stopped at a `yield return`.

use rustlyn_semantics::{Modifiers, SpecialType, SymbolId, SymbolKind, Type, TypeKind};

use crate::async_machine::{AsyncIteratorPlan, AsyncPlan, ITERATOR_START};
use crate::codegen::BodyEmitter;
use crate::emitter::{
    EmitError, Emitter, MachineKey, MethodSource, ParameterPlan, PromiseCall, TypePlan,
};
use crate::il::{Instruction, Token};
use crate::metadata::method_attributes;
use crate::signature::{
    ElementType, SigType, generic_method_signature, method_signature, type_def_or_ref,
};

/// A method of the machine, as `plan_async` makes the row for it: where its
/// body comes from, its name, its flags, what it returns and takes.
pub(crate) type PlannedMethod = (MethodSource, String, u16, Type, Vec<ParameterPlan>);

const MANUAL_RESET: &str = "System.Threading.Tasks.Sources.ManualResetValueTaskSourceCore`1";
const VALUE_TASK_SOURCE: &str = "System.Threading.Tasks.Sources.IValueTaskSource";
const VALUE_TASK_SOURCE_OF: &str = "System.Threading.Tasks.Sources.IValueTaskSource`1";
const SOURCE_STATUS: &str = "System.Threading.Tasks.Sources.ValueTaskSourceStatus";
const COMPLETED_FLAGS: &str = "System.Threading.Tasks.Sources.ValueTaskSourceOnCompletedFlags";
const CANCELLATION_TOKEN: &str = "System.Threading.CancellationToken";
const TOKEN_SOURCE: &str = "System.Threading.CancellationTokenSource";

/// The `MethodDefOrRef` coded index of §II.24.2.6: tag 0 is a `MethodDef` and
/// tag 1 a `MemberRef`.
fn method_def_or_ref(tag: u32, token: Token) -> u32 {
    ((token.0 & 0x00FF_FFFF) << 1) | tag
}

impl Emitter<'_> {
    /// A framework type by its metadata name, constructed over `arguments`.
    pub(crate) fn framework_type(
        &self,
        name: &str,
        arguments: Vec<Type>,
    ) -> Result<Type, EmitError> {
        let symbol = self
            .compilation
            .type_by_metadata_name(name)
            .ok_or_else(|| {
                EmitError::new(format!(
                    "an `async` iterator needs `{name}`, which nothing referenced defines"
                ))
            })?;
        Ok(Type::Named {
            symbol,
            type_arguments: arguments,
        })
    }

    fn special_named(&self, which: SpecialType) -> Result<Type, EmitError> {
        self.compilation
            .special_type(which)
            .map(Type::named)
            .ok_or_else(|| EmitError::new(format!("the compilation has no `{which:?}`")))
    }

    /// Whether a value of the type holds a reference the collector follows
    /// (Roslyn's `IsManagedType`): a class, an interface, an array, a type
    /// parameter, or a struct with a field that does. A primitive, an enum,
    /// a pointer, and a struct of nothing but those hold none.
    pub(crate) fn holds_references(&self, ty: &Type) -> bool {
        self.holds_references_at(ty, 0)
    }

    fn holds_references_at(&self, ty: &Type, depth: usize) -> bool {
        if depth > 16 {
            return true;
        }
        let symbols = self.compilation.symbols();
        match ty {
            Type::Pointer(_) | Type::FunctionPointer(_) => false,
            // `where T : unmanaged` is written like a type and is the one
            // constraint that says a `T` holds none.
            Type::TypeParameter(parameter) => !symbols
                .get(*parameter)
                .as_type_parameter()
                .is_some_and(|detail| {
                    detail.unmanaged
                        || detail.constraints.iter().any(|constraint| {
                            self.binder
                                .node_at(constraint.0.tree, constraint.0.span)
                                .is_some_and(|node| node.text().trim() == "unmanaged")
                        })
                }),
            Type::Tuple(elements) => elements
                .iter()
                .any(|element| self.holds_references_at(&element.ty, depth + 1)),
            Type::Named {
                symbol,
                type_arguments,
            } => match symbols.get(*symbol).type_kind() {
                Some(TypeKind::Enum) => false,
                Some(TypeKind::Struct | TypeKind::RecordStruct) => {
                    // A primitive holds its value in a field of its own type.
                    if self.special_type_of(ty).is_some() {
                        return false;
                    }
                    let substitution: std::collections::HashMap<SymbolId, Type> = symbols
                        .get(*symbol)
                        .as_named_type()
                        .map(|detail| {
                            detail
                                .type_parameters
                                .iter()
                                .copied()
                                .zip(type_arguments.iter().cloned())
                                .collect()
                        })
                        .unwrap_or_default();
                    symbols.get(*symbol).members.iter().any(|member| {
                        let field = symbols.get(*member);
                        field.kind == SymbolKind::Field
                            && !field.modifiers.contains(Modifiers::STATIC)
                            && !field.modifiers.contains(Modifiers::CONST)
                            && self.holds_references_at(
                                &self.type_of(*member).substitute(&substitution),
                                depth + 1,
                            )
                    })
                }
                _ => true,
            },
            _ => true,
        }
    }

    /// `ManualResetValueTaskSourceCore<bool>`, the machine's promise.
    pub(crate) fn promise_type(&self) -> Result<Type, EmitError> {
        let boolean = self.special_named(SpecialType::Boolean)?;
        self.framework_type(MANUAL_RESET, vec![boolean])
    }

    /// The methods an `async` iterator's machine implements its interfaces
    /// with, beyond `MoveNext` and `SetStateMachine`.
    ///
    /// Each is public and virtual, and implements the interface member of its
    /// name and signature without a `MethodImpl` row — one `GetStatus` and
    /// one `OnCompleted` answer both `IValueTaskSource`s — except the
    /// untyped `GetResult`, whose name the typed one already has.
    pub(crate) fn async_iterator_methods(
        &self,
        key: MachineKey,
        iterator: &AsyncIteratorPlan,
    ) -> Result<Vec<PlannedMethod>, EmitError> {
        let sealed_virtual = method_attributes::PUBLIC
            | method_attributes::HIDE_BY_SIG
            | method_attributes::VIRTUAL
            | method_attributes::NEW_SLOT
            | method_attributes::FINAL;
        let explicit = method_attributes::PRIVATE
            | method_attributes::HIDE_BY_SIG
            | method_attributes::VIRTUAL
            | method_attributes::NEW_SLOT
            | method_attributes::FINAL;
        let boolean = self.special_named(SpecialType::Boolean)?;
        let short = self.special_named(SpecialType::Int16)?;
        let object = self.special_named(SpecialType::Object)?;
        let parameter = |name: &str, ty: Type| ParameterPlan {
            symbol: None,
            name: name.to_string(),
            ty,
            by_ref: false,
        };
        let token = || parameter("token", short.clone());
        let mut methods = Vec::new();
        if iterator.enumerable {
            methods.push((
                MethodSource::AsyncIteratorGetEnumerator(key),
                "GetAsyncEnumerator".to_string(),
                sealed_virtual,
                self.framework_type(
                    "System.Collections.Generic.IAsyncEnumerator`1",
                    vec![iterator.element.clone()],
                )?,
                vec![parameter(
                    "token",
                    self.framework_type(CANCELLATION_TOKEN, Vec::new())?,
                )],
            ));
        }
        methods.push((
            MethodSource::AsyncIteratorMoveNext(key),
            "MoveNextAsync".to_string(),
            sealed_virtual,
            self.framework_type("System.Threading.Tasks.ValueTask`1", vec![boolean.clone()])?,
            Vec::new(),
        ));
        methods.push((
            MethodSource::AsyncIteratorCurrent(key),
            "get_Current".to_string(),
            sealed_virtual | method_attributes::SPECIAL_NAME,
            iterator.element.clone(),
            Vec::new(),
        ));
        methods.push((
            MethodSource::AsyncIteratorPromise(key, PromiseCall::GetResult),
            "GetResult".to_string(),
            sealed_virtual,
            boolean,
            vec![token()],
        ));
        methods.push((
            MethodSource::AsyncIteratorPromise(key, PromiseCall::GetStatus),
            "GetStatus".to_string(),
            sealed_virtual,
            self.framework_type(SOURCE_STATUS, Vec::new())?,
            vec![token()],
        ));
        methods.push((
            MethodSource::AsyncIteratorPromise(key, PromiseCall::OnCompleted),
            "OnCompleted".to_string(),
            sealed_virtual,
            Type::Void,
            vec![
                parameter(
                    "continuation",
                    self.framework_type("System.Action`1", vec![object.clone()])?,
                ),
                parameter("state", object),
                token(),
                parameter("flags", self.framework_type(COMPLETED_FLAGS, Vec::new())?),
            ],
        ));
        methods.push((
            MethodSource::AsyncIteratorPromise(key, PromiseCall::GetResultVoid),
            "System.Threading.Tasks.Sources.IValueTaskSource.GetResult".to_string(),
            explicit,
            Type::Void,
            vec![token()],
        ));
        methods.push((
            MethodSource::AsyncIteratorDispose(key),
            "DisposeAsync".to_string(),
            sealed_virtual,
            self.framework_type("System.Threading.Tasks.ValueTask", Vec::new())?,
            Vec::new(),
        ));
        Ok(methods)
    }

    /// The interfaces an `async` iterator's machine implements beside
    /// `IAsyncStateMachine`, and the `MethodImpl` of the one method written
    /// under an interface's name. What `T` is has to be said with the
    /// machine's own parameters, which the caller has made current.
    pub(crate) fn write_async_iterator_interfaces(
        &mut self,
        plan: &TypePlan,
        key: MachineKey,
        iterator: &AsyncIteratorPlan,
    ) -> Result<(), EmitError> {
        let boolean = self.special_named(SpecialType::Boolean)?;
        let mut constructed = vec![
            self.framework_type(
                "System.Collections.Generic.IAsyncEnumerator`1",
                vec![iterator.element.clone()],
            )?,
            self.framework_type(VALUE_TASK_SOURCE_OF, vec![boolean])?,
        ];
        if iterator.enumerable {
            constructed.insert(
                0,
                self.framework_type(
                    "System.Collections.Generic.IAsyncEnumerable`1",
                    vec![iterator.element.clone()],
                )?,
            );
        }
        let mut interfaces = Vec::new();
        for interface in &constructed {
            let mut blob = Vec::new();
            self.sig_type(interface)?.write(&mut blob);
            let spec = self.references.type_spec(&mut self.metadata, &blob);
            // A `TypeDefOrRef` tagged 2 is a `TypeSpec`.
            interfaces.push(type_def_or_ref(2, spec.0 & 0x00FF_FFFF));
        }
        interfaces.push(
            self.references
                .type_ref_coded(&mut self.metadata, "System.IAsyncDisposable"),
        );
        interfaces.push(
            self.references
                .type_ref_coded(&mut self.metadata, VALUE_TASK_SOURCE),
        );
        for interface in interfaces {
            self.metadata.add_interface_impl(plan.token, interface);
        }
        let untyped = plan.methods.iter().find(|method| {
            matches!(
                method.source,
                MethodSource::AsyncIteratorPromise(of, PromiseCall::GetResultVoid) if of == key
            )
        });
        if let Some(untyped) = untyped {
            let declaration = self.references.member_ref(
                &mut self.metadata,
                VALUE_TASK_SOURCE,
                "GetResult",
                &method_signature(
                    true,
                    &SigType::Primitive(ElementType::Void),
                    &[SigType::Primitive(ElementType::I2)],
                ),
            );
            self.metadata.add_method_impl(
                plan.token,
                method_def_or_ref(0, untyped.token),
                method_def_or_ref(1, declaration),
            );
        }
        Ok(())
    }

    /// A member of the promise, `ManualResetValueTaskSourceCore<bool>`, by
    /// the definition's signature.
    fn promise_member(
        &mut self,
        name: &str,
        returns: &SigType,
        parameters: &[SigType],
    ) -> Result<Token, EmitError> {
        let promise = self.promise_type()?;
        self.member_of_type(&promise, name, &method_signature(true, returns, parameters))
    }

    /// `ValueTaskSourceStatus` or `ValueTaskSourceOnCompletedFlags`, which
    /// signatures name as the value types they are.
    fn framework_enum(&mut self, name: &str) -> SigType {
        SigType::Named {
            value_type: true,
            coded: self.references.type_ref_coded(&mut self.metadata, name),
        }
    }

    /// `ValueTask<bool>` or `ValueTask`'s constructor from a source and its
    /// version: what `MoveNextAsync` and `DisposeAsync` hand out while the
    /// body has not answered yet.
    fn value_task_constructor(&mut self, typed: bool) -> Result<Token, EmitError> {
        let short = SigType::Primitive(ElementType::I2);
        let void = SigType::Primitive(ElementType::Void);
        if typed {
            let boolean = self.special_named(SpecialType::Boolean)?;
            let task = self.framework_type("System.Threading.Tasks.ValueTask`1", vec![boolean])?;
            let source = SigType::Constructed {
                value_type: false,
                coded: self
                    .references
                    .type_ref_coded(&mut self.metadata, VALUE_TASK_SOURCE_OF),
                arguments: vec![SigType::TypeParameter(0)],
            };
            self.member_of_type(
                &task,
                ".ctor",
                &method_signature(true, &void, &[source, short]),
            )
        } else {
            let source = SigType::Named {
                value_type: false,
                coded: self
                    .references
                    .type_ref_coded(&mut self.metadata, VALUE_TASK_SOURCE),
            };
            Ok(self.framework_member(
                "System.Threading.Tasks.ValueTask",
                ".ctor",
                true,
                &void,
                &[source, short],
            ))
        }
    }
}

impl BodyEmitter<'_, '_> {
    fn async_iterator_plan(
        &self,
        key: MachineKey,
    ) -> Result<(AsyncPlan, AsyncIteratorPlan), EmitError> {
        let plan = self
            .emitter
            .asyncs
            .get(&key)
            .cloned()
            .ok_or_else(|| EmitError::new("a state machine with no plan"))?;
        let iterator = plan
            .iterator
            .clone()
            .ok_or_else(|| EmitError::new("an `async` iterator's member on another machine"))?;
        Ok((plan, iterator))
    }

    /// The field an `async` iterator's dispose mode is hoisted into.
    fn dispose_mode_field(
        plan: &AsyncPlan,
        iterator: &AsyncIteratorPlan,
    ) -> Result<Token, EmitError> {
        plan.locals
            .get(&iterator.dispose_mode)
            .copied()
            .ok_or_else(|| EmitError::new("an `async` iterator's dispose mode has no field"))
    }

    /// `this.<>t__builder = AsyncIteratorMethodBuilder.Create();`
    fn create_iterator_builder(&mut self, plan: &AsyncPlan) -> Result<(), EmitError> {
        let builder_self = self.emitter.builder_self_sig(&plan.kind);
        let create = self.emitter.builder_member(
            plan,
            "Create",
            &method_signature(false, &builder_self, &[]),
        )?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.call_effect(Instruction::Call(create), 0, 1);
        self.stream.emit(Instruction::StoreField(plan.builder));
        Ok(())
    }

    /// `Environment.CurrentManagedThreadId`, on the stack.
    fn push_thread_id(&mut self) {
        let thread = self.emitter.framework_member(
            "System.Environment",
            "get_CurrentManagedThreadId",
            false,
            &SigType::Primitive(ElementType::I4),
            &[],
        );
        self.stream.call_effect(Instruction::Call(thread), 0, 1);
    }

    /// `.ctor(int state)`: the state it starts in, a builder of its own, and
    /// the thread that made it, which lets that thread's first walk of an
    /// enumerable be the machine itself.
    pub(crate) fn emit_async_iterator_constructor(
        &mut self,
        key: MachineKey,
    ) -> Result<(), EmitError> {
        let (plan, iterator) = self.async_iterator_plan(key)?;
        let object = self.emitter.framework_member(
            "System.Object",
            ".ctor",
            true,
            &SigType::Primitive(ElementType::Void),
            &[],
        );
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.call_effect(Instruction::Call(object), 1, 0);
        self.create_iterator_builder(&plan)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadArgument(1));
        self.stream.emit(Instruction::StoreField(plan.state));
        if let Some(thread) = iterator.thread {
            self.stream.emit(Instruction::LoadArgument(0));
            self.push_thread_id();
            self.stream.emit(Instruction::StoreField(thread));
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// The method the source wrote: make the machine, fill it with what the
    /// method was called with, and hand it back. An enumerable is made
    /// finished (`-2`), for `GetAsyncEnumerator` to start, and keeps the
    /// arguments in copies of its own that each walk starts from; an
    /// enumerator is ready to walk (`-3`) and keeps them where the body
    /// reads them.
    pub(crate) fn emit_async_iterator_start(&mut self, plan: &AsyncPlan) -> Result<(), EmitError> {
        let Some(iterator) = &plan.iterator else {
            return Err(EmitError::new("an `async` iterator with no plan"));
        };
        let state = if iterator.enumerable {
            -2
        } else {
            ITERATOR_START
        };
        self.stream.emit(Instruction::LoadInt32(state));
        self.stream
            .call_effect(Instruction::NewObject(plan.outer_constructor), 1, 1);
        if let Some(field) = plan.outer_this {
            self.stream.emit(Instruction::Dup);
            self.push_this_value()?;
            self.stream.emit(Instruction::StoreField(field));
        }
        let filled = if iterator.enumerable {
            &iterator.outer_proxies
        } else {
            &plan.outer_order
        };
        for (parameter, field) in filled.clone() {
            let index = self.argument_index(parameter)?;
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadArgument(index));
            self.stream.emit(Instruction::StoreField(field));
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `GetAsyncEnumerator(CancellationToken token)`.
    ///
    /// The first walk on the thread that made the enumerable is the machine
    /// itself, set back to the start; any other gets a fresh machine. Either
    /// way the parameters the body reads start from the copies the method
    /// was called with — except an `[EnumeratorCancellation]` token, which
    /// is the one given here, the one the method was given, or the two
    /// linked, whichever says anything.
    pub(crate) fn emit_async_iterator_get_enumerator(
        &mut self,
        key: MachineKey,
    ) -> Result<(), EmitError> {
        let (plan, iterator) = self.async_iterator_plan(key)?;
        let dispose_mode = Self::dispose_mode_field(&plan, &iterator)?;
        let result = self.locals.len() as u16;
        self.locals.push(plan.inner_sig.clone());
        self.local_types.push(Type::Error);
        let fresh = self.stream.label();
        let ready = self.stream.label();
        // if (state == -2 && initialThreadId == CurrentManagedThreadId)
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(plan.state));
        self.stream.emit(Instruction::LoadInt32(-2));
        self.stream.emit(Instruction::CompareEqual);
        self.stream.emit(Instruction::BranchIfFalse(fresh));
        if let Some(thread) = iterator.thread {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(thread));
            self.push_thread_id();
            self.stream.emit(Instruction::CompareEqual);
            self.stream.emit(Instruction::BranchIfFalse(fresh));
        }
        // { state = -3; builder = Create(); disposeMode = false; result = this; }
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(ITERATOR_START));
        self.stream.emit(Instruction::StoreField(plan.state));
        self.create_iterator_builder(&plan)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(0));
        self.stream.emit(Instruction::StoreField(dispose_mode));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::StoreLocal(result));
        self.stream.emit(Instruction::Branch(ready));
        // else { result = new D(-3); result.<>4__this = this.<>4__this; }
        self.stream.mark(fresh);
        self.stream.emit(Instruction::LoadInt32(ITERATOR_START));
        self.stream
            .call_effect(Instruction::NewObject(plan.constructor), 1, 1);
        self.stream.emit(Instruction::StoreLocal(result));
        if let Some(field) = plan.this {
            self.stream.emit(Instruction::LoadLocal(result));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(field));
            self.stream.emit(Instruction::StoreField(field));
        }
        self.stream.mark(ready);
        for (parameter, proxy) in iterator.proxies.clone() {
            let Some(working) = plan.parameters.get(&parameter).copied() else {
                continue;
            };
            if iterator.cancellation == Some(parameter) {
                let combined = iterator.combined.ok_or_else(|| {
                    EmitError::new("an `[EnumeratorCancellation]` token with nothing to link it")
                })?;
                self.emit_token_combination(result, proxy, working, combined)?;
                continue;
            }
            self.stream.emit(Instruction::LoadLocal(result));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(proxy));
            self.stream.emit(Instruction::StoreField(working));
        }
        self.stream.emit(Instruction::LoadLocal(result));
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// The `[EnumeratorCancellation]` parameter of a fresh walk, as Roslyn's
    /// `InitializeParameterField` works it out from the token the method was
    /// called with (`proxy`) and the one `GetAsyncEnumerator` was given
    /// (argument 1):
    ///
    /// ```text
    /// if (this.proxy.Equals(default)) result.token = token;
    /// else if (token.Equals(this.proxy) || token.Equals(default)) result.token = this.proxy;
    /// else {
    ///     result.combined = CancellationTokenSource.CreateLinkedTokenSource(this.proxy, token);
    ///     result.token = result.combined.Token;
    /// }
    /// ```
    fn emit_token_combination(
        &mut self,
        result: u16,
        proxy: Token,
        working: Token,
        combined: Token,
    ) -> Result<(), EmitError> {
        let token_type = self
            .emitter
            .framework_type(CANCELLATION_TOKEN, Vec::new())?;
        let token_sig = self.emitter.sig_type(&token_type)?;
        let source_sig = SigType::Named {
            value_type: false,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, TOKEN_SOURCE),
        };
        let equals = self.emitter.framework_member(
            CANCELLATION_TOKEN,
            "Equals",
            true,
            &SigType::Primitive(ElementType::Boolean),
            std::slice::from_ref(&token_sig),
        );
        let link = self.emitter.framework_member(
            TOKEN_SOURCE,
            "CreateLinkedTokenSource",
            false,
            &source_sig,
            &[token_sig.clone(), token_sig.clone()],
        );
        let get_token =
            self.emitter
                .framework_member(TOKEN_SOURCE, "get_Token", true, &token_sig, &[]);
        let token_token = self.emitter.type_token(&token_type)?;
        let default = self.temporary(&token_type)?;
        let push_default = |this: &mut Self| {
            this.stream.emit(Instruction::LoadLocalAddress(default));
            this.stream.emit(Instruction::InitObject(token_token));
            this.stream.emit(Instruction::LoadLocal(default));
        };
        let other = self.stream.label();
        let linked = self.stream.label();
        let from_method = self.stream.label();
        let end = self.stream.label();
        // if (this.proxy.Equals(default)) result.token = token;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadFieldAddress(proxy));
        push_default(self);
        self.stream.call_effect(Instruction::Call(equals), 2, 1);
        self.stream.emit(Instruction::BranchIfFalse(other));
        self.stream.emit(Instruction::LoadLocal(result));
        self.stream.emit(Instruction::LoadArgument(1));
        self.stream.emit(Instruction::StoreField(working));
        self.stream.emit(Instruction::Branch(end));
        // else if (token.Equals(this.proxy) || token.Equals(default))
        self.stream.mark(other);
        self.stream.emit(Instruction::LoadArgumentAddress(1));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(proxy));
        self.stream.call_effect(Instruction::Call(equals), 2, 1);
        self.stream.emit(Instruction::BranchIfTrue(from_method));
        self.stream.emit(Instruction::LoadArgumentAddress(1));
        push_default(self);
        self.stream.call_effect(Instruction::Call(equals), 2, 1);
        self.stream.emit(Instruction::BranchIfFalse(linked));
        //     result.token = this.proxy;
        self.stream.mark(from_method);
        self.stream.emit(Instruction::LoadLocal(result));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(proxy));
        self.stream.emit(Instruction::StoreField(working));
        self.stream.emit(Instruction::Branch(end));
        // else { result.combined = Link(this.proxy, token); result.token = result.combined.Token; }
        self.stream.mark(linked);
        self.stream.emit(Instruction::LoadLocal(result));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(proxy));
        self.stream.emit(Instruction::LoadArgument(1));
        self.stream.call_effect(Instruction::Call(link), 2, 1);
        self.stream.emit(Instruction::StoreField(combined));
        self.stream.emit(Instruction::LoadLocal(result));
        self.stream.emit(Instruction::LoadLocal(result));
        self.stream.emit(Instruction::LoadField(combined));
        self.stream
            .call_effect(Instruction::CallVirtual(get_token), 1, 1);
        self.stream.emit(Instruction::StoreField(working));
        self.stream.mark(end);
        Ok(())
    }

    /// `promise.Reset(); var inst = this; builder.MoveNext(ref inst);` —
    /// runs the body on this thread until it yields, ends or waits. The
    /// iterator builder's `MoveNext` is what the others call `Start`.
    fn start_iterator_body(&mut self, plan: &AsyncPlan) -> Result<(), EmitError> {
        let Some(promise) = plan.iterator.as_ref().map(|iterator| iterator.promise) else {
            return Err(EmitError::new("an `async` iterator with no plan"));
        };
        let void = SigType::Primitive(ElementType::Void);
        let reset = self.emitter.promise_member("Reset", &void, &[])?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadFieldAddress(promise));
        self.stream.call_effect(Instruction::Call(reset), 1, 0);
        let instance = self.locals.len() as u16;
        self.locals.push(plan.inner_sig.clone());
        self.local_types.push(Type::Error);
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::StoreLocal(instance));
        let start = self.emitter.builder_member(
            plan,
            "MoveNext",
            &generic_method_signature(
                true,
                1,
                &void,
                &[SigType::ByRef(Box::new(SigType::MethodTypeParameter(0)))],
            ),
        )?;
        let start = self
            .emitter
            .spec_of(start, std::slice::from_ref(&plan.inner_sig));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(plan.builder));
        self.stream.emit(Instruction::LoadLocalAddress(instance));
        self.stream.call_effect(Instruction::Call(start), 2, 0);
        Ok(())
    }

    /// `this.promise.Version`, on the stack.
    fn push_promise_version(&mut self, promise: Token) -> Result<(), EmitError> {
        let get_version = self.emitter.promise_member(
            "get_Version",
            &SigType::Primitive(ElementType::I2),
            &[],
        )?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadFieldAddress(promise));
        self.stream
            .call_effect(Instruction::Call(get_version), 1, 1);
        Ok(())
    }

    /// `return default;` for a value type: a `ValueTask` or a
    /// `ValueTask<bool>` that is already done.
    fn return_default(&mut self, ty: &Type) -> Result<(), EmitError> {
        let slot = self.temporary(ty)?;
        let token = self.emitter.type_token(ty)?;
        self.stream.emit(Instruction::LoadLocalAddress(slot));
        self.stream.emit(Instruction::InitObject(token));
        self.stream.emit(Instruction::LoadLocal(slot));
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `MoveNextAsync()`: nothing more once the walk is done; otherwise run
    /// the body to its next `yield return` or its end, and hand out the
    /// answer where it already has one, or a `ValueTask<bool>` over the
    /// promise where it went off to wait.
    pub(crate) fn emit_async_iterator_move_next(
        &mut self,
        key: MachineKey,
    ) -> Result<(), EmitError> {
        let (plan, iterator) = self.async_iterator_plan(key)?;
        let boolean = self
            .emitter
            .compilation
            .special_type(SpecialType::Boolean)
            .map(Type::named)
            .ok_or_else(|| EmitError::new("the compilation has no `System.Boolean`"))?;
        let task = self
            .emitter
            .framework_type("System.Threading.Tasks.ValueTask`1", vec![boolean])?;
        let running = self.stream.label();
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(plan.state));
        self.stream.emit(Instruction::LoadInt32(-2));
        self.stream.emit(Instruction::CompareEqual);
        self.stream.emit(Instruction::BranchIfFalse(running));
        self.return_default(&task)?;
        self.stream.mark(running);
        self.start_iterator_body(&plan)?;
        let short = self
            .emitter
            .compilation
            .special_type(SpecialType::Int16)
            .map(Type::named)
            .ok_or_else(|| EmitError::new("the compilation has no `System.Int16`"))?;
        let version = self.temporary(&short)?;
        self.push_promise_version(iterator.promise)?;
        self.stream.emit(Instruction::StoreLocal(version));
        let short_sig = SigType::Primitive(ElementType::I2);
        let status = self.emitter.framework_enum(SOURCE_STATUS);
        let get_status =
            self.emitter
                .promise_member("GetStatus", &status, std::slice::from_ref(&short_sig))?;
        let get_result = self.emitter.promise_member(
            "GetResult",
            &SigType::TypeParameter(0),
            std::slice::from_ref(&short_sig),
        )?;
        let from_value = self.emitter.member_of_type(
            &task,
            ".ctor",
            &method_signature(
                true,
                &SigType::Primitive(ElementType::Void),
                &[SigType::TypeParameter(0)],
            ),
        )?;
        let from_source = self.emitter.value_task_constructor(true)?;
        // if (promise.GetStatus(version) == ValueTaskSourceStatus.Succeeded)
        //     return new ValueTask<bool>(promise.GetResult(version));
        let waiting = self.stream.label();
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(iterator.promise));
        self.stream.emit(Instruction::LoadLocal(version));
        self.stream.call_effect(Instruction::Call(get_status), 2, 1);
        self.stream.emit(Instruction::LoadInt32(1));
        self.stream.emit(Instruction::CompareEqual);
        self.stream.emit(Instruction::BranchIfFalse(waiting));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(iterator.promise));
        self.stream.emit(Instruction::LoadLocal(version));
        self.stream.call_effect(Instruction::Call(get_result), 2, 1);
        self.stream
            .call_effect(Instruction::NewObject(from_value), 1, 1);
        self.stream.emit(Instruction::Ret);
        // return new ValueTask<bool>(this, version);
        self.stream.mark(waiting);
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadLocal(version));
        self.stream
            .call_effect(Instruction::NewObject(from_source), 2, 1);
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `Current`: what the last `yield return` gave.
    pub(crate) fn emit_async_iterator_current(&mut self, key: MachineKey) -> Result<(), EmitError> {
        let (_, iterator) = self.async_iterator_plan(key)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(iterator.current));
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// A member of `IValueTaskSource<bool>` or `IValueTaskSource`, handed on
    /// to the promise with the arguments it was given.
    pub(crate) fn emit_promise_call(
        &mut self,
        key: MachineKey,
        call: PromiseCall,
    ) -> Result<(), EmitError> {
        let (_, iterator) = self.async_iterator_plan(key)?;
        let short = SigType::Primitive(ElementType::I2);
        let void = SigType::Primitive(ElementType::Void);
        let (name, returns, parameters) = match call {
            PromiseCall::GetResult | PromiseCall::GetResultVoid => {
                ("GetResult", SigType::TypeParameter(0), vec![short])
            }
            PromiseCall::GetStatus => (
                "GetStatus",
                self.emitter.framework_enum(SOURCE_STATUS),
                vec![short],
            ),
            PromiseCall::OnCompleted => {
                let action = SigType::Constructed {
                    value_type: false,
                    coded: self
                        .emitter
                        .references
                        .type_ref_coded(&mut self.emitter.metadata, "System.Action`1"),
                    arguments: vec![SigType::Primitive(ElementType::Object)],
                };
                let flags = self.emitter.framework_enum(COMPLETED_FLAGS);
                (
                    "OnCompleted",
                    void.clone(),
                    vec![
                        action,
                        SigType::Primitive(ElementType::Object),
                        short,
                        flags,
                    ],
                )
            }
        };
        let gives = !matches!(returns, SigType::Primitive(ElementType::Void));
        let arguments = parameters.len();
        let member = self.emitter.promise_member(name, &returns, &parameters)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(iterator.promise));
        for argument in 1..=arguments {
            self.stream.emit(Instruction::LoadArgument(argument as u16));
        }
        self.stream
            .call_effect(Instruction::Call(member), arguments + 1, usize::from(gives));
        if gives && call == PromiseCall::GetResultVoid {
            self.stream.emit(Instruction::Pop);
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `DisposeAsync()`: never while the body runs or waits on an `await`
    /// (the state is then `-1` or more), nothing once it is done, and
    /// otherwise the body resumed in dispose mode, to leave through the
    /// `finally`s it stopped inside.
    pub(crate) fn emit_async_iterator_dispose(&mut self, key: MachineKey) -> Result<(), EmitError> {
        let (plan, iterator) = self.async_iterator_plan(key)?;
        let dispose_mode = Self::dispose_mode_field(&plan, &iterator)?;
        let task = self
            .emitter
            .framework_type("System.Threading.Tasks.ValueTask", Vec::new())?;
        // if (state >= -1) throw new NotSupportedException();
        let allowed = self.stream.label();
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(plan.state));
        self.stream.emit(Instruction::LoadInt32(-1));
        self.stream.emit(Instruction::CompareLess);
        self.stream.emit(Instruction::BranchIfTrue(allowed));
        let unsupported = self.emitter.framework_member(
            "System.NotSupportedException",
            ".ctor",
            true,
            &SigType::Primitive(ElementType::Void),
            &[],
        );
        self.stream
            .call_effect(Instruction::NewObject(unsupported), 0, 1);
        self.stream.emit(Instruction::Throw);
        // if (state == -2) return default;
        self.stream.mark(allowed);
        let running = self.stream.label();
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(plan.state));
        self.stream.emit(Instruction::LoadInt32(-2));
        self.stream.emit(Instruction::CompareEqual);
        self.stream.emit(Instruction::BranchIfFalse(running));
        self.return_default(&task)?;
        self.stream.mark(running);
        // disposeMode = true; ...; return new ValueTask(this, promise.Version);
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(1));
        self.stream.emit(Instruction::StoreField(dispose_mode));
        self.start_iterator_body(&plan)?;
        let from_source = self.emitter.value_task_constructor(false)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.push_promise_version(iterator.promise)?;
        self.stream
            .call_effect(Instruction::NewObject(from_source), 2, 1);
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `yield return e;` in an `async` iterator: the value goes to
    /// `Current`, the state says which `yield return` the body stopped at,
    /// and the `try` around the body is left for the `true` outside it. The
    /// `finally`s on the way are skipped, since the state is not `-1`;
    /// resumed, the body is running again.
    pub(crate) fn emit_async_yield_return(
        &mut self,
        value: &rustlyn_semantics::BoundExpression,
    ) -> Result<(), EmitError> {
        let (current, yielded) = match &self.async_run {
            Some(run) => match (&run.plan.iterator, run.yielded) {
                (Some(iterator), Some(yielded)) => (iterator.current, yielded),
                _ => {
                    return Err(EmitError::new(
                        "`yield return` in an `async` method that is no iterator",
                    ));
                }
            },
            None => return Err(EmitError::new("`yield return` outside its machine")),
        };
        let (state, resume) = self.next_suspension()?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.emit_expression(value, true)?;
        self.stream.emit(Instruction::StoreField(current));
        self.set_machine_state(state);
        self.emit_jump(yielded, 0);
        self.stream.mark(resume);
        self.set_machine_state(-1);
        Ok(())
    }

    /// `current = default;` before an `await` in an `async` iterator whose
    /// element holds references, as Roslyn clears it (`MakeAwaitPreamble`):
    /// a walk waiting on something keeps nothing alive it already handed
    /// out.
    pub(crate) fn clear_current_before_await(&mut self) -> Result<(), EmitError> {
        let Some(iterator) = self
            .async_run
            .as_ref()
            .and_then(|run| run.plan.iterator.clone())
        else {
            return Ok(());
        };
        if !self.emitter.holds_references(&iterator.element) {
            return Ok(());
        }
        let token = self.emitter.type_token(&iterator.element)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(iterator.current));
        self.stream.emit(Instruction::InitObject(token));
        Ok(())
    }

    /// The end of an `async` iterator's walk, normal or not: finished (`-2`),
    /// the combined tokens disposed, `Current` cleared and the builder
    /// told; the promise says `false` or the exception — which the caller
    /// sets after this.
    pub(crate) fn finish_async_iterator(&mut self, plan: &AsyncPlan) -> Result<(), EmitError> {
        let Some(iterator) = &plan.iterator else {
            return Ok(());
        };
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(-2));
        self.stream.emit(Instruction::StoreField(plan.state));
        // if (combinedTokens != null) { combinedTokens.Dispose(); combinedTokens = null; }
        if let Some(combined) = iterator.combined {
            let kept = self.stream.label();
            let dispose = self.emitter.framework_member(
                TOKEN_SOURCE,
                "Dispose",
                true,
                &SigType::Primitive(ElementType::Void),
                &[],
            );
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(combined));
            self.stream.emit(Instruction::BranchIfFalse(kept));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(combined));
            self.stream
                .call_effect(Instruction::CallVirtual(dispose), 1, 0);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadNull);
            self.stream.emit(Instruction::StoreField(combined));
            self.stream.mark(kept);
        }
        let element = self.emitter.type_token(&iterator.element)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(iterator.current));
        self.stream.emit(Instruction::InitObject(element));
        let complete = self.emitter.builder_member(
            plan,
            "Complete",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &[]),
        )?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(plan.builder));
        self.stream.call_effect(Instruction::Call(complete), 1, 0);
        Ok(())
    }

    /// `promise.SetResult(answer);`.
    pub(crate) fn settle_promise(
        &mut self,
        plan: &AsyncPlan,
        answer: bool,
    ) -> Result<(), EmitError> {
        let Some(iterator) = &plan.iterator else {
            return Ok(());
        };
        let set_result = self.emitter.promise_member(
            "SetResult",
            &SigType::Primitive(ElementType::Void),
            &[SigType::TypeParameter(0)],
        )?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(iterator.promise));
        self.stream.emit(Instruction::LoadInt32(i32::from(answer)));
        self.stream.call_effect(Instruction::Call(set_result), 2, 0);
        Ok(())
    }

    /// `promise.SetException(e);` with the exception in `slot`.
    pub(crate) fn fail_promise(&mut self, plan: &AsyncPlan, slot: u16) -> Result<(), EmitError> {
        let Some(iterator) = &plan.iterator else {
            return Ok(());
        };
        let exception = self
            .emitter
            .compilation
            .type_by_metadata_name("System.Exception")
            .map(Type::named)
            .ok_or_else(|| EmitError::new("the compilation has no `System.Exception`"))?;
        let exception = self.emitter.sig_type(&exception)?;
        let set_exception = self.emitter.promise_member(
            "SetException",
            &SigType::Primitive(ElementType::Void),
            &[exception],
        )?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(iterator.promise));
        self.stream.emit(Instruction::LoadLocal(slot));
        self.stream
            .call_effect(Instruction::Call(set_exception), 2, 0);
        Ok(())
    }
}
