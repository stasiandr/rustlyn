//! The state machine a method with a `yield` in it becomes.
//!
//! The CLI has no iterators: what C# calls one is a class the compiler writes,
//! holding the method's arguments, its locals and how far through the body it
//! got. The method itself is left making one of those and handing it back
//! (§15.15), and everything the source wrote moves into `MoveNext`.

use std::collections::{HashMap, HashSet};

use rustlyn_semantics::{BoundExpression, BoundExpressionKind, LocalId, Modifiers, SymbolId, Type};

use crate::codegen::BodyEmitter;
use crate::il::{Instruction, Label};

use crate::emitter::{
    DisplayView, EmitError, Emitter, FieldPlan, MachineKey, MethodPlan, MethodSource,
    ParameterPlan, TypePlan,
};
use crate::il::Token;
use crate::metadata::table;
use crate::metadata::{field_attributes, method_attributes, type_attributes};
use crate::signature::{ElementType, SigType, method_signature, type_def_or_ref};

/// Where everything the state machine holds ended up.
#[derive(Clone, Debug)]
pub(crate) struct IteratorPlan {
    /// How the class is named in a signature. Nested in a generic type it is
    /// generic itself — it holds values of those parameters — so it is named
    /// as a construction and its members are `MemberRef`s under that.
    pub(crate) sig: SigType,
    /// Whether the method making the machine is a member of a display class
    /// or another machine: `<>4__this` is then that object, and what the
    /// body calls `this` is reached through it.
    pub(crate) hosted: bool,
    pub(crate) element: Type,
    /// Whether the method said `IEnumerable`, which decides the state a fresh
    /// machine starts in and whether `GetEnumerator` may hand back itself.
    pub(crate) enumerable: bool,
    pub(crate) constructor: Token,
    pub(crate) state: Token,
    pub(crate) current: Token,
    pub(crate) thread: Token,
    /// Set by `Dispose`: the walk is resumed only to leave the regions it
    /// stopped in, so that their `finally`s run.
    pub(crate) disposing: Token,
    pub(crate) move_next: Token,
    pub(crate) dispose: Token,
    pub(crate) this: Option<Token>,
    /// Every `yield return`, in the order `MoveNext` reaches them, with the
    /// protected regions around each, and how many regions there are.
    pub(crate) sites: Vec<crate::async_machine::AwaitSite>,
    pub(crate) regions: usize,
    pub(crate) parameters: HashMap<SymbolId, Token>,
    pub(crate) locals: HashMap<LocalId, Token>,
    /// The hoisted locals no closure reads, of types that might hold
    /// references: cleared where their scope ends, so that the machine keeps
    /// nothing alive it will not read again, and all of them by `Dispose`.
    pub(crate) cleared: Vec<(LocalId, Type)>,
    /// The parameters as the walk reads them, in the order they were
    /// declared.
    pub(crate) order: Vec<(SymbolId, Token)>,
    /// For a machine an `IEnumerable` makes, the parameters as the method
    /// was called with them (`<>3__p`), in the same order: what each walk
    /// starts from.
    pub(crate) initial: Vec<(SymbolId, Token)>,
    pub(crate) get_enumerator: Token,
    /// The few members the method that makes a machine reaches, as it reaches
    /// them: `MemberRef`s under the construction it named, where the machine
    /// is generic. Everything else is reached from inside, where a definition
    /// resolves against whatever it was constructed with.
    pub(crate) outer_constructor: Token,
    pub(crate) outer_this: Option<Token>,
    pub(crate) outer_order: Vec<(SymbolId, Token)>,
}

impl Emitter<'_> {
    /// Whether a member's body is an iterator this machine is for, and what
    /// it hands out. An `async` one is an `async` machine's (see
    /// [`AsyncKind::Iterator`](crate::async_machine::AsyncKind::Iterator)).
    pub(crate) fn iterated_element(&mut self, key: MachineKey) -> Option<Type> {
        if self.is_async_closure(key) {
            return None;
        }
        self.yielded_element(key)
    }

    /// What a body's `yield return`s hand out, where it has any: the element
    /// of an iterator, `async` or not.
    pub(crate) fn yielded_element(&mut self, key: MachineKey) -> Option<Type> {
        let body = self.body_of(key.owner())?;
        match key {
            MachineKey::Member(_) => body.iterator.clone(),
            // A lambda may not `yield` (§12.19.1); a local function may.
            MachineKey::Lambda { .. } => None,
            MachineKey::Function { index, .. } => body.local_functions.get(index)?.iterator.clone(),
        }
    }

    /// Why an iterator cannot be built for this member, where it cannot.
    ///
    /// Everything left out here is left out of the whole method: the body is
    /// stubbed, and the reason says which piece is missing rather than
    /// pretending the method works.
    pub(crate) fn iterator_refusal(&mut self, key: MachineKey) -> Option<String> {
        let body = self.machine_body(key)?;
        if self
            .iterated_element(key)
            .is_some_and(|element| element.is_error())
        {
            return Some(
                "an iterator has to be declared returning `IEnumerable<T>`, `IEnumerator<T>` \
                 or one of their untyped forms"
                    .to_string(),
            );
        }
        let parameters = self.machine_parameters(key);
        let by_reference = parameters
            .iter()
            .any(|parameter| self.is_by_reference(Some(*parameter)));
        if by_reference {
            return Some(
                "an iterator cannot take a parameter by reference: the machine holds it in a \
                 field, and a field may not be one"
                    .to_string(),
            );
        }
        let locals = self.machine_locals(key, &body);
        if locals.iter().any(|(_, local)| local.by_ref) {
            return Some(
                "an iterator whose body declares a `ref` local needs it in a field, and a \
                 field may not be a reference"
                    .to_string(),
            );
        }
        // Everything the machine will hold in a field, which a `ref struct`
        // may never be: the arguments, the locals, what it hands out, and the
        // `this` it was called on.
        let mut held: Vec<Type> = parameters
            .iter()
            .map(|parameter| self.type_of(*parameter))
            .collect();
        held.extend(locals.iter().map(|(_, local)| local.ty.clone()));
        held.extend(self.iterated_element(key));
        let host = self.host_of(key);
        if host.instance
            && host.hosted.is_none()
            && let Some(container) = self.compilation.symbols().get(key.owner()).container
        {
            held.push(self.binder.self_type(container));
        }
        if held.iter().any(|ty| self.is_ref_like(ty)) {
            return Some(
                "an iterator that would hold a `ref struct` cannot be built: a field may \
                 never be one"
                    .to_string(),
            );
        }
        None
    }

    /// Whether a type may never be a field of an ordinary class.
    ///
    /// `Span<T>` and everything else the runtime marks `IsByRefLike` may hold
    /// a reference into the stack, so it lives only where the stack does. A
    /// pointer is a number to the runtime, and a field holds it as well as a
    /// local: an `async` method hoists one as Roslyn does.
    pub(crate) fn is_ref_like(&self, ty: &Type) -> bool {
        let Some(symbol) = ty.symbol() else {
            return matches!(ty, Type::ByRef(_));
        };
        let symbols = self.compilation.symbols();
        symbols.get(symbol).modifiers.contains(Modifiers::REF)
            || symbols
                .get(symbol)
                .as_named_type()
                .is_some_and(|detail| detail.ref_like)
    }

    /// Whether a value of a type might hold a reference the collector
    /// follows, and so is worth clearing once nothing will read it (Roslyn
    /// 4.11's `MightContainReferences`, which `csc` 8.0 is): a reference or
    /// a type parameter might; a struct the language builds in (an `int`, a
    /// `decimal`, a `DateTime`) does not; any other struct from an assembly
    /// might, since a reference assembly does not say what its private
    /// fields are — `int?` and `(int, int)` among them; a struct of this
    /// compilation might where one of its fields might.
    pub(crate) fn might_hold_references(&self, ty: &Type, depth: usize) -> bool {
        if depth > 8 {
            return true;
        }
        let symbols = self.compilation.symbols();
        match ty {
            Type::Array { .. } | Type::Dynamic | Type::Null | Type::Tuple(_) => true,
            // A `T : unmanaged` holds no reference whatever it is.
            Type::TypeParameter(parameter) => !symbols
                .get(*parameter)
                .as_type_parameter()
                .is_some_and(|detail| detail.unmanaged),
            Type::Named { symbol, .. } => {
                let declared = symbols.get(*symbol);
                match declared.type_kind() {
                    Some(rustlyn_semantics::TypeKind::Enum) => false,
                    Some(kind) if kind.is_reference_type() => true,
                    _ => {
                        let name = symbols.qualified_name(*symbol);
                        if rustlyn_semantics::SpecialType::ALL
                            .iter()
                            .any(|special| self.compilation.special_type(*special) == Some(*symbol))
                            || BUILT_IN_STRUCTS.contains(&name.as_str())
                        {
                            return false;
                        }
                        if name == "System.TypedReference"
                            || self.compilation.is_from_metadata(*symbol)
                        {
                            return true;
                        }
                        let substitution = self.binder.type_substitution(ty);
                        declared.members.iter().any(|member| {
                            let member = symbols.get(*member);
                            member.kind == rustlyn_semantics::SymbolKind::Field
                                && !member.modifiers.contains(Modifiers::STATIC)
                                && !member.modifiers.contains(Modifiers::CONST)
                                && self.might_hold_references(
                                    &self.type_of(member.id).substitute(&substitution),
                                    depth + 1,
                                )
                        })
                    }
                }
            }
            Type::Pointer(_)
            | Type::FunctionPointer(_)
            | Type::ByRef(_)
            | Type::Void
            | Type::Error => false,
        }
    }

    /// Plans the class a member's `yield`s turn it into.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn plan_iterator(
        &mut self,
        key: MachineKey,
        enclosing: SymbolId,
        element: Type,
        next_type: &mut u32,
        next_field: &mut u32,
        next_method: &mut u32,
    ) -> Result<Option<TypePlan>, EmitError> {
        let owner = key.owner();
        let Some(body) = self.machine_body(key) else {
            return Ok(None);
        };
        let host = self.host_of(key);
        let instance = host.instance;
        let declared = self.machine_return(key);
        let enumerable = matches!(&declared, Type::Named { symbol, .. }
            if self.compilation.symbols().get(*symbol).name == "IEnumerable");

        let token = Token::new(table::TYPE_DEF, *next_type);
        *next_type += 1;

        // Nested in `C<T>` the machine carries `T` the way any nested type
        // does: the arguments and locals it holds are of those types.
        let inherited = self
            .compilation
            .symbols()
            .get(enclosing)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        // A machine for `Twice<T>(T value)` holds a `T` of the method's own,
        // so it declares that parameter after whatever the type gave it.
        // A local function's machine declares the function's own after them.
        let (own, class_level) =
            self.machine_own_generics(key, inherited.len(), host.hosted.is_some());
        let coded = type_def_or_ref(0, token.0 & 0x00FF_FFFF);
        // A closure hosted in a display class or a machine names the
        // method's parameters as that class's own, `!n`, since the class
        // declares them.
        let sig = if inherited.is_empty() && own.is_empty() {
            SigType::Named {
                value_type: false,
                coded,
            }
        } else if host.hosted.is_some() {
            SigType::Constructed {
                value_type: false,
                coded,
                arguments: (0..class_level as u32)
                    .map(SigType::TypeParameter)
                    .chain(
                        (0..(inherited.len() + own.len() - class_level) as u32)
                            .map(SigType::MethodTypeParameter),
                    )
                    .collect(),
            }
        } else {
            SigType::Constructed {
                value_type: false,
                coded,
                arguments: (0..inherited.len() as u32)
                    .map(SigType::TypeParameter)
                    .collect(),
            }
        };

        // Everything below is written as the machine names it — its own
        // parameters, `!0` — because that is what its rows say. The
        // construction above is the one exception: that is how the method
        // making one names it, and it was built before this was set.
        let mut declared = inherited.clone();
        declared.extend(own.iter().copied());
        self.display_generics = declared;

        let integer = Type::named(
            self.compilation
                .special_type(rustlyn_semantics::SpecialType::Int32)
                .ok_or_else(|| EmitError::new("the compilation has no `System.Int32`"))?,
        );
        let mut fields = Vec::new();
        // What only the machine's own methods touch is private, as Roslyn
        // makes it; what the method making a machine fills, and what a
        // closure's class may read, is public.
        let mut field = |fields: &mut Vec<FieldPlan>,
                         name: String,
                         ty: Type,
                         sig: Option<SigType>,
                         flags: u16| {
            let token = Token::new(table::FIELD, *next_field);
            *next_field += 1;
            fields.push(FieldPlan {
                token,
                name,
                ty,
                flags,
                symbol: None,
                constant: None,
                sig,
            });
            token
        };
        let private = field_attributes::PRIVATE;
        let public = field_attributes::PUBLIC;
        let state = field(
            &mut fields,
            "<>1__state".to_string(),
            integer.clone(),
            None,
            private,
        );
        let current = field(
            &mut fields,
            "<>2__current".to_string(),
            element.clone(),
            None,
            private,
        );
        let thread = field(
            &mut fields,
            "<>l__initialThreadId".to_string(),
            integer,
            None,
            private,
        );
        let boolean_type = Type::named(
            self.compilation
                .special_type(rustlyn_semantics::SpecialType::Boolean)
                .ok_or_else(|| EmitError::new("the compilation has no `System.Boolean`"))?,
        );
        let disposing = field(
            &mut fields,
            "<>w__disposing".to_string(),
            boolean_type,
            None,
            private,
        );
        let (sites, regions) = crate::async_machine::collect_sites(
            &body.statements,
            &crate::async_machine::yields_directly,
        );
        // `this` is the enclosing type's for a member; for a closure hosted
        // in a display class or a machine it is that object, which only a
        // signature names.
        let this = instance.then(|| match &host.hosted {
            Some(sig) => field(
                &mut fields,
                "<>4__this".to_string(),
                Type::Error,
                Some(sig.clone()),
                public,
            ),
            None => field(
                &mut fields,
                "<>4__this".to_string(),
                self.binder.self_type(enclosing),
                None,
                public,
            ),
        });

        // What a closure of the body reads lives here for it: the machine is
        // its display class.
        let captured: HashSet<LocalId> = body
            .lambdas
            .iter()
            .flat_map(|lambda| lambda.captured.iter().copied())
            .chain(
                body.local_functions
                    .iter()
                    .flat_map(|function| function.captured.iter().copied()),
            )
            .collect();
        let captured_parameters: HashSet<SymbolId> = body
            .lambdas
            .iter()
            .flat_map(|lambda| lambda.captured_parameters.iter().copied())
            .chain(
                body.local_functions
                    .iter()
                    .flat_map(|function| function.captured_parameters.iter().copied()),
            )
            .collect();
        // Each parameter is what the walk reads, `p`. A machine an
        // `IEnumerable` makes keeps what it was called with as well,
        // `<>3__p`, which the method making it fills and `GetEnumerator`
        // copies into `p` for each walk, so that one walk's changes are not
        // the next one's start.
        let declared_parameters = self.machine_parameters(key);
        let mut parameters = HashMap::new();
        let mut order = Vec::new();
        let mut initial = Vec::new();
        for parameter in &declared_parameters {
            let name = self.compilation.symbols().get(*parameter).name.clone();
            let ty = self.type_of(*parameter);
            let visibility = if enumerable && !captured_parameters.contains(parameter) {
                private
            } else {
                public
            };
            let token = field(&mut fields, name.clone(), ty.clone(), None, visibility);
            parameters.insert(*parameter, token);
            order.push((*parameter, token));
            if enumerable {
                let token = field(&mut fields, format!("<>3__{name}"), ty, None, public);
                initial.push((*parameter, token));
            }
        }
        // The locals that outlast a `yield`, in the fields Roslyn would put
        // them in (see `hoisting`).
        let candidates = self.machine_locals(key, &body);
        let taken: HashSet<String> = fields.iter().map(|field| field.name.clone()).collect();
        let hoisted = crate::hoisting::hoist(
            &body,
            &body.statements,
            &candidates,
            &captured,
            self.compilation.options().optimize,
            true,
            &taken,
        );
        let mut tokens = Vec::with_capacity(hoisted.fields.len());
        for (at, (name, ty)) in hoisted.fields.iter().enumerate() {
            let shared = hoisted
                .field_of
                .iter()
                .any(|(local, field)| *field == at && captured.contains(local));
            let visibility = if shared { public } else { private };
            tokens.push(field(
                &mut fields,
                name.clone(),
                ty.clone(),
                None,
                visibility,
            ));
        }
        let mut held_locals: Vec<(LocalId, String, Type)> = hoisted
            .field_of
            .iter()
            .map(|(local, at)| {
                let (name, ty) = &hoisted.fields[*at];
                (*local, name.clone(), ty.clone())
            })
            .collect();
        held_locals.sort_by_key(|(local, _, _)| local.0);
        let locals: HashMap<LocalId, Token> = hoisted
            .field_of
            .iter()
            .map(|(local, at)| (*local, tokens[*at]))
            .collect();
        // What is cleared as its scope ends: a hoisted local no closure
        // reads, of a type that might hold references.
        let mut cleared: Vec<(LocalId, Type)> = held_locals
            .iter()
            .filter(|(local, _, ty)| !captured.contains(local) && self.might_hold_references(ty, 0))
            .map(|(local, _, ty)| (*local, ty.clone()))
            .collect();
        cleared.sort_by_key(|(local, _)| local.0);

        let mut methods = Vec::new();
        let mut method = |methods: &mut Vec<MethodPlan>,
                          source: MethodSource,
                          name: &str,
                          flags: u16,
                          returns: Type,
                          parameters: Vec<ParameterPlan>,
                          signature: Vec<u8>| {
            let token = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            methods.push(MethodPlan {
                source,
                token,
                name: name.to_string(),
                flags,
                instance: true,
                return_type: returns,
                parameters,
                type_parameters: Vec::new(),
                impl_flags: 0,
                signature: Some(signature),
            });
            token
        };
        let void = SigType::Primitive(ElementType::Void);
        let boolean = SigType::Primitive(ElementType::Boolean);
        let object = SigType::Primitive(ElementType::Object);
        let integer_sig = SigType::Primitive(ElementType::I4);
        // The element is not written yet, and cannot be: a machine is planned
        // while the type holding it is, and a type declared further down the
        // file has no `TypeDef` token until the planning pass reaches it.
        // Naming it now would write `IEnumerator<MetadataReference>` with a
        // `TypeRef` into the framework, which no framework assembly answers
        // to. `restate_iterator_signatures` writes these again once every
        // type has a token; everything below only reserves the room.
        let element_sig = SigType::Primitive(ElementType::Object);
        let enumerator_of = SigType::Constructed {
            value_type: false,
            coded: self.references.type_ref_coded(
                &mut self.metadata,
                "System.Collections.Generic.IEnumerator`1",
            ),
            arguments: vec![element_sig.clone()],
        };
        let enumerator = SigType::Named {
            value_type: false,
            coded: self
                .references
                .type_ref_coded(&mut self.metadata, "System.Collections.IEnumerator"),
        };

        // A public virtual method whose name and signature match an interface
        // member implements it without a `MethodImpl` row; the two `Current`s
        // and the two `GetEnumerator`s collide, and those are written out.
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

        let constructor = method(
            &mut methods,
            MethodSource::IteratorConstructor(key),
            ".ctor",
            method_attributes::PUBLIC
                | method_attributes::HIDE_BY_SIG
                | method_attributes::SPECIAL_NAME
                | method_attributes::RT_SPECIAL_NAME,
            Type::Void,
            vec![ParameterPlan {
                symbol: None,
                name: "state".to_string(),
                ty: Type::Error,
                by_ref: false,
            }],
            method_signature(true, &void, &[integer_sig]),
        );
        let move_next = method(
            &mut methods,
            MethodSource::IteratorMoveNext(key),
            "MoveNext",
            sealed_virtual,
            Type::Error,
            Vec::new(),
            method_signature(true, &boolean, &[]),
        );
        method(
            &mut methods,
            MethodSource::IteratorCurrent(key, false),
            "get_Current",
            sealed_virtual | method_attributes::SPECIAL_NAME,
            element.clone(),
            Vec::new(),
            method_signature(true, &element_sig, &[]),
        );
        let untyped_current = method(
            &mut methods,
            MethodSource::IteratorCurrent(key, true),
            "System.Collections.IEnumerator.get_Current",
            explicit | method_attributes::SPECIAL_NAME,
            Type::Error,
            Vec::new(),
            method_signature(true, &object, &[]),
        );
        let dispose = method(
            &mut methods,
            MethodSource::IteratorDispose(key),
            "Dispose",
            sealed_virtual,
            Type::Void,
            Vec::new(),
            method_signature(true, &void, &[]),
        );
        method(
            &mut methods,
            MethodSource::IteratorReset,
            "Reset",
            sealed_virtual,
            Type::Void,
            Vec::new(),
            method_signature(true, &void, &[]),
        );
        let get_enumerator = method(
            &mut methods,
            MethodSource::IteratorGetEnumerator(key, false),
            "GetEnumerator",
            sealed_virtual,
            Type::Error,
            Vec::new(),
            method_signature(true, &enumerator_of, &[]),
        );
        let untyped_get_enumerator = method(
            &mut methods,
            MethodSource::IteratorGetEnumerator(key, true),
            "System.Collections.IEnumerable.GetEnumerator",
            explicit,
            Type::Error,
            Vec::new(),
            method_signature(true, &enumerator, &[]),
        );

        self.iterators.insert(
            key,
            IteratorPlan {
                sig,
                hosted: host.hosted.is_some(),
                element: element.clone(),
                enumerable,
                constructor,
                state,
                current,
                thread,
                disposing,
                move_next,
                dispose,
                this,
                sites,
                regions,
                parameters: parameters.clone(),
                locals: locals.clone(),
                cleared,
                order: order.clone(),
                initial: initial.clone(),
                get_enumerator,
                outer_constructor: constructor,
                outer_this: this,
                // The method making the machine fills what it was called
                // with: `<>3__p` where there is one.
                outer_order: if enumerable { initial } else { order },
            },
        );
        if !inherited.is_empty() || !own.is_empty() {
            let held =
                (instance && host.hosted.is_none()).then(|| self.binder.self_type(enclosing));
            let named: Vec<(SymbolId, String, Type)> = declared_parameters
                .iter()
                .map(|parameter| {
                    (
                        *parameter,
                        self.compilation.symbols().get(*parameter).name.clone(),
                        self.type_of(*parameter),
                    )
                })
                .collect();
            let initial = if enumerable {
                named
                    .iter()
                    .map(|(parameter, name, ty)| (*parameter, format!("<>3__{name}"), ty.clone()))
                    .collect()
            } else {
                Vec::new()
            };
            self.iterator_pending.push(PendingIterator {
                key,
                token,
                arity: inherited.len(),
                own: own.len(),
                element: element.clone(),
                this: held,
                this_sig: instance.then(|| host.hosted.clone()).flatten(),
                class_level,
                order: named,
                initial,
                locals: held_locals,
            });
        }
        self.iterator_impls.push(IteratorImpls {
            token,
            element_sig,
            enumerator_of,
            enumerator,
            untyped_current,
            untyped_get_enumerator,
            enumerable,
        });
        self.display_generics = Vec::new();
        let mut plan = TypePlan {
            symbol: enclosing,
            token,
            fields,
            methods,
            properties: Vec::new(),
            display: None,
            iterator: Some(owner),
            machine: Some(key),
            nested: None,
        };
        // The lambdas of the body are methods of the machine, which is the
        // display class for them.
        let inner_sig = if inherited.is_empty() && own.is_empty() {
            SigType::Named {
                value_type: false,
                coded,
            }
        } else {
            SigType::Constructed {
                value_type: false,
                coded,
                arguments: (0..(inherited.len() + own.len()) as u32)
                    .map(SigType::TypeParameter)
                    .collect(),
            }
        };
        if matches!(key, MachineKey::Member(_)) {
            let view = DisplayView {
                constructor,
                locals,
                parameters,
                this,
                ..DisplayView::default()
            };
            self.attach_closures(
                owner,
                &mut plan,
                inner_sig,
                view,
                inherited.len(),
                own.len(),
                next_field,
                next_method,
            )?;
        }
        Ok(Some(plan))
    }
}

/// A state machine whose few outward-facing members still have to be named
/// under the construction the method that makes one wrote.
#[derive(Clone, Debug)]
pub(crate) struct PendingIterator {
    pub(crate) key: MachineKey,
    pub(crate) token: Token,
    pub(crate) arity: usize,
    pub(crate) own: usize,
    pub(crate) element: Type,
    pub(crate) this: Option<Type>,
    /// `<>4__this` where it holds a display class or a machine.
    pub(crate) this_sig: Option<SigType>,
    /// How many of the machine's parameters the method making it names as
    /// its class's, `!n`; the rest are that method's own, `!!n`.
    pub(crate) class_level: usize,
    pub(crate) order: Vec<(SymbolId, String, Type)>,
    pub(crate) initial: Vec<(SymbolId, String, Type)>,
    pub(crate) locals: Vec<(LocalId, String, Type)>,
}

/// The rows a state machine needs beyond its members: the interfaces it
/// implements, and which of its methods stand for the two whose names collide.
#[derive(Clone, Debug)]
pub(crate) struct IteratorImpls {
    pub(crate) token: Token,
    pub(crate) element_sig: SigType,
    pub(crate) enumerator_of: SigType,
    pub(crate) enumerator: SigType,
    pub(crate) untyped_current: Token,
    pub(crate) untyped_get_enumerator: Token,
    pub(crate) enumerable: bool,
}

/// How far through emitting a state machine's `MoveNext` the walk has got.
pub(crate) struct IteratorRun {
    pub(crate) plan: IteratorPlan,
    /// Where a `yield return` goes once the value is parked: a `true`,
    /// outside every protected region.
    pub(crate) yielded: Label,
    /// Where the end of the walk goes: a `false`.
    pub(crate) done: Label,
    /// Where the `fault` that disposes of the machine begins, where the walk
    /// goes through a `try` that yields: an exception leaving `MoveNext` then
    /// finishes the machine, as the `finally`s that ran have left it unfit
    /// to go on with.
    pub(crate) fault: Option<Label>,
}

impl BodyEmitter<'_, '_> {
    /// The dispatch at the top of `MoveNext`.
    ///
    /// `<>1__state` says where the body left off: 0 is the beginning and `k`
    /// is just after the `k`th `yield return`. Anything else — `-1` while the
    /// body is running, `-2` before it started — means there is nothing more
    /// to give, so the default answer is `false`.
    pub(crate) fn emit_move_next_dispatch(&mut self) -> Result<(), EmitError> {
        let Some(run) = &self.iterator else {
            return Ok(());
        };
        let (state, done) = (run.plan.state, run.done);
        let (sites, regions) = (run.plan.sites.clone(), run.plan.regions);
        if sites.iter().any(|site| !site.regions.is_empty()) {
            let try_start = self.stream.label();
            self.stream.mark(try_start);
            self.protected += 1;
            if let Some(run) = &mut self.iterator {
                run.fault = Some(try_start);
            }
        }
        let start = self.stream.label();
        let slot = self.state_slot()?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(state));
        self.stream.emit(Instruction::StoreLocal(slot));
        self.stream.emit(Instruction::LoadLocal(slot));
        self.stream.emit(Instruction::BranchIfFalse(start));
        self.begin_machine(state, slot, 1, None, sites, regions);
        self.emit_machine_dispatch(&[])?;
        self.emit_jump(done, 0);
        self.stream.mark(start);
        self.set_state(-1);
        Ok(())
    }

    /// The end of an iterator's `MoveNext`: falling off the body is the end
    /// of the walk, a `yield` lands on the `true` and the end on the `false`.
    pub(crate) fn end_iterator_move_next(&mut self) {
        if !self.stream.ends_flow() {
            self.emit_yield_break();
        }
        let Some(run) = self.iterator.take() else {
            return;
        };
        self.machine = None;
        if let Some(try_start) = run.fault {
            self.protected -= 1;
            let (try_end, handler_start, handler_end) = (
                self.stream.label(),
                self.stream.label(),
                self.stream.label(),
            );
            self.stream.mark(try_end);
            self.stream.mark_handler(handler_start, 0);
            // A walk that `Dispose` resumed to run its `finally`s and that
            // threw from one leaves the machine as it is.
            let skip = self.stream.label();
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(run.plan.disposing));
            self.stream.emit(Instruction::BranchIfTrue(skip));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream
                .call_effect(Instruction::CallVirtual(run.plan.dispose), 1, 0);
            self.stream.mark(skip);
            self.stream.emit(Instruction::EndFinally);
            self.stream.mark(handler_end);
            self.stream.region(crate::il::ExceptionRegion {
                kind: crate::il::HandlerKind::Fault,
                try_start,
                try_end,
                handler_start,
                handler_end,
            });
        }
        self.stream.mark(run.yielded);
        self.stream.emit(Instruction::LoadInt32(1));
        self.stream.emit(Instruction::Ret);
        self.stream.mark(run.done);
        self.stream.emit(Instruction::LoadInt32(0));
        self.stream.emit(Instruction::Ret);
    }

    /// `Dispose`: a walk that stopped inside a `try` is resumed only to leave
    /// it, so that the `finally` runs; one that stopped anywhere else, or
    /// finished, has nothing to run.
    pub(crate) fn emit_iterator_dispose(&mut self, key: MachineKey) -> Result<(), EmitError> {
        let Some(plan) = self.emitter.iterators.get(&key).cloned() else {
            return Err(EmitError::new("a state machine with no plan"));
        };
        // A machine that stopped at a `yield` inside a `try` is resumed only
        // to leave it, so that the `finally`s around it run. Whatever state
        // it was in, it is done then: the locals it holds are let go, and a
        // `GetEnumerator` after hands out the machine itself again (Roslyn's
        // `Dispose` since 4.11).
        let protected: Vec<i32> = plan
            .sites
            .iter()
            .enumerate()
            .filter(|(_, site)| !site.regions.is_empty())
            .map(|(at, _)| at as i32 + 1)
            .collect();
        let finish = self.stream.label();
        if !protected.is_empty() {
            let resume = self.stream.label();
            for state in protected {
                self.stream.emit(Instruction::LoadArgument(0));
                self.stream.emit(Instruction::LoadField(plan.state));
                self.stream.emit(Instruction::LoadInt32(state));
                self.stream.emit(Instruction::CompareEqual);
                self.stream.emit(Instruction::BranchIfTrue(resume));
            }
            self.stream.emit(Instruction::Branch(finish));
            self.stream.mark(resume);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadInt32(1));
            self.stream.emit(Instruction::StoreField(plan.disposing));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream
                .call_effect(Instruction::Call(plan.move_next), 1, 1);
            self.stream.emit(Instruction::Pop);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.emit(Instruction::StoreField(plan.disposing));
        }
        self.stream.mark(finish);
        self.clear_fields(&plan.cleared, &plan.locals)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(-2));
        self.stream.emit(Instruction::StoreField(plan.state));
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// Sets the fields of `cleared` to their defaults, in a method of the
    /// machine that is not the walk itself.
    pub(crate) fn clear_fields(
        &mut self,
        cleared: &[(LocalId, Type)],
        locals: &HashMap<LocalId, Token>,
    ) -> Result<(), EmitError> {
        for (local, ty) in cleared {
            let Some(field) = locals.get(local) else {
                continue;
            };
            self.stream.emit(Instruction::LoadArgument(0));
            let default = BoundExpression::new(
                BoundExpressionKind::Default(ty.clone()),
                ty.clone(),
                rustlyn_text::TextSpan::new(0, 0),
            );
            self.emit_expression(&default, true)?;
            self.stream.emit(Instruction::StoreField(*field));
        }
        Ok(())
    }

    /// `yield return e;` — hand the value out and record where to carry on.
    pub(crate) fn emit_yield_return(
        &mut self,
        value: &rustlyn_semantics::BoundExpression,
    ) -> Result<(), EmitError> {
        let Some(run) = &self.iterator else {
            // The method was refused a state machine; the reason says which
            // piece is missing rather than leaving a `yield` unexplained.
            let refusal = self
                .owner
                .and_then(|owner| self.emitter.iterator_refusal(MachineKey::Member(owner)));
            return Err(EmitError::new(refusal.unwrap_or_else(|| {
                "`yield return` outside the state machine it belongs to".to_string()
            })));
        };
        let (current, disposing, yielded, done) =
            (run.plan.current, run.plan.disposing, run.yielded, run.done);
        let (state, label) = self.next_suspension()?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.emit_expression(value, true)?;
        self.stream.emit(Instruction::StoreField(current));
        self.set_state(state);
        // A `ret` may not run inside a protected region (§III.3.56): the
        // answer waits outside, and a `leave` gets there. The `finally`s on
        // the way are guarded by the state, which is positive now.
        self.emit_jump(yielded, 0);
        self.stream.mark(label);
        self.set_state(-1);
        // Resumed by `Dispose`: nothing more is wanted, only the way out —
        // and the `finally`s it runs through.
        let carry_on = self.stream.label();
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(disposing));
        self.stream.emit(Instruction::BranchIfFalse(carry_on));
        self.emit_jump(done, 0);
        self.stream.mark(carry_on);
        Ok(())
    }

    /// `yield break;`, and the `return;` that means the same thing.
    pub(crate) fn emit_yield_break(&mut self) {
        self.set_state(-1);
        if let Some(done) = self.iterator.as_ref().map(|run| run.done) {
            self.emit_jump(done, 0);
        }
    }

    /// `this.<>1__state = value;`
    fn set_state(&mut self, value: i32) {
        let Some(run) = &self.iterator else {
            return;
        };
        let state = run.plan.state;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(value));
        self.stream.emit(Instruction::StoreField(state));
    }

    /// A slot for the state the dispatch reads, which never outlives it.
    fn state_slot(&mut self) -> Result<u16, EmitError> {
        let integer = self
            .emitter
            .compilation
            .special_type(rustlyn_semantics::SpecialType::Int32)
            .map(Type::named)
            .ok_or_else(|| EmitError::new("the compilation has no `System.Int32`"))?;
        self.temporary(&integer)
    }

    /// `.ctor(int state)`: chain to `object`, record the state and the thread.
    pub(crate) fn emit_iterator_constructor(&mut self, key: MachineKey) -> Result<(), EmitError> {
        let Some(plan) = self.emitter.iterators.get(&key).cloned() else {
            return Err(EmitError::new("a state machine with no plan"));
        };
        let object = self.emitter.framework_member(
            "System.Object",
            ".ctor",
            true,
            &SigType::Primitive(ElementType::Void),
            &[],
        );
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.call_effect(Instruction::Call(object), 1, 0);
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadArgument(1));
        self.stream.emit(Instruction::StoreField(plan.state));
        // Which thread made it, so that `GetEnumerator` on the same one can
        // hand back this very machine rather than a copy.
        let thread = self.emitter.framework_member(
            "System.Environment",
            "get_CurrentManagedThreadId",
            false,
            &SigType::Primitive(ElementType::I4),
            &[],
        );
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.call_effect(Instruction::Call(thread), 0, 1);
        self.stream.emit(Instruction::StoreField(plan.thread));
        Ok(())
    }

    /// `Current`, as the element type or boxed as an `object`.
    pub(crate) fn emit_iterator_current(
        &mut self,
        key: MachineKey,
        boxed: bool,
    ) -> Result<(), EmitError> {
        let Some(plan) = self.emitter.iterators.get(&key).cloned() else {
            return Err(EmitError::new("a state machine with no plan"));
        };
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(plan.current));
        if boxed {
            self.box_if_needed(&plan.element)?;
        }
        Ok(())
    }

    /// `GetEnumerator`, which hands back this machine where it can.
    ///
    /// An `IEnumerable` may be walked more than once and by more than one
    /// thread. The first walk on the thread that made it gets the machine
    /// itself — which is why it starts in state `-2` — and everything else
    /// gets a fresh one holding the same arguments.
    pub(crate) fn emit_iterator_get_enumerator(
        &mut self,
        key: MachineKey,
        untyped: bool,
    ) -> Result<(), EmitError> {
        let Some(plan) = self.emitter.iterators.get(&key).cloned() else {
            return Err(EmitError::new("a state machine with no plan"));
        };
        if untyped {
            // The untyped one is the typed one; `IEnumerator<T>` is an
            // `IEnumerator`, so nothing has to be converted.
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream
                .call_effect(Instruction::Call(plan.get_enumerator), 1, 1);
            return Ok(());
        }
        let fresh = self.stream.label();
        let ready = self.stream.label();
        if plan.enumerable {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(plan.state));
            self.stream.emit(Instruction::LoadInt32(-2));
            self.stream.emit(Instruction::CompareEqual);
            self.stream.emit(Instruction::BranchIfFalse(fresh));
            let thread = self.emitter.framework_member(
                "System.Environment",
                "get_CurrentManagedThreadId",
                false,
                &SigType::Primitive(ElementType::I4),
                &[],
            );
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(plan.thread));
            self.stream.call_effect(Instruction::Call(thread), 0, 1);
            self.stream.emit(Instruction::CompareEqual);
            self.stream.emit(Instruction::BranchIfFalse(fresh));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.emit(Instruction::StoreField(plan.state));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::Branch(ready));
        }
        self.stream.mark(fresh);
        self.stream.emit(Instruction::LoadInt32(0));
        self.stream
            .call_effect(Instruction::NewObject(plan.constructor), 1, 1);
        // The `this` the method was called on goes into the copy.
        if let Some(field) = plan.this {
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(field));
            self.stream.emit(Instruction::StoreField(field));
        }
        self.stream.mark(ready);
        // Each walk starts from what the method was called with, whether it
        // is this machine's first or a copy's.
        for ((_, walked), (_, called)) in plan.order.iter().zip(&plan.initial) {
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(*called));
            self.stream.emit(Instruction::StoreField(*walked));
        }
        Ok(())
    }

    /// The end of a block of an iterator's `MoveNext`: each local the block
    /// declared that the machine keeps in a field for no closure is cleared,
    /// so that the machine holds on to nothing it will not read again
    /// (Roslyn's `AddVariableCleanup`). A block left by a jump is not.
    pub(crate) fn clear_hoisted(
        &mut self,
        statements: &[rustlyn_semantics::BoundStatement],
    ) -> Result<(), EmitError> {
        let plan_cleared = match (&self.iterator, &self.async_run) {
            (Some(run), _) => run.plan.cleared.clone(),
            (None, Some(run)) => run.plan.cleared.clone(),
            (None, None) => return Ok(()),
        };
        if !self.stream.end_reachable() {
            return Ok(());
        }
        let cleared: Vec<(LocalId, Type)> = statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                rustlyn_semantics::BoundStatementKind::LocalDeclaration { local, .. } => {
                    plan_cleared
                        .iter()
                        .find(|(cleared, _)| cleared == local)
                        .cloned()
                }
                _ => None,
            })
            .collect();
        for (local, ty) in cleared {
            let span = rustlyn_text::TextSpan::new(0, 0);
            let clear = rustlyn_semantics::BoundExpression::new(
                rustlyn_semantics::BoundExpressionKind::Assignment {
                    target: Box::new(rustlyn_semantics::BoundExpression::new(
                        rustlyn_semantics::BoundExpressionKind::Local(local),
                        ty.clone(),
                        span,
                    )),
                    value: Box::new(rustlyn_semantics::BoundExpression::new(
                        rustlyn_semantics::BoundExpressionKind::Default(ty.clone()),
                        ty.clone(),
                        span,
                    )),
                },
                ty,
                span,
            );
            self.emit_expression(&clear, false)?;
        }
        Ok(())
    }

    /// `Reset`, which no iterator supports (§15.15.5).
    pub(crate) fn emit_iterator_reset(&mut self) {
        let constructor = self.emitter.framework_member(
            "System.NotSupportedException",
            ".ctor",
            true,
            &SigType::Primitive(ElementType::Void),
            &[],
        );
        self.stream
            .call_effect(Instruction::NewObject(constructor), 0, 1);
        self.stream.emit(Instruction::Throw);
    }

    /// The method the source wrote: make a machine, fill it, hand it back.
    pub(crate) fn emit_iterator_start(&mut self, key: MachineKey) -> Result<(), EmitError> {
        let Some(plan) = self.emitter.iterators.get(&key).cloned() else {
            return Err(EmitError::new("a state machine with no plan"));
        };
        // `-2` says "made but not walked", which is what lets the first
        // `foreach` over it use this very machine.
        self.stream
            .emit(Instruction::LoadInt32(if plan.enumerable { -2 } else { 0 }));
        self.stream
            .call_effect(Instruction::NewObject(plan.outer_constructor), 1, 1);
        if let Some(field) = plan.outer_this {
            self.stream.emit(Instruction::Dup);
            self.push_this_value()?;
            self.stream.emit(Instruction::StoreField(field));
        }
        for (parameter, field) in &plan.outer_order {
            let index = self.argument_index(*parameter)?;
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadArgument(index));
            self.stream.emit(Instruction::StoreField(*field));
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }
}

impl Emitter<'_> {
    /// The rows of one state machine: the type, the interfaces it implements,
    /// the two `MethodImpl`s its colliding names need, and its members.
    pub(crate) fn write_iterator_type(
        &mut self,
        plan: &TypePlan,
        key: MachineKey,
        type_offsets: &[u32],
    ) -> Result<(), EmitError> {
        let name = self.machine_type_name(key, plan);
        let object = self
            .references
            .type_ref_coded(&mut self.metadata, "System.Object");
        let token = self.metadata.add_type_def(
            type_attributes::NESTED_PRIVATE
                | type_attributes::SEALED
                | type_attributes::BEFORE_FIELD_INIT,
            "",
            &name,
            object,
        );
        if token != plan.token {
            return Err(EmitError::new(format!(
                "a state machine was written as {token:?} where {:?} was planned",
                plan.token
            )));
        }
        if let Some(enclosing) = self.types.get(&plan.symbol).copied() {
            self.metadata.add_nested_class(token, enclosing);
        }
        self.mark_compiler_generated(token);
        let inherited = self.display_parameters(plan);
        let generic_owner = (token.0 & 0x00FF_FFFF) << 1;
        // The constraints are stated in the machine's own parameters, `!1`
        // where the method's say `!!1`.
        self.display_generics = inherited.clone();
        for (number, parameter) in inherited.iter().enumerate() {
            let name = self.compilation.symbols().get(*parameter).name.clone();
            let flags = crate::emitter::generic_param_flags(self.compilation.symbols(), *parameter)
                & !0x0003u16;
            self.metadata
                .add_generic_param(number as u16, flags, generic_owner, &name);
            let written = self.write_constraints(generic_owner, number as u16, *parameter);
            if written.is_err() {
                self.display_generics = Vec::new();
            }
            written?;
        }
        self.display_generics = Vec::new();

        let Some(impls) = self
            .iterator_impls
            .iter()
            .find(|found| found.token == plan.token)
            .cloned()
        else {
            return Err(EmitError::new("a state machine with no interface rows"));
        };
        let mut blob = Vec::new();
        impls.enumerator_of.write(&mut blob);
        let enumerator_of = self.references.type_spec(&mut self.metadata, &blob);
        let mut enumerable_blob = Vec::new();
        SigType::Constructed {
            value_type: false,
            coded: self.references.type_ref_coded(
                &mut self.metadata,
                "System.Collections.Generic.IEnumerable`1",
            ),
            arguments: vec![impls.element_sig.clone()],
        }
        .write(&mut enumerable_blob);
        let enumerable_of = self
            .references
            .type_spec(&mut self.metadata, &enumerable_blob);

        // A `TypeDefOrRef` tagged 2 is a `TypeSpec`.
        let mut interfaces = vec![
            type_def_or_ref(2, enumerator_of.0 & 0x00FF_FFFF),
            self.references
                .type_ref_coded(&mut self.metadata, "System.Collections.IEnumerator"),
            self.references
                .type_ref_coded(&mut self.metadata, "System.IDisposable"),
        ];
        if impls.enumerable {
            interfaces.push(type_def_or_ref(2, enumerable_of.0 & 0x00FF_FFFF));
            interfaces.push(
                self.references
                    .type_ref_coded(&mut self.metadata, "System.Collections.IEnumerable"),
            );
        }
        for interface in interfaces {
            self.metadata.add_interface_impl(token, interface);
        }

        // `IEnumerator.Current` and `IEnumerable.GetEnumerator` cannot be
        // implemented by name — the typed ones already have those names — so
        // a row says which method stands for which.
        let current = self.references.member_ref(
            &mut self.metadata,
            "System.Collections.IEnumerator",
            "get_Current",
            &method_signature(true, &SigType::Primitive(ElementType::Object), &[]),
        );
        self.metadata.add_method_impl(
            token,
            method_def_or_ref(0, impls.untyped_current),
            method_def_or_ref(1, current),
        );
        if impls.enumerable {
            let walk = self.references.member_ref(
                &mut self.metadata,
                "System.Collections.IEnumerable",
                "GetEnumerator",
                &method_signature(true, &impls.enumerator, &[]),
            );
            self.metadata.add_method_impl(
                token,
                method_def_or_ref(0, impls.untyped_get_enumerator),
                method_def_or_ref(1, walk),
            );
        }
        // What the machine's own members name is what it declares, so a
        // signature written here says `!0` where the method that makes one
        // says `!!0`.
        self.display_generics = inherited;
        let written = self.write_members(plan, type_offsets);
        self.display_generics = Vec::new();
        written
    }

    /// Writes again every signature of a state machine that carries its
    /// element type.
    ///
    /// A machine is planned as part of the type holding it, when the types
    /// declared after that one have no `TypeDef` token yet — and a type with
    /// no token is written as a `TypeRef`, which sends the runtime looking
    /// for `Microsoft.CodeAnalysis.MetadataReference` in `System.Runtime`.
    /// Every token is assigned by the time the last type is planned, which is
    /// when the element can be named for what it is.
    pub(crate) fn restate_iterator_signatures(
        &mut self,
        plans: &mut [TypePlan],
    ) -> Result<(), EmitError> {
        for plan in plans.iter_mut() {
            let Some(key) = plan.machine else {
                continue;
            };
            let Some(element) = self
                .iterators
                .get(&key)
                .map(|iterator| iterator.element.clone())
            else {
                continue;
            };
            // A machine names its element with its own parameters, `!0`,
            // whatever the method making one calls them.
            self.display_generics = self.machine_generics(key);
            let element_sig = self.sig_type(&element);
            self.display_generics = Vec::new();
            let element_sig = element_sig?;
            let enumerator_of = SigType::Constructed {
                value_type: false,
                coded: self.references.type_ref_coded(
                    &mut self.metadata,
                    "System.Collections.Generic.IEnumerator`1",
                ),
                arguments: vec![element_sig.clone()],
            };
            for method in &mut plan.methods {
                match method.source {
                    MethodSource::IteratorCurrent(_, false) => {
                        method.signature = Some(method_signature(true, &element_sig, &[]));
                    }
                    MethodSource::IteratorGetEnumerator(_, false) => {
                        method.signature = Some(method_signature(true, &enumerator_of, &[]));
                    }
                    _ => {}
                }
            }
            let token = plan.token;
            let Some(impls) = self
                .iterator_impls
                .iter_mut()
                .find(|found| found.token == token)
            else {
                return Err(EmitError::new("a state machine with no interface rows"));
            };
            impls.element_sig = element_sig;
            impls.enumerator_of = enumerator_of;
        }
        Ok(())
    }

    /// Names the members of every state machine that sits in a generic type
    /// or belongs to a generic method, as the method that makes one has to.
    pub(crate) fn resolve_iterator_members(&mut self) -> Result<(), EmitError> {
        for pending in std::mem::take(&mut self.iterator_pending) {
            let sig = SigType::Constructed {
                value_type: false,
                coded: type_def_or_ref(0, pending.token.0 & 0x00FF_FFFF),
                arguments: (0..pending.class_level as u32)
                    .map(SigType::TypeParameter)
                    .chain(
                        (0..(pending.arity + pending.own - pending.class_level) as u32)
                            .map(SigType::MethodTypeParameter),
                    )
                    .collect(),
            };
            let mut blob = Vec::new();
            sig.write(&mut blob);
            let outer = self.references.type_spec(&mut self.metadata, &blob);
            // A member of a generic type is reached through a construction
            // even from inside it, where the machine's own parameters are
            // what name it.
            let mut blob = Vec::new();
            SigType::Constructed {
                value_type: false,
                coded: type_def_or_ref(0, pending.token.0 & 0x00FF_FFFF),
                arguments: (0..(pending.arity + pending.own) as u32)
                    .map(SigType::TypeParameter)
                    .collect(),
            }
            .write(&mut blob);
            let inner = self.references.type_spec(&mut self.metadata, &blob);

            // A `MemberRef` under a `TypeSpec` carries the definition's own
            // signature (§II.22.25), so these are written as the machine
            // names them whichever construction they hang off.
            self.display_generics = self.machine_generics(pending.key);
            let integer = Type::named(
                self.compilation
                    .special_type(rustlyn_semantics::SpecialType::Int32)
                    .ok_or_else(|| EmitError::new("the compilation has no `System.Int32`"))?,
            );
            let made = method_signature(
                true,
                &SigType::Primitive(ElementType::Void),
                &[SigType::Primitive(ElementType::I4)],
            );
            let element_sig = self.sig_type(&pending.element)?;
            let walks = method_signature(
                true,
                &SigType::Constructed {
                    value_type: false,
                    coded: self.references.type_ref_coded(
                        &mut self.metadata,
                        "System.Collections.Generic.IEnumerator`1",
                    ),
                    arguments: vec![element_sig],
                },
                &[],
            );
            let boolean = Type::named(
                self.compilation
                    .special_type(rustlyn_semantics::SpecialType::Boolean)
                    .ok_or_else(|| EmitError::new("the compilation has no `System.Boolean`"))?,
            );
            let moves = method_signature(true, &SigType::Primitive(ElementType::Boolean), &[]);
            let mut views = Vec::new();
            for spec in [outer, inner] {
                let constructor =
                    self.references
                        .member_of_spec(&mut self.metadata, spec, ".ctor", &made);
                let get_enumerator = self.references.member_of_spec(
                    &mut self.metadata,
                    spec,
                    "GetEnumerator",
                    &walks,
                );
                let move_next =
                    self.references
                        .member_of_spec(&mut self.metadata, spec, "MoveNext", &moves);
                let dispose = self.references.member_of_spec(
                    &mut self.metadata,
                    spec,
                    "Dispose",
                    &method_signature(true, &SigType::Primitive(ElementType::Void), &[]),
                );
                let state = self.display_field(spec, "<>1__state", &integer)?;
                let current = self.display_field(spec, "<>2__current", &pending.element)?;
                let thread = self.display_field(spec, "<>l__initialThreadId", &integer)?;
                let disposing = self.display_field(spec, "<>w__disposing", &boolean)?;
                let held = match (&pending.this, &pending.this_sig) {
                    (Some(ty), _) => Some(self.display_field(spec, "<>4__this", ty)?),
                    (None, Some(sig)) => Some(self.display_field_sig(spec, "<>4__this", sig)),
                    (None, None) => None,
                };
                let mut order = Vec::new();
                for (parameter, name, ty) in &pending.order {
                    order.push((*parameter, self.display_field(spec, name, ty)?));
                }
                let mut initial = Vec::new();
                for (parameter, name, ty) in &pending.initial {
                    initial.push((*parameter, self.display_field(spec, name, ty)?));
                }
                let mut locals = HashMap::new();
                for (local, name, ty) in &pending.locals {
                    locals.insert(*local, self.display_field(spec, name, ty)?);
                }
                views.push((
                    constructor,
                    get_enumerator,
                    state,
                    current,
                    thread,
                    held,
                    order,
                    locals,
                    (disposing, (move_next, dispose), initial),
                ));
            }
            self.display_generics = Vec::new();
            let inside = views.pop().expect("both views were built");
            let outside = views.pop().expect("both views were built");
            if let Some(plan) = self.iterators.get_mut(&pending.key) {
                plan.outer_constructor = outside.0;
                plan.outer_this = outside.5;
                plan.outer_order = if plan.enumerable {
                    outside.8.2
                } else {
                    outside.6
                };
                plan.constructor = inside.0;
                plan.get_enumerator = inside.1;
                plan.state = inside.2;
                plan.current = inside.3;
                plan.thread = inside.4;
                plan.this = inside.5;
                plan.parameters = inside.6.iter().copied().collect();
                plan.order = inside.6;
                plan.locals = inside.7;
                plan.disposing = inside.8.0;
                (plan.move_next, plan.dispose) = inside.8.1;
                plan.initial = inside.8.2;
            }
            // A member's machine is its lambdas' display class, and they
            // read the fields under the same names.
            if let MachineKey::Member(owner) = pending.key
                && let Some(plan) = self.iterators.get(&pending.key).cloned()
            {
                self.refresh_machine_display(
                    owner,
                    plan.constructor,
                    &plan.locals,
                    &plan.parameters,
                    plan.this,
                );
            }
        }
        Ok(())
    }
}

/// The `MethodDefOrRef` coded index of §II.24.2.6: tag 0 is a `MethodDef` and
/// tag 1 a `MemberRef`.
fn method_def_or_ref(tag: u32, token: Token) -> u32 {
    ((token.0 & 0x00FF_FFFF) << 1) | tag
}

/// The structs besides the language's own numbers that Roslyn counts as
/// special types, which hold no references whatever assembly they are in.
const BUILT_IN_STRUCTS: [&str; 8] = [
    "System.IntPtr",
    "System.UIntPtr",
    "System.DateTime",
    "System.ArgIterator",
    "System.RuntimeArgumentHandle",
    "System.RuntimeFieldHandle",
    "System.RuntimeMethodHandle",
    "System.RuntimeTypeHandle",
];
