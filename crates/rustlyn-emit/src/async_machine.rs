//! The state machine an `async` method becomes.
//!
//! The CLI has no `await`: what C# calls an async method is a class the
//! compiler writes, holding the method's arguments, its locals and how far
//! through the body it got, driven by a *builder* the framework supplies for
//! the kind of task the method returns (§15.15). The method itself is left
//! making one of those, starting it, and handing back the builder's task; the
//! body moves into `MoveNext`, and every `await` in it becomes a place the
//! machine can stop at and be resumed from.
//!
//! The shape is the one C# compilers write for a class-based machine: a
//! `MoveNext` whose whole body sits in a `try`, an `await` that asks the
//! awaiter whether it is done and, when it is not, records where to carry on
//! and hands itself to the builder, and a resume that reads the awaiter back
//! out of a field. A `try` inside the body that holds an `await` gets a
//! dispatch of its own at its entry, since a protected region may only be
//! entered at its start.

use std::collections::HashMap;

use rustlyn_semantics::{
    BinaryOperator, BoundBody, BoundCaseLabel, BoundCatch, BoundExpression, BoundExpressionKind,
    BoundPattern, BoundPatternKind, BoundStatement, BoundStatementKind, BoundSwitchLabel,
    BoundSwitchSection, ConstantValue, LocalId, LocalSymbol, Modifiers, RefKind, SymbolId,
    SymbolKind, Type, UnaryOperator,
};
use rustlyn_text::TextSpan;

use crate::codegen::{BodyEmitter, DisplayAt};
use crate::emitter::{
    Closure, ClosureHost, DisplayClass, DisplayView, EmitError, Emitter, FieldPlan, MachineKey,
    MethodPlan, MethodSource, ParameterPlan, TypePlan, within,
};
use crate::il::{ExceptionRegion, HandlerKind, Instruction, Label, Token};
use crate::metadata::{field_attributes, method_attributes, table, type_attributes};
use crate::signature::{
    ElementType, SigType, generic_method_signature, method_signature, method_spec_signature,
    type_def_or_ref,
};

/// Which builder a method's return type asks for (§15.15.1).
#[derive(Clone, Debug)]
pub(crate) enum AsyncKind {
    Void,
    Task,
    TaskOf(Type),
    ValueTask,
    ValueTaskOf(Type),
    /// An `async` iterator (C# 8), returning `IAsyncEnumerable<T>` or
    /// `IAsyncEnumerator<T>`: a machine that is its own enumerator, whose
    /// `MoveNextAsync` runs the body up to the next `yield return` and whose
    /// `await`s suspend it in between. `enumerable` says which of the two
    /// was declared.
    Iterator {
        element: Type,
        enumerable: bool,
    },
    /// A task-like type (C# 7), built by the builder its
    /// `[AsyncMethodBuilder(typeof(B))]` names: `builder` is `B`, constructed
    /// over the task's type argument where it has one, which is what the
    /// method's `return` statements give.
    Custom {
        task: Type,
        builder: Type,
        result: Option<Type>,
    },
}

impl AsyncKind {
    /// The builder's metadata name, for the builders the framework has.
    fn builder_name(&self) -> Option<&'static str> {
        Some(match self {
            Self::Void => "System.Runtime.CompilerServices.AsyncVoidMethodBuilder",
            Self::Task => "System.Runtime.CompilerServices.AsyncTaskMethodBuilder",
            Self::TaskOf(_) => "System.Runtime.CompilerServices.AsyncTaskMethodBuilder`1",
            Self::ValueTask => "System.Runtime.CompilerServices.AsyncValueTaskMethodBuilder",
            Self::ValueTaskOf(_) => "System.Runtime.CompilerServices.AsyncValueTaskMethodBuilder`1",
            Self::Iterator { .. } => "System.Runtime.CompilerServices.AsyncIteratorMethodBuilder",
            Self::Custom { .. } => return None,
        })
    }

    /// The element an `async` iterator hands out, and whether it was
    /// declared `IAsyncEnumerable<T>`.
    pub(crate) fn iterator(&self) -> Option<(&Type, bool)> {
        match self {
            Self::Iterator {
                element,
                enumerable,
            } => Some((element, *enumerable)),
            _ => None,
        }
    }

    /// What the method's `return` statements give, where they give anything.
    fn result(&self) -> Option<&Type> {
        match self {
            Self::TaskOf(result) | Self::ValueTaskOf(result) => Some(result),
            Self::Custom { result, .. } => result.as_ref(),
            _ => None,
        }
    }

    /// The task the builder hands back, as a member of the builder names it:
    /// `Task<!0>` where the builder is generic.
    fn task_sig(&self, emitter: &mut Emitter<'_>) -> Option<SigType> {
        let (name, value_type, generic) = match self {
            Self::Void | Self::Iterator { .. } => return None,
            Self::Custom { task, result, .. } => {
                return emitter.own_sig(task, result.is_some());
            }
            Self::Task => ("System.Threading.Tasks.Task", false, false),
            Self::TaskOf(_) => ("System.Threading.Tasks.Task`1", false, true),
            Self::ValueTask => ("System.Threading.Tasks.ValueTask", true, false),
            Self::ValueTaskOf(_) => ("System.Threading.Tasks.ValueTask`1", true, true),
        };
        let coded = emitter
            .references
            .type_ref_coded(&mut emitter.metadata, name);
        Some(if generic {
            SigType::Constructed {
                value_type,
                coded,
                arguments: vec![SigType::TypeParameter(0)],
            }
        } else {
            SigType::Named { value_type, coded }
        })
    }
}

/// Where everything the state machine holds ended up.
#[derive(Clone, Debug)]
pub(crate) struct AsyncPlan {
    pub(crate) kind: AsyncKind,
    /// The builder, as a type: `AsyncTaskMethodBuilder<int>`.
    pub(crate) builder_type: Type,
    /// The machine as the method making one names it — the enclosing type's
    /// parameters as `!n` and the method's own as `!!n` — and as it names
    /// itself, where every parameter is its own.
    pub(crate) outer_sig: SigType,
    pub(crate) inner_sig: SigType,
    pub(crate) constructor: Token,
    pub(crate) outer_constructor: Token,
    pub(crate) state: Token,
    pub(crate) outer_state: Token,
    pub(crate) builder: Token,
    pub(crate) outer_builder: Token,
    pub(crate) this: Option<Token>,
    pub(crate) outer_this: Option<Token>,
    pub(crate) parameters: HashMap<SymbolId, Token>,
    pub(crate) order: Vec<(SymbolId, Token)>,
    pub(crate) outer_order: Vec<(SymbolId, Token)>,
    pub(crate) locals: HashMap<LocalId, Token>,
    /// The hoisted locals no closure reads, of types that might hold
    /// references, that the body declares itself: cleared where their block
    /// ends. A compiler's temporary is not, as the blocks the spiller writes
    /// are not scopes. `root_cleared` are the ones the body's own block
    /// declares, cleared where the machine finishes; `finished_cleared` is
    /// every one, which an `async` iterator lets go of however it finishes.
    pub(crate) cleared: Vec<(LocalId, Type)>,
    pub(crate) root_cleared: Vec<(LocalId, Type)>,
    pub(crate) finished_cleared: Vec<(LocalId, Type)>,
    /// The same fields as the method making the machine names them.
    pub(crate) outer_locals: HashMap<LocalId, Token>,
    /// A lambda's parameters, which are locals of the body and arrive as the
    /// arguments of the method the lambda became, in order.
    pub(crate) parameter_locals: Vec<LocalId>,
    /// Whether the method making the machine is itself a member of a display
    /// class or another machine: its `this` is that object, kept in
    /// `<>4__this`, and what the body calls `this` is reached through it.
    pub(crate) hosted: bool,
    /// One field per distinct awaiter type, since an awaiter is kept while
    /// the machine is suspended and read back when it resumes.
    pub(crate) awaiters: Vec<(Type, Token)>,
    /// Every `await`, in the order `MoveNext` reaches them, with the
    /// protected regions around each.
    pub(crate) sites: Vec<AwaitSite>,
    /// How many protected regions `MoveNext` enters, in the order it does.
    pub(crate) regions: usize,
    /// The field holding the class a loop body makes each time round, by
    /// the body's span: a local of `MoveNext` would not outlive an `await`
    /// inside the loop.
    pub(crate) scopes: HashMap<TextSpan, Token>,
    /// What an `async` iterator's machine keeps beyond an `async` method's,
    /// where it is one.
    pub(crate) iterator: Option<AsyncIteratorPlan>,
}

/// The members an `async` iterator's machine has beyond an `async`
/// method's (Roslyn's `AsyncIteratorRewriter`): the promise `MoveNextAsync`
/// and `DisposeAsync` hand out, the element last yielded, and, for an
/// `IAsyncEnumerable<T>`, what `GetAsyncEnumerator` needs to start a walk
/// of its own from what the method was called with.
#[derive(Clone, Debug)]
pub(crate) struct AsyncIteratorPlan {
    pub(crate) element: Type,
    pub(crate) enumerable: bool,
    /// `<>v__promiseOfValueOrEnd`, a `ManualResetValueTaskSourceCore<bool>`:
    /// what every `ValueTask<bool>` of `MoveNextAsync` and every `ValueTask`
    /// of `DisposeAsync` waits on, set when the body yields or ends.
    pub(crate) promise: Token,
    /// `<>2__current`, what the last `yield return` gave.
    pub(crate) current: Token,
    /// The local the spiller made for dispose mode (see
    /// [`DISPOSE_MODE`]): set by `DisposeAsync` and by `yield break`, it
    /// sends a resumed body out through its `finally`s and nowhere else.
    pub(crate) dispose_mode: LocalId,
    /// `<>l__initialThreadId`, for an enumerable: the first walk on the
    /// thread that made the machine is the machine itself.
    pub(crate) thread: Option<Token>,
    /// `<>x__combinedTokens`, for an enumerable with an
    /// `[EnumeratorCancellation]` parameter: the source linking it with the
    /// token `GetAsyncEnumerator` was given, disposed when the walk ends.
    pub(crate) combined: Option<Token>,
    /// `<>3__name` for each parameter of an enumerable: what the method was
    /// called with, which each walk copies into the fields its body reads.
    pub(crate) proxies: Vec<(SymbolId, Token)>,
    /// The same as the method making the machine names them.
    pub(crate) outer_proxies: Vec<(SymbolId, Token)>,
    /// The `[EnumeratorCancellation]` parameter of an enumerable.
    pub(crate) cancellation: Option<SymbolId>,
}

/// The name of the local an `async` iterator's dispose mode is kept in,
/// which the spiller declares and the machine hoists like any other.
pub(crate) const DISPOSE_MODE: &str = "<>w__disposeMode";

/// The state an `async` iterator starts in once asked to walk (Roslyn's
/// `InitialAsyncIteratorState`); the one an `IAsyncEnumerable<T>` is made in
/// is `-2`, which `GetAsyncEnumerator` moves on from.
pub(crate) const ITERATOR_START: i32 = -3;
/// The state of the first `yield return` of an `async` iterator; the ones
/// after it count down (Roslyn's `FirstResumableAsyncIteratorState`).
const FIRST_YIELD_STATE: i32 = -4;

/// One suspension — an `await`, or a `yield return` — with the protected
/// regions around it, outermost first, as numbered in the order `MoveNext`
/// enters them.
#[derive(Clone, Debug, Default)]
pub(crate) struct AwaitSite {
    pub(crate) regions: Vec<usize>,
    /// Whether it is a `yield return`, which an `async` iterator numbers
    /// apart from its `await`s.
    pub(crate) yields: bool,
}

/// A machine in a generic type or method, whose members still have to be
/// named under a construction once every type has a token.
#[derive(Clone, Debug)]
pub(crate) struct PendingAsync {
    pub(crate) key: MachineKey,
    pub(crate) token: Token,
    pub(crate) arity: usize,
    pub(crate) own: usize,
    pub(crate) builder: Type,
    pub(crate) this: Option<Type>,
    /// `<>4__this` where it holds a display class or a machine, which only a
    /// signature names.
    pub(crate) this_sig: Option<SigType>,
    /// How many of the machine's type parameters the method making it names
    /// as its class's, `!n`: the enclosing type's, and the owner's too where
    /// that method is a member of a display class or another machine, which
    /// declares them as its own. The rest are the method's, `!!n`.
    pub(crate) class_level: usize,
    pub(crate) order: Vec<(SymbolId, String, Type)>,
    pub(crate) locals: Vec<(LocalId, String, Type)>,
    pub(crate) awaiters: Vec<(Type, String)>,
    pub(crate) scopes: Vec<(TextSpan, String)>,
    /// An `async` iterator's own fields, by name and type: the promise, the
    /// element, the thread, the combined tokens and the parameter copies.
    pub(crate) iterator: Vec<(String, Type)>,
}

/// What both kinds of state machine share while their `MoveNext` is being
/// emitted: where each suspension resumes, where each protected region
/// begins, and how far the walk has got through both.
pub(crate) struct MachineRun {
    /// The `<>1__state` field, as the machine names it.
    pub(crate) state: Token,
    /// The slot `MoveNext` read the state into, for the dispatches.
    pub(crate) state_slot: u16,
    /// The state each suspension records, in the order the walk meets them:
    /// an `await` counts from 0 and a `yield return` from 1 (0 is an
    /// iterator not yet started); an `async` iterator's `yield return`s
    /// count down from -4 beside its `await`s.
    pub(crate) states: Vec<i32>,
    pub(crate) sites: Vec<AwaitSite>,
    /// One label per suspension, marked where the body carries on after it.
    pub(crate) resume: Vec<Label>,
    /// One label per protected region, marked at its first instruction.
    pub(crate) entries: Vec<Label>,
    pub(crate) next_site: usize,
    pub(crate) next_region: usize,
    /// The protected regions the cursor is inside, outermost first, by the
    /// numbers the plan gave them.
    pub(crate) region_path: Vec<usize>,
}

/// How far through emitting an `async` machine's `MoveNext` the walk has got.
pub(crate) struct AsyncRun {
    pub(crate) plan: AsyncPlan,
    /// A slot holding `this`, which the builder takes by reference.
    pub(crate) machine_slot: u16,
    /// Where a `return` goes: outside the `try`, to hand the result over.
    pub(crate) done: Label,
    /// The `ret` at the very end, which a suspension leaves to.
    pub(crate) finished: Label,
    pub(crate) result_slot: Option<u16>,
    /// Where an `async` iterator's `yield return` leaves to, outside the
    /// `try`, to say `true` through the promise.
    pub(crate) yielded: Option<Label>,
}

/// Where the value an `await` produces is put.
enum AwaitTarget {
    Dropped,
    Local(LocalId),
}

impl Emitter<'_> {
    /// Whether a member is an `async` method or accessor.
    pub(crate) fn is_async_method(&self, member: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        symbols.get(member).modifiers.contains(Modifiers::ASYNC)
            && symbols.get(member).as_method().is_some()
    }

    /// Whether a closure is an `async` lambda or an `async` local function.
    pub(crate) fn is_async_closure(&mut self, key: MachineKey) -> bool {
        match key {
            MachineKey::Member(member) => self.is_async_method(member),
            MachineKey::Lambda { owner, index } => self
                .body_of(owner)
                .and_then(|body| {
                    body.lambdas
                        .get(index)
                        .map(|lambda| lambda.task_type.is_some())
                })
                .unwrap_or(false),
            MachineKey::Function { .. } => self
                .machine_symbol(key)
                .is_some_and(|symbol| self.is_async_method(symbol)),
        }
    }

    /// The symbol a machine's method has, where it has one: a member's own,
    /// a local function's; a lambda has none.
    pub(crate) fn machine_symbol(&mut self, key: MachineKey) -> Option<SymbolId> {
        match key {
            MachineKey::Member(member) => Some(member),
            MachineKey::Lambda { .. } => None,
            MachineKey::Function { owner, index } => self.body_of(owner).and_then(|body| {
                body.local_functions
                    .get(index)
                    .map(|function| function.symbol)
            }),
        }
    }

    /// The body a machine runs: the member's, or the closure's statements on
    /// the member's table of locals, which is where they were bound.
    pub(crate) fn machine_body(&mut self, key: MachineKey) -> Option<BoundBody> {
        let body = self.bound_body(key.owner())?;
        Some(match key {
            MachineKey::Member(_) => body,
            MachineKey::Lambda { index, .. } => BoundBody {
                statements: vec![body.lambdas.get(index)?.body.clone()],
                ..body
            },
            MachineKey::Function { index, .. } => BoundBody {
                statements: vec![body.local_functions.get(index)?.body.clone()],
                ..body
            },
        })
    }

    /// The loop bodies of a machine's own statements that get a class each
    /// time round: the ones written directly in the member or closure the
    /// machine is for, not inside another closure of it, whose method has
    /// locals of its own to keep such a class in.
    fn machine_scopes(&mut self, key: MachineKey) -> Vec<TextSpan> {
        let owner = key.owner();
        let Some(body) = self.body_of(owner) else {
            return Vec::new();
        };
        let mut closures: Vec<(Option<MachineKey>, TextSpan)> = body
            .lambdas
            .iter()
            .enumerate()
            .map(|(index, lambda)| (Some(MachineKey::Lambda { owner, index }), lambda.span))
            .collect();
        for (index, function) in body.local_functions.iter().enumerate() {
            if let Some(span) = self
                .compilation
                .declaration_node(function.symbol)
                .map(|node| node.span())
            {
                closures.push((Some(MachineKey::Function { owner, index }), span));
            }
        }
        let wanted = match key {
            MachineKey::Member(_) => None,
            other => Some(other),
        };
        self.nested_display_owners(owner)
            .into_iter()
            .filter_map(|closure| match closure {
                Closure::Scope(span) => Some(span),
                Closure::Lambda(_) | Closure::Function(_) => None,
            })
            .filter(|span| {
                // The innermost closure around the loop, if any, is whose
                // method the loop is written in.
                let innermost = closures
                    .iter()
                    .filter(|(_, it)| *it != *span && within(*span, *it))
                    .min_by_key(|(_, it)| it.length())
                    .and_then(|(key, _)| *key);
                innermost == wanted
            })
            .collect()
    }

    /// What the method a machine stands in for returns.
    pub(crate) fn machine_return(&mut self, key: MachineKey) -> Type {
        match key {
            MachineKey::Lambda { owner, index } => self
                .body_of(owner)
                .and_then(|body| {
                    body.lambdas.get(index).map(|lambda| {
                        lambda
                            .task_type
                            .clone()
                            .unwrap_or_else(|| lambda.return_type.clone())
                    })
                })
                .unwrap_or(Type::Error),
            _ => match self.machine_symbol(key) {
                Some(symbol) => self.type_of(symbol),
                None => Type::Error,
            },
        }
    }

    /// The parameter symbols the machine's method declares.
    pub(crate) fn machine_parameters(&mut self, key: MachineKey) -> Vec<SymbolId> {
        let Some(symbol) = self.machine_symbol(key) else {
            return Vec::new();
        };
        self.compilation
            .symbols()
            .get(symbol)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default()
    }

    /// A lambda's parameters, which are locals rather than symbols.
    pub(crate) fn machine_parameter_locals(&mut self, key: MachineKey) -> Vec<LocalId> {
        match key {
            MachineKey::Lambda { owner, index } => self
                .body_of(owner)
                .and_then(|body| {
                    body.lambdas
                        .get(index)
                        .map(|lambda| lambda.parameters.clone())
                })
                .unwrap_or_default(),
            _ => Vec::new(),
        }
    }

    /// The locals the machine keeps in fields: every local of a member's
    /// body, and of a closure's only the ones declared inside it — the rest
    /// belong to the member around it, and the ones it reads are reached
    /// through the display class it was made a method of.
    ///
    /// A `ref` local and a local of a `ref struct` stay ordinary locals of
    /// `MoveNext`: a field may be neither, and C# 13 lets them into an
    /// `async` method or an iterator only where no `await` or `yield` falls
    /// while they are live, so nothing of theirs has to outlast a resumption.
    pub(crate) fn machine_locals(
        &mut self,
        key: MachineKey,
        body: &BoundBody,
    ) -> Vec<(LocalId, LocalSymbol)> {
        let inside = match key {
            MachineKey::Member(_) => None,
            MachineKey::Lambda { owner, index } => self
                .body_of(owner)
                .and_then(|body| body.lambdas.get(index).map(|lambda| lambda.span)),
            MachineKey::Function { .. } => self
                .machine_symbol(key)
                .and_then(|symbol| self.compilation.declaration_node(symbol))
                .map(|node| node.span()),
        };
        // An optimized build keeps a local whose address is taken (`&x`, in
        // `unsafe` code) a local of `MoveNext`, as Roslyn does: a field of
        // the machine could move under the pointer. A debug build hoists
        // every local, that one too.
        let addressed = if self.compilation.options().optimize {
            addressed_locals(&body.statements)
        } else {
            std::collections::HashSet::new()
        };
        body.locals
            .iter()
            .enumerate()
            .filter(|(_, local)| {
                inside.is_none_or(|span| {
                    local.span.start() >= span.start() && local.span.end() <= span.end()
                })
            })
            .filter(|(_, local)| !local.by_ref && !self.is_ref_like(&local.ty))
            .filter(|(index, _)| !addressed.contains(&LocalId(*index as u32)))
            .map(|(index, local)| (LocalId(index as u32), local.clone()))
            .collect()
    }

    /// The name the machine is built from: the member's, or the unspeakable
    /// one the closure's method got.
    pub(crate) fn machine_name(&mut self, key: MachineKey) -> String {
        let symbols = self.compilation.symbols();
        let owner = symbols.get(key.owner()).name.clone();
        match key {
            MachineKey::Member(member) => self.metadata_method_name(member),
            MachineKey::Lambda {
                owner: member,
                index,
            } => self
                .lambda_names
                .get(&(member, index))
                .cloned()
                .unwrap_or_else(|| format!("<{owner}>b__{index}")),
            MachineKey::Function { .. } => {
                let symbol = self.machine_symbol(key);
                match symbol.and_then(|symbol| self.emitted_names.get(&symbol)) {
                    Some(name) => name.clone(),
                    None => {
                        let name = symbol
                            .map(|symbol| self.compilation.symbols().get(symbol).name.clone())
                            .unwrap_or_default();
                        format!("<{owner}>g__{name}")
                    }
                }
            }
        }
    }

    /// The name of a machine's class (Roslyn's `MakeStateMachineTypeName`):
    /// `<M>d__3`, numbered by where the member stands among its type's, and
    /// `<<M>b__0_0>d` for a lambda's or a local function's, whose method's
    /// name is unique already. A dot, which a type's name had better not
    /// carry, is written `-`.
    ///
    /// Roslyn nests a closure's machine in the class its method is a member
    /// of; one hosted in a display class is nested beside the member's here,
    /// where two such could share a name, and is numbered by its row.
    pub(crate) fn machine_type_name(&mut self, key: MachineKey, plan: &TypePlan) -> String {
        let name = self.machine_name(key).replace('.', "-");
        let name = match key {
            MachineKey::Member(member) => format!("<{name}>d__{}", self.member_ordinal(member)),
            _ if self.host_of(key).hosted.is_none() => format!("<{name}>d"),
            _ => format!("<{name}>d__{}", plan.token.0 & 0x00FF_FFFF),
        };
        // A machine declares the enclosing type's parameters again and
        // then the method's, and only those are its own: `<M>d__0`1` for
        // `M<T>`, as any generic type is named.
        let declared = self.display_parameters(plan).len();
        let inherited = self
            .compilation
            .symbols()
            .get(plan.symbol)
            .as_named_type()
            .map_or(0, |detail| detail.type_parameters.len());
        match declared.saturating_sub(inherited) {
            0 => name,
            own => format!("{name}`{own}"),
        }
    }

    /// Where the method making the machine lives.
    pub(crate) fn host_of(&self, key: MachineKey) -> ClosureHost {
        match key {
            MachineKey::Member(member) => ClosureHost {
                instance: !self
                    .compilation
                    .symbols()
                    .get(member)
                    .modifiers
                    .contains(Modifiers::STATIC),
                hosted: None,
            },
            _ => self
                .closure_hosts
                .get(&key)
                .cloned()
                .unwrap_or(ClosureHost {
                    instance: false,
                    hosted: None,
                }),
        }
    }

    /// Which builder the method's return type asks for, if any this backend
    /// knows.
    pub(crate) fn async_kind(&mut self, key: MachineKey) -> Option<AsyncKind> {
        let declared = self.machine_return(key);
        let Type::Named {
            symbol,
            type_arguments,
        } = &declared
        else {
            return matches!(declared, Type::Void).then_some(AsyncKind::Void);
        };
        let named = |emitter: &Self, name: &str| {
            emitter.compilation.type_by_metadata_name(name) == Some(*symbol)
        };
        if named(self, "System.Threading.Tasks.Task") {
            Some(AsyncKind::Task)
        } else if named(self, "System.Threading.Tasks.Task`1") {
            Some(AsyncKind::TaskOf(type_arguments.first()?.clone()))
        } else if named(self, "System.Threading.Tasks.ValueTask") {
            Some(AsyncKind::ValueTask)
        } else if named(self, "System.Threading.Tasks.ValueTask`1") {
            Some(AsyncKind::ValueTaskOf(type_arguments.first()?.clone()))
        } else if named(self, "System.Collections.Generic.IAsyncEnumerable`1")
            || named(self, "System.Collections.Generic.IAsyncEnumerator`1")
        {
            // What the body's `yield return`s give, which the binder read off
            // the same declaration.
            let element = self.yielded_element(key)?;
            Some(AsyncKind::Iterator {
                element,
                enumerable: named(self, "System.Collections.Generic.IAsyncEnumerable`1"),
            })
        } else {
            // A task-like type is built by the builder it names, over its own
            // type argument where it has one: `MyTask<T>` by
            // `MyTaskMethodBuilder<T>`.
            let builder = self.binder.async_method_builder(*symbol)?;
            Some(AsyncKind::Custom {
                task: declared.clone(),
                builder: Type::Named {
                    symbol: builder,
                    type_arguments: type_arguments.clone(),
                },
                result: type_arguments.first().cloned(),
            })
        }
    }

    /// The body as `MoveNext` runs it: every `await` moved to a statement of
    /// its own, so that nothing is on the stack when the machine stops.
    pub(crate) fn async_body(&mut self, key: MachineKey) -> Option<BoundBody> {
        if let Some(cached) = self.async_bodies.get(&key) {
            return cached.clone().ok();
        }
        let body = self.machine_body(key)?;
        let special = |emitter: &Self, which| {
            emitter
                .compilation
                .special_type(which)
                .map_or(Type::Error, Type::named)
        };
        let boolean = special(self, rustlyn_semantics::SpecialType::Boolean);
        let integer = special(self, rustlyn_semantics::SpecialType::Int32);
        let exception = self
            .compilation
            .type_by_metadata_name("System.Exception")
            .map_or(Type::Error, Type::named);
        // `ExceptionDispatchInfo.Throw(e)` rethrows with the stack trace `e`
        // was caught with, which a plain `throw e;` would replace.
        let rethrow = self
            .compilation
            .type_by_metadata_name("System.Runtime.ExceptionServices.ExceptionDispatchInfo")
            .and_then(|info| {
                let symbols = self.compilation.symbols();
                symbols.lookup(info, "Throw").iter().copied().find(|id| {
                    let symbol = symbols.get(*id);
                    symbol.modifiers.contains(Modifiers::STATIC)
                        && symbol
                            .as_method()
                            .is_some_and(|method| method.parameters.len() == 1)
                })
            });
        let nullable = self.compilation.type_by_metadata_name("System.Nullable`1");
        let iterator = matches!(self.async_kind(key), Some(AsyncKind::Iterator { .. }));
        let spilled = spill_awaits(
            body,
            boolean,
            integer,
            exception,
            rethrow,
            &|ty| self.is_ref_like(ty),
            nullable,
            self.compilation.symbols(),
            iterator,
        );
        self.async_bodies.insert(key, spilled.clone());
        spilled.ok()
    }

    /// Why a machine cannot be built for this member or closure, where it
    /// cannot.
    pub(crate) fn async_refusal(&mut self, key: MachineKey) -> Option<String> {
        let Some(kind) = self.async_kind(key) else {
            return Some(format!(
                "an `async` method returning `{}` needs a builder this backend does not know",
                self.machine_return(key).display(self.compilation.symbols())
            ));
        };
        let parameters = self.machine_parameters(key);
        if parameters
            .iter()
            .any(|parameter| self.is_by_reference(Some(*parameter)))
        {
            return Some(
                "an `async` method cannot take a parameter by reference: the machine holds it \
                 in a field, and a field may not be one"
                    .to_string(),
            );
        }
        let body = self.machine_body(key)?;
        let locals = self.machine_locals(key, &body);
        let mut held: Vec<Type> = parameters
            .iter()
            .map(|parameter| self.type_of(*parameter))
            .collect();
        held.extend(locals.iter().map(|(_, local)| local.ty.clone()));
        held.extend(kind.result().cloned());
        held.extend(kind.iterator().map(|(element, _)| element.clone()));
        let host = self.host_of(key);
        if host.instance
            && host.hosted.is_none()
            && let Some(container) = self.compilation.symbols().get(key.owner()).container
        {
            held.push(self.binder.self_type(container));
        }
        if held.iter().any(|ty| self.is_ref_like(ty)) {
            return Some(
                "an `async` method that would hold a `ref struct` cannot be built: a field may \
                 never be one"
                    .to_string(),
            );
        }
        self.async_body(key);
        match self.async_bodies.get(&key) {
            Some(Err(reason)) => Some(reason.clone()),
            _ => None,
        }
    }

    /// The builder as a type, constructed over the result where it is generic.
    fn builder_type(&self, kind: &AsyncKind) -> Option<Type> {
        if let AsyncKind::Custom { builder, .. } = kind {
            return Some(builder.clone());
        }
        let symbol = self
            .compilation
            .type_by_metadata_name(kind.builder_name()?)?;
        Some(Type::Named {
            symbol,
            type_arguments: kind.result().cloned().into_iter().collect(),
        })
    }

    /// A generic type as a member of its own names it, `MyTask<!0>`, or a
    /// type that is not generic as itself.
    fn own_sig(&mut self, ty: &Type, generic: bool) -> Option<SigType> {
        let definition = Type::named(ty.symbol()?);
        let value_type = self.is_value_type(&definition);
        let token = self.type_token(&definition).ok()?;
        let coded = type_def_or_ref(
            u32::from(token.0 >> 24 == u32::from(table::TYPE_REF)),
            token.0 & 0x00FF_FFFF,
        );
        Some(if generic {
            SigType::Constructed {
                value_type,
                coded,
                arguments: vec![SigType::TypeParameter(0)],
            }
        } else {
            SigType::Named { value_type, coded }
        })
    }

    /// The builder as a member of its own names it: `AsyncTaskMethodBuilder<!0>`.
    pub(crate) fn builder_self_sig(&mut self, kind: &AsyncKind) -> SigType {
        if let AsyncKind::Custom {
            builder, result, ..
        } = kind
            && let Some(sig) = self.own_sig(builder, result.is_some())
        {
            return sig;
        }
        let coded = self
            .references
            .type_ref_coded(&mut self.metadata, kind.builder_name().unwrap_or_default());
        if kind.result().is_some() {
            SigType::Constructed {
                value_type: true,
                coded,
                arguments: vec![SigType::TypeParameter(0)],
            }
        } else {
            SigType::Named {
                value_type: true,
                coded,
            }
        }
    }

    /// A member of the builder, with the definition's own signature.
    pub(crate) fn builder_member(
        &mut self,
        plan: &AsyncPlan,
        name: &str,
        signature: &[u8],
    ) -> Result<Token, EmitError> {
        if let AsyncKind::Custom { builder, .. } = &plan.kind {
            return self.custom_builder_member(builder, name);
        }
        if plan.kind.result().is_some() {
            self.member_of_type(&plan.builder_type, name, signature)
        } else {
            Ok(self.references.member_ref(
                &mut self.metadata,
                plan.kind.builder_name().unwrap_or_default(),
                name,
                signature,
            ))
        }
    }

    /// A member of a task-like type's builder, found by name on it as the
    /// pattern asks (§15.15.1): `get_Task` is its `Task` property's getter.
    fn custom_builder_member(&mut self, builder: &Type, name: &str) -> Result<Token, EmitError> {
        let missing = || EmitError::new(format!("the builder has no `{name}`"));
        let definition = builder.symbol().ok_or_else(missing)?;
        let symbols = self.compilation.symbols();
        if let Some(property) = name.strip_prefix("get_") {
            let property = symbols
                .lookup(definition, property)
                .iter()
                .copied()
                .find(|member| symbols.get(*member).kind == SymbolKind::Property)
                .ok_or_else(missing)?;
            return self.property_accessor(property, Some(builder), false);
        }
        let method = symbols
            .lookup(definition, name)
            .iter()
            .copied()
            .find(|member| symbols.get(*member).kind == SymbolKind::Method)
            .ok_or_else(missing)?;
        if matches!(builder, Type::Named { type_arguments, .. } if !type_arguments.is_empty()) {
            return self.member_of_constructed(method, builder);
        }
        match self.methods.get(&method) {
            Some(token) => Ok(*token),
            None => self.member_of_constructed(method, builder),
        }
    }

    /// A `MethodSpec` over a member, for the type arguments given as
    /// signatures — which is how a machine, that has no type of its own, is
    /// named as one.
    pub(crate) fn spec_of(&mut self, method: Token, arguments: &[SigType]) -> Token {
        let signature = method_spec_signature(arguments);
        let tag = u32::from(method.0 >> 24 == u32::from(table::MEMBER_REF));
        let coded = ((method.0 & 0x00FF_FFFF) << 1) | tag;
        self.metadata.add_method_spec(coded, &signature)
    }

    /// Plans the class a member's `await`s turn it into.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn plan_async(
        &mut self,
        key: MachineKey,
        enclosing: SymbolId,
        next_type: &mut u32,
        next_field: &mut u32,
        next_method: &mut u32,
    ) -> Result<Option<TypePlan>, EmitError> {
        let owner = key.owner();
        let Some(kind) = self.async_kind(key) else {
            return Ok(None);
        };
        let Some(body) = self.async_body(key) else {
            return Ok(None);
        };
        let Some(builder_type) = self.builder_type(&kind) else {
            return Ok(None);
        };
        let host = self.host_of(key);
        let instance = host.instance;

        let token = Token::new(table::TYPE_DEF, *next_type);
        *next_type += 1;

        let inherited = self
            .compilation
            .symbols()
            .get(enclosing)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        let (own, class_level) =
            self.machine_own_generics(key, inherited.len(), host.hosted.is_some());
        let coded = type_def_or_ref(0, token.0 & 0x00FF_FFFF);
        let generic = !inherited.is_empty() || !own.is_empty();
        // A closure hosted in a display class or a machine names the
        // method's parameters as that class's own, `!n`, since the class
        // declares them; a method of the type names its own as `!!n`, and so
        // does a local function the type parameters it declares itself.
        let outer_sig = if generic {
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
            SigType::Named {
                value_type: false,
                coded,
            }
        };
        let inner_sig = if generic {
            SigType::Constructed {
                value_type: false,
                coded,
                arguments: (0..(inherited.len() + own.len()) as u32)
                    .map(SigType::TypeParameter)
                    .collect(),
            }
        } else {
            outer_sig.clone()
        };

        let mut declared = inherited.clone();
        declared.extend(own.iter().copied());
        self.display_generics = declared;

        let integer = Type::named(
            self.compilation
                .special_type(rustlyn_semantics::SpecialType::Int32)
                .ok_or_else(|| EmitError::new("the compilation has no `System.Int32`"))?,
        );
        let mut fields = Vec::new();
        let mut field =
            |fields: &mut Vec<FieldPlan>, name: String, ty: Type, sig: Option<SigType>| {
                let token = Token::new(table::FIELD, *next_field);
                *next_field += 1;
                fields.push(FieldPlan {
                    token,
                    name,
                    ty,
                    flags: field_attributes::PUBLIC,
                    symbol: None,
                    constant: None,
                    sig,
                });
                token
            };
        let state = field(&mut fields, "<>1__state".to_string(), integer.clone(), None);
        let builder = field(
            &mut fields,
            "<>t__builder".to_string(),
            builder_type.clone(),
            None,
        );
        // `this` is the enclosing type's for a member; for a closure hosted
        // in a display class or a machine it is that object, which only a
        // signature names.
        let this_type =
            (instance && host.hosted.is_none()).then(|| self.binder.self_type(enclosing));
        let this = instance.then(|| match &host.hosted {
            Some(sig) => field(
                &mut fields,
                "<>4__this".to_string(),
                Type::Error,
                Some(sig.clone()),
            ),
            None => field(
                &mut fields,
                "<>4__this".to_string(),
                self.binder.self_type(enclosing),
                None,
            ),
        });
        let declared_parameters = self.machine_parameters(key);
        let mut parameters = HashMap::new();
        let mut order = Vec::new();
        for parameter in &declared_parameters {
            let name = self.compilation.symbols().get(*parameter).name.clone();
            let ty = self.type_of(*parameter);
            let token = field(&mut fields, name, ty, None);
            parameters.insert(*parameter, token);
            order.push((*parameter, token));
        }
        let held_locals = self.machine_locals(key, &body);
        let parameter_locals = self.machine_parameter_locals(key);
        // What a closure of the body reads lives here for it: the machine is
        // its display class. Where the body has closures, which reach the
        // fields of machines of their own too, every field stays public;
        // otherwise the locals are private, as Roslyn's are.
        let closures = !body.lambdas.is_empty() || !body.local_functions.is_empty();
        let captured: std::collections::HashSet<LocalId> = body
            .lambdas
            .iter()
            .flat_map(|lambda| lambda.captured.iter().copied())
            .chain(
                body.local_functions
                    .iter()
                    .flat_map(|function| function.captured.iter().copied()),
            )
            .collect();
        // The fields Roslyn gives the locals that outlast a suspension, by
        // its names; any other local is a field of its own, named after its
        // place in the body's table.
        let candidates: Vec<(LocalId, LocalSymbol)> = held_locals
            .iter()
            .filter(|(_, local)| local.name != DISPOSE_MODE)
            .cloned()
            .collect();
        let taken: std::collections::HashSet<String> =
            fields.iter().map(|field| field.name.clone()).collect();
        let hoisted = crate::hoisting::hoist(
            &body,
            &body.statements,
            &candidates,
            &captured,
            self.compilation.options().optimize,
            false,
            &taken,
        );
        let mut tokens = Vec::with_capacity(hoisted.fields.len());
        for (at, (name, ty)) in hoisted.fields.iter().enumerate() {
            let token = field(&mut fields, name.clone(), ty.clone(), None);
            let shared = hoisted
                .field_of
                .iter()
                .any(|(local, field)| *field == at && captured.contains(local));
            if !shared
                && !closures
                && let Some(plan) = fields.last_mut()
            {
                plan.flags = field_attributes::PRIVATE;
            }
            tokens.push(token);
        }
        let finished_cleared: Vec<(LocalId, Type)> = held_locals
            .iter()
            .filter(|(id, local)| {
                !captured.contains(id)
                    && local.name != DISPOSE_MODE
                    && self.might_hold_references(&local.ty, 0)
            })
            .map(|(id, local)| (*id, local.ty.clone()))
            .collect();
        let cleared: Vec<(LocalId, Type)> = finished_cleared
            .iter()
            .filter(|(id, _)| {
                body.locals
                    .get(id.0 as usize)
                    .is_some_and(|local| !local.name.starts_with('<'))
            })
            .cloned()
            .collect();
        let root: &[BoundStatement] = match &body.statements[..] {
            [
                BoundStatement {
                    kind: BoundStatementKind::Block(inner),
                    ..
                },
            ] => inner,
            all => all,
        };
        let root_cleared: Vec<(LocalId, Type)> = root
            .iter()
            .filter_map(|statement| match &statement.kind {
                BoundStatementKind::LocalDeclaration { local, .. } => {
                    cleared.iter().find(|(id, _)| id == local).cloned()
                }
                _ => None,
            })
            .collect();
        let mut locals = HashMap::new();
        let mut local_fields: Vec<(LocalId, String, Type)> = Vec::new();
        for (id, local) in &held_locals {
            if let Some(at) = hoisted.field_of.get(id) {
                locals.insert(*id, tokens[*at]);
                let (name, ty) = &hoisted.fields[*at];
                local_fields.push((*id, name.clone(), ty.clone()));
                continue;
            }
            let name = hoisted_name(*id, local);
            let token = field(&mut fields, name.clone(), local.ty.clone(), None);
            if !captured.contains(id)
                && !closures
                && local.name != DISPOSE_MODE
                && let Some(plan) = fields.last_mut()
            {
                plan.flags = field_attributes::PRIVATE;
            }
            locals.insert(*id, token);
            local_fields.push((*id, name, local.ty.clone()));
        }
        // One field per awaiter type: two `await`s on a `Task<int>` share
        // `<>u__1`, since only one of them is ever pending.
        let mut awaiter_types: Vec<Type> = Vec::new();
        collect_awaiters(&body.statements, &mut awaiter_types);
        let mut awaiters = Vec::new();
        for (number, ty) in awaiter_types.iter().enumerate() {
            let token = field(
                &mut fields,
                format!("<>u__{}", number + 1),
                ty.clone(),
                None,
            );
            awaiters.push((ty.clone(), token));
        }
        // A loop body with a class of its own keeps that class in a field
        // here, named after where the body starts; what the class is called
        // is filled in once it has been planned.
        let mut scopes = HashMap::new();
        let mut scope_names = Vec::new();
        for span in self.machine_scopes(key) {
            let name = format!("<>8__s{}", span.start());
            let token = field(
                &mut fields,
                name.clone(),
                Type::Error,
                Some(SigType::Primitive(ElementType::Object)),
            );
            scopes.insert(span, token);
            scope_names.push((span, name));
        }
        // An `async` iterator's own fields, after everything an `async`
        // method's machine keeps.
        let mut iterator_fields = Vec::new();
        let iterator = match kind.iterator() {
            Some((element, enumerable)) => {
                let element = element.clone();
                let mut own = |fields: &mut Vec<FieldPlan>, name: String, ty: Type| {
                    iterator_fields.push((name.clone(), ty.clone()));
                    field(fields, name, ty, None)
                };
                let promise = own(
                    &mut fields,
                    "<>v__promiseOfValueOrEnd".to_string(),
                    self.promise_type()?,
                );
                let current = own(&mut fields, "<>2__current".to_string(), element.clone());
                let thread = enumerable.then(|| {
                    own(
                        &mut fields,
                        "<>l__initialThreadId".to_string(),
                        integer.clone(),
                    )
                });
                let token_type =
                    self.framework_type("System.Threading.CancellationToken", Vec::new())?;
                let symbols = self.compilation.symbols();
                let cancellation = declared_parameters.iter().copied().find(|parameter| {
                    enumerable
                        && symbols
                            .get(*parameter)
                            .as_parameter()
                            .is_some_and(|detail| detail.enumerator_cancellation)
                });
                let cancellation =
                    cancellation.filter(|parameter| self.type_of(*parameter) == token_type);
                let combined = match cancellation {
                    Some(_) => Some(own(
                        &mut fields,
                        "<>x__combinedTokens".to_string(),
                        self.framework_type(
                            "System.Threading.CancellationTokenSource",
                            Vec::new(),
                        )?,
                    )),
                    None => None,
                };
                let mut proxies = Vec::new();
                if enumerable {
                    for parameter in &declared_parameters {
                        let name = self.compilation.symbols().get(*parameter).name.clone();
                        let ty = self.type_of(*parameter);
                        proxies.push((*parameter, own(&mut fields, format!("<>3__{name}"), ty)));
                    }
                }
                let Some(dispose_mode) = held_locals
                    .iter()
                    .find(|(_, local)| local.name == DISPOSE_MODE)
                    .map(|(id, _)| *id)
                else {
                    return Err(EmitError::new(
                        "an `async` iterator whose body has no dispose mode",
                    ));
                };
                Some(AsyncIteratorPlan {
                    element,
                    enumerable,
                    promise,
                    current,
                    dispose_mode,
                    thread,
                    combined,
                    outer_proxies: proxies.clone(),
                    proxies,
                    cancellation,
                })
            }
            None => None,
        };
        // An `async` iterator stops at its `yield return`s as well as at its
        // `await`s.
        let (sites, regions) = if iterator.is_some() {
            collect_sites(&body.statements, &|statement| {
                awaits_directly(statement) || yields_directly(statement)
            })
        } else {
            collect_sites(&body.statements, &awaits_directly)
        };

        let mut methods = Vec::new();
        let mut method = |methods: &mut Vec<MethodPlan>,
                          source: MethodSource,
                          name: &str,
                          flags: u16,
                          returns: Type,
                          parameters: Vec<ParameterPlan>,
                          signature: Option<Vec<u8>>| {
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
                signature,
            });
            token
        };
        let void = SigType::Primitive(ElementType::Void);
        let sealed_virtual = method_attributes::PUBLIC
            | method_attributes::HIDE_BY_SIG
            | method_attributes::VIRTUAL
            | method_attributes::NEW_SLOT
            | method_attributes::FINAL;
        let constructor_flags = method_attributes::PUBLIC
            | method_attributes::HIDE_BY_SIG
            | method_attributes::SPECIAL_NAME
            | method_attributes::RT_SPECIAL_NAME;
        // An iterator's machine is made in the state it starts in.
        let constructor = if iterator.is_some() {
            method(
                &mut methods,
                MethodSource::AsyncIteratorConstructor(key),
                ".ctor",
                constructor_flags,
                Type::Void,
                vec![ParameterPlan {
                    symbol: None,
                    name: "<>1__state".to_string(),
                    ty: Type::Error,
                    by_ref: false,
                }],
                Some(method_signature(
                    true,
                    &void,
                    &[SigType::Primitive(ElementType::I4)],
                )),
            )
        } else {
            method(
                &mut methods,
                MethodSource::AsyncConstructor,
                ".ctor",
                constructor_flags,
                Type::Void,
                Vec::new(),
                Some(method_signature(true, &void, &[])),
            )
        };
        method(
            &mut methods,
            MethodSource::AsyncMoveNext(key),
            "MoveNext",
            sealed_virtual,
            Type::Void,
            Vec::new(),
            Some(method_signature(true, &void, &[])),
        );
        let state_machine = SigType::Named {
            value_type: false,
            coded: self.references.type_ref_coded(
                &mut self.metadata,
                "System.Runtime.CompilerServices.IAsyncStateMachine",
            ),
        };
        method(
            &mut methods,
            MethodSource::AsyncSetStateMachine,
            "SetStateMachine",
            sealed_virtual,
            Type::Void,
            vec![ParameterPlan {
                symbol: None,
                name: "stateMachine".to_string(),
                ty: Type::Error,
                by_ref: false,
            }],
            Some(method_signature(true, &void, &[state_machine])),
        );
        if let Some(iterator) = &iterator {
            for (source, name, flags, returns, parameters) in
                self.async_iterator_methods(key, iterator)?
            {
                method(
                    &mut methods,
                    source,
                    &name,
                    flags,
                    returns,
                    parameters,
                    None,
                );
            }
        }

        let (locals_view, parameters_view, inner_sig_view) =
            (locals.clone(), parameters.clone(), inner_sig.clone());
        self.asyncs.insert(
            key,
            AsyncPlan {
                cleared,
                root_cleared,
                finished_cleared,
                kind,
                builder_type: builder_type.clone(),
                outer_sig,
                inner_sig,
                constructor,
                outer_constructor: constructor,
                state,
                outer_state: state,
                builder,
                outer_builder: builder,
                this,
                outer_this: this,
                parameters,
                order: order.clone(),
                outer_order: order,
                outer_locals: locals.clone(),
                locals,
                parameter_locals,
                hosted: host.hosted.is_some(),
                awaiters: awaiters.clone(),
                sites,
                regions,
                scopes,
                iterator,
            },
        );
        if generic {
            let held = this_type;
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
            self.async_pending.push(PendingAsync {
                key,
                token,
                arity: inherited.len(),
                own: own.len(),
                builder: builder_type,
                this: held,
                this_sig: instance.then(|| host.hosted.clone()).flatten(),
                class_level,
                order: named,
                locals: local_fields,
                awaiters: awaiters
                    .iter()
                    .enumerate()
                    .map(|(number, (ty, _))| (ty.clone(), format!("<>u__{}", number + 1)))
                    .collect(),
                scopes: scope_names,
                iterator: iterator_fields,
            });
        }
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
        // The lambdas of a member's body are methods of the machine, which
        // is the display class for them. A closure's own lambdas stay where
        // the member put them.
        if matches!(key, MachineKey::Member(_)) {
            let view = DisplayView {
                constructor,
                locals: locals_view,
                parameters: parameters_view,
                this,
                ..DisplayView::default()
            };
            self.attach_closures(
                owner,
                &mut plan,
                inner_sig_view,
                view,
                inherited.len(),
                own.len(),
                next_field,
                next_method,
            )?;
        }
        Ok(Some(plan))
    }

    /// The rows of one machine: the type, `IAsyncStateMachine`, its members.
    pub(crate) fn write_async_type(
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
        // The constraints are the machine's to state, in its own parameters:
        // `where T : IList<U>` on the method names `!!1`, and on the machine
        // made over it `!1` — as a display class's are.
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
        let interface = self.references.type_ref_coded(
            &mut self.metadata,
            "System.Runtime.CompilerServices.IAsyncStateMachine",
        );
        self.metadata.add_interface_impl(token, interface);
        self.display_generics = inherited;
        let iterator = self
            .asyncs
            .get(&key)
            .and_then(|machine| machine.iterator.clone());
        if let Some(iterator) = iterator {
            let written = self.write_async_iterator_interfaces(plan, key, &iterator);
            if written.is_err() {
                self.display_generics = Vec::new();
            }
            written?;
        }
        let written = self.write_members(plan, type_offsets);
        self.display_generics = Vec::new();
        written
    }

    /// Names the members of every machine that sits in a generic type or
    /// belongs to a generic method, as the method that makes one has to.
    pub(crate) fn resolve_async_members(&mut self) -> Result<(), EmitError> {
        for pending in std::mem::take(&mut self.async_pending) {
            let outer = SigType::Constructed {
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
            let inner = SigType::Constructed {
                value_type: false,
                coded: type_def_or_ref(0, pending.token.0 & 0x00FF_FFFF),
                arguments: (0..(pending.arity + pending.own) as u32)
                    .map(SigType::TypeParameter)
                    .collect(),
            };
            let mut blob = Vec::new();
            outer.write(&mut blob);
            let outer = self.references.type_spec(&mut self.metadata, &blob);
            let mut blob = Vec::new();
            inner.write(&mut blob);
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
            // An `async` iterator's machine is made in the state it starts in.
            let made = if pending.iterator.is_empty() {
                method_signature(true, &SigType::Primitive(ElementType::Void), &[])
            } else {
                method_signature(
                    true,
                    &SigType::Primitive(ElementType::Void),
                    &[SigType::Primitive(ElementType::I4)],
                )
            };
            // Its own fields, by name, as each construction names them.
            let mut named_views = Vec::new();
            for spec in [outer, inner] {
                let mut named = HashMap::new();
                for (name, ty) in &pending.iterator {
                    named.insert(name.clone(), self.display_field(spec, name, ty)?);
                }
                named_views.push(named);
            }
            let mut views = Vec::new();
            for spec in [outer, inner] {
                let constructor =
                    self.references
                        .member_of_spec(&mut self.metadata, spec, ".ctor", &made);
                let state = self.display_field(spec, "<>1__state", &integer)?;
                let builder = self.display_field(spec, "<>t__builder", &pending.builder)?;
                let held = match (&pending.this, &pending.this_sig) {
                    (Some(ty), _) => Some(self.display_field(spec, "<>4__this", ty)?),
                    (None, Some(sig)) => Some(self.display_field_sig(spec, "<>4__this", sig)),
                    (None, None) => None,
                };
                let mut order = Vec::new();
                for (parameter, name, ty) in &pending.order {
                    order.push((*parameter, self.display_field(spec, name, ty)?));
                }
                let mut locals = HashMap::new();
                for (local, name, ty) in &pending.locals {
                    locals.insert(*local, self.display_field(spec, name, ty)?);
                }
                let mut awaiters = Vec::new();
                for (ty, name) in &pending.awaiters {
                    awaiters.push((ty.clone(), self.display_field(spec, name, ty)?));
                }
                let mut scopes = HashMap::new();
                for (span, name) in &pending.scopes {
                    let Some(sig) = self
                        .nested_displays
                        .get(&(pending.key.owner(), Closure::Scope(*span)))
                        .map(|display| display.inner_sig.clone())
                    else {
                        continue;
                    };
                    scopes.insert(*span, self.display_field_sig(spec, name, &sig));
                }
                views.push((
                    constructor,
                    state,
                    builder,
                    held,
                    order,
                    locals,
                    awaiters,
                    scopes,
                ));
            }
            self.display_generics = Vec::new();
            let inside = views.pop().expect("both views were built");
            let outside = views.pop().expect("both views were built");
            if let Some(plan) = self.asyncs.get_mut(&pending.key) {
                plan.outer_constructor = outside.0;
                plan.outer_state = outside.1;
                plan.outer_builder = outside.2;
                plan.outer_this = outside.3;
                plan.outer_order = outside.4;
                plan.outer_locals = outside.5;
                plan.constructor = inside.0;
                plan.state = inside.1;
                plan.builder = inside.2;
                plan.this = inside.3;
                plan.parameters = inside.4.iter().copied().collect();
                plan.order = inside.4;
                plan.locals = inside.5;
                plan.awaiters = inside.6;
                plan.scopes = inside.7;
                let named_inside = named_views.pop().unwrap_or_default();
                let named_outside = named_views.pop().unwrap_or_default();
                if let Some(iterator) = &mut plan.iterator {
                    let symbols = self.compilation.symbols();
                    let field = |named: &HashMap<String, Token>, name: &str, was: Token| {
                        named.get(name).copied().unwrap_or(was)
                    };
                    iterator.promise =
                        field(&named_inside, "<>v__promiseOfValueOrEnd", iterator.promise);
                    iterator.current = field(&named_inside, "<>2__current", iterator.current);
                    iterator.thread = iterator
                        .thread
                        .map(|was| field(&named_inside, "<>l__initialThreadId", was));
                    iterator.combined = iterator
                        .combined
                        .map(|was| field(&named_inside, "<>x__combinedTokens", was));
                    let proxy =
                        |named: &HashMap<String, Token>, (parameter, was): (SymbolId, Token)| {
                            let name = format!("<>3__{}", symbols.get(parameter).name);
                            (parameter, field(named, &name, was))
                        };
                    iterator.outer_proxies = iterator
                        .outer_proxies
                        .iter()
                        .map(|entry| proxy(&named_outside, *entry))
                        .collect();
                    iterator.proxies = iterator
                        .proxies
                        .iter()
                        .map(|entry| proxy(&named_inside, *entry))
                        .collect();
                }
            }
            // A member's machine is its lambdas' display class, and they
            // read the fields under the same names.
            if let MachineKey::Member(owner) = pending.key
                && let Some(plan) = self.asyncs.get(&pending.key).cloned()
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

    /// The type parameters a machine declares: the enclosing type's, then the
    /// method's own.
    pub(crate) fn machine_generics(&mut self, key: MachineKey) -> Vec<SymbolId> {
        let owner = key.owner();
        let function = self.function_generics(key);
        let symbols = self.compilation.symbols();
        let mut all = symbols
            .get(owner)
            .container
            .and_then(|container| symbols.get(container).as_named_type())
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        all.extend(
            symbols
                .get(owner)
                .as_method()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default(),
        );
        all.extend(function);
        all
    }

    /// The type parameters a local function declares itself, which its
    /// machine declares after the owner's.
    pub(crate) fn function_generics(&mut self, key: MachineKey) -> Vec<SymbolId> {
        if !matches!(key, MachineKey::Function { .. }) {
            return Vec::new();
        }
        self.machine_symbol(key)
            .and_then(|symbol| {
                self.compilation
                    .symbols()
                    .get(symbol)
                    .as_method()
                    .map(|detail| detail.type_parameters.clone())
            })
            .unwrap_or_default()
    }

    /// A machine's type parameters after the enclosing type's — the owner's,
    /// then a local function's own — and how many of all of them the method
    /// making it names as its class's (see [`PendingAsync::class_level`]).
    pub(crate) fn machine_own_generics(
        &mut self,
        key: MachineKey,
        inherited: usize,
        hosted: bool,
    ) -> (Vec<SymbolId>, usize) {
        let mut own = self
            .compilation
            .symbols()
            .get(key.owner())
            .as_method()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        let class_level = if hosted {
            inherited + own.len()
        } else {
            inherited
        };
        own.extend(self.function_generics(key));
        (own, class_level)
    }
}

impl BodyEmitter<'_, '_> {
    /// The method the source wrote: make a machine, fill it, start it, and
    /// hand back the builder's task.
    pub(crate) fn emit_async_start(&mut self, key: MachineKey) -> Result<(), EmitError> {
        let Some(plan) = self.emitter.asyncs.get(&key).cloned() else {
            return Err(EmitError::new("a state machine with no plan"));
        };
        // An `async` iterator is not started: it is handed back, for its
        // `MoveNextAsync` to start.
        if plan.iterator.is_some() {
            return self.emit_async_iterator_start(&plan);
        }
        let slot = self.locals.len() as u16;
        self.locals.push(plan.outer_sig.clone());
        self.local_types.push(Type::Error);

        self.stream
            .call_effect(Instruction::NewObject(plan.outer_constructor), 0, 1);
        self.stream.emit(Instruction::StoreLocal(slot));
        if let Some(field) = plan.outer_this {
            self.stream.emit(Instruction::LoadLocal(slot));
            self.push_this_value()?;
            self.stream.emit(Instruction::StoreField(field));
        }
        for (parameter, field) in &plan.outer_order {
            let index = self.argument_index(*parameter)?;
            self.stream.emit(Instruction::LoadLocal(slot));
            self.stream.emit(Instruction::LoadArgument(index));
            self.stream.emit(Instruction::StoreField(*field));
        }
        // A lambda's parameters are locals of the body, and arrive as the
        // arguments of the method the lambda became.
        let base = u16::from(self.instance);
        for (position, local) in plan.parameter_locals.iter().enumerate() {
            let Some(field) = plan.outer_locals.get(local).copied() else {
                return Err(EmitError::new(
                    "a lambda parameter the machine has no field for",
                ));
            };
            self.stream.emit(Instruction::LoadLocal(slot));
            self.stream
                .emit(Instruction::LoadArgument(position as u16 + base));
            self.stream.emit(Instruction::StoreField(field));
        }
        // `<>t__builder = Builder.Create()`, and `-1` for "running".
        let builder_self = self.emitter.builder_self_sig(&plan.kind);
        let create = self.emitter.builder_member(
            &plan,
            "Create",
            &method_signature(false, &builder_self, &[]),
        )?;
        self.stream.emit(Instruction::LoadLocal(slot));
        self.stream.call_effect(Instruction::Call(create), 0, 1);
        self.stream
            .emit(Instruction::StoreField(plan.outer_builder));
        self.stream.emit(Instruction::LoadLocal(slot));
        self.stream.emit(Instruction::LoadInt32(-1));
        self.stream.emit(Instruction::StoreField(plan.outer_state));
        // `<>t__builder.Start(ref machine)`, which runs `MoveNext` once.
        let void = SigType::Primitive(ElementType::Void);
        let start = self.emitter.builder_member(
            &plan,
            "Start",
            &generic_method_signature(
                true,
                1,
                &void,
                &[SigType::ByRef(Box::new(SigType::MethodTypeParameter(0)))],
            ),
        )?;
        let start = self
            .emitter
            .spec_of(start, std::slice::from_ref(&plan.outer_sig));
        self.stream.emit(Instruction::LoadLocal(slot));
        self.stream
            .emit(Instruction::LoadFieldAddress(plan.outer_builder));
        self.stream.emit(Instruction::LoadLocalAddress(slot));
        self.stream.call_effect(Instruction::Call(start), 2, 0);
        // What the caller gets is the builder's task.
        if let Some(task) = plan.kind.task_sig(self.emitter) {
            let get_task = self.emitter.builder_member(
                &plan,
                "get_Task",
                &method_signature(true, &task, &[]),
            )?;
            self.stream.emit(Instruction::LoadLocal(slot));
            self.stream
                .emit(Instruction::LoadFieldAddress(plan.outer_builder));
            self.stream.call_effect(Instruction::Call(get_task), 1, 1);
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `.ctor()`: chain to `object`.
    pub(crate) fn emit_async_constructor(&mut self) {
        let object = self.emitter.framework_member(
            "System.Object",
            ".ctor",
            true,
            &SigType::Primitive(ElementType::Void),
            &[],
        );
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.call_effect(Instruction::Call(object), 1, 0);
        self.stream.emit(Instruction::Ret);
    }

    /// The start of `MoveNext`: the machine is the display class the body
    /// reads its variables from, the whole body sits in a `try`, and the
    /// state says where to carry on.
    pub(crate) fn begin_async_move_next(&mut self, key: MachineKey) -> Result<(), EmitError> {
        let Some(plan) = self.emitter.asyncs.get(&key).cloned() else {
            return Err(EmitError::new("a state machine with no plan"));
        };
        if self.display.is_none() {
            self.display = Some((
                DisplayClass {
                    sig: plan.inner_sig.clone(),
                    inner_sig: plan.inner_sig.clone(),
                    parent_closure: None,
                    generics: Vec::new(),
                    inside: DisplayView {
                        constructor: plan.constructor,
                        locals: plan.locals.clone(),
                        parameters: plan.parameters.clone(),
                        // A hosted closure's `<>4__this` is the display
                        // class, not what the body calls `this`: that is
                        // reached through the class, from the slot below.
                        this: if plan.hosted { None } else { plan.this },
                        ..DisplayView::default()
                    },
                    outside: DisplayView::default(),
                },
                DisplayAt::This,
            ));
        }
        let machine_slot = self.locals.len() as u16;
        self.locals.push(plan.inner_sig.clone());
        self.local_types.push(Type::Error);
        let result_slot = match plan.kind.result() {
            Some(result) => Some(self.temporary(result)?),
            None => None,
        };
        let done = self.stream.label();
        let finished = self.stream.label();

        // `int state = this.<>1__state;`
        let integer = self
            .emitter
            .compilation
            .special_type(rustlyn_semantics::SpecialType::Int32)
            .map(Type::named)
            .ok_or_else(|| EmitError::new("the compilation has no `System.Int32`"))?;
        let state_slot = self.temporary(&integer)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(plan.state));
        self.stream.emit(Instruction::StoreLocal(state_slot));

        let try_start = self.stream.label();
        self.stream.mark(try_start);
        self.protected += 1;
        self.exit = Some((done, result_slot));
        // An `async` iterator's `yield return`s count down from -4 beside
        // its `await`s.
        let iterating = plan.iterator.is_some();
        self.begin_machine(
            plan.state,
            state_slot,
            0,
            iterating.then_some(FIRST_YIELD_STATE),
            plan.sites.clone(),
            plan.regions,
        );
        let yielded = iterating.then(|| self.stream.label());
        self.async_run = Some(AsyncRun {
            plan,
            machine_slot,
            done,
            finished,
            result_slot,
            yielded,
        });
        self.async_try_start = Some(try_start);
        self.emit_machine_dispatch(&[])?;
        // Whatever state found no suspension to resume — `-3`, a walk just
        // asked for — starts the body, which is running from here on.
        if iterating {
            self.set_machine_state(-1);
        }
        Ok(())
    }

    /// Sets up the shared part of a machine's `MoveNext`.
    ///
    /// The suspensions are numbered from `state_base` in the order the walk
    /// meets them, except the `yield return`s of an `async` iterator, which
    /// count down from `yield_base` beside its `await`s.
    pub(crate) fn begin_machine(
        &mut self,
        state: Token,
        state_slot: u16,
        state_base: i32,
        yield_base: Option<i32>,
        sites: Vec<AwaitSite>,
        regions: usize,
    ) {
        let resume: Vec<Label> = sites.iter().map(|_| self.stream.label()).collect();
        let entries: Vec<Label> = (0..regions).map(|_| self.stream.label()).collect();
        let (mut awaited, mut yielded) = (state_base, yield_base.unwrap_or_default());
        let states = sites
            .iter()
            .map(|site| match yield_base {
                Some(_) if site.yields => {
                    yielded -= 1;
                    yielded + 1
                }
                _ => {
                    awaited += 1;
                    awaited - 1
                }
            })
            .collect();
        self.machine = Some(MachineRun {
            state,
            state_slot,
            states,
            sites,
            resume,
            entries,
            next_site: 0,
            next_region: 0,
            region_path: Vec::new(),
        });
    }

    /// The dispatch for the suspensions whose path of regions is `path`: the
    /// ones directly here resume, and the ones deeper in branch to the next
    /// region on their way, whose own dispatch takes it from there.
    pub(crate) fn emit_machine_dispatch(&mut self, path: &[usize]) -> Result<(), EmitError> {
        let Some(run) = &self.machine else {
            return Ok(());
        };
        let state_slot = run.state_slot;
        let state_field = run.state;
        let mut targets = Vec::new();
        for (number, site) in run.sites.iter().enumerate() {
            if !site.regions.starts_with(path) {
                continue;
            }
            let target = match site.regions.get(path.len()) {
                None => run.resume[number],
                Some(next) => run.entries[*next],
            };
            targets.push((run.states[number], target));
        }
        for (state, target) in targets {
            // The dispatch at the top reads the state it was entered with;
            // one at a region's entry reads the field, which a resume set
            // back to `-1` — a loop enters the region again and again, and
            // must not find the old state still waiting in the slot.
            if path.is_empty() {
                self.stream.emit(Instruction::LoadLocal(state_slot));
            } else {
                self.stream.emit(Instruction::LoadArgument(0));
                self.stream.emit(Instruction::LoadField(state_field));
            }
            self.stream.emit(Instruction::LoadInt32(state));
            self.stream.emit(Instruction::CompareEqual);
            self.stream.emit(Instruction::BranchIfTrue(target));
        }
        Ok(())
    }

    /// The next suspension's state and resume label, in the order the walk
    /// meets them.
    pub(crate) fn next_suspension(&mut self) -> Result<(i32, Label), EmitError> {
        let Some(run) = &mut self.machine else {
            return Err(EmitError::new(
                "a suspension outside the state machine it belongs to",
            ));
        };
        let number = run.next_site;
        run.next_site += 1;
        let (Some(label), Some(state)) = (
            run.resume.get(number).copied(),
            run.states.get(number).copied(),
        ) else {
            return Err(EmitError::new("more suspensions than were counted"));
        };
        Ok((state, label))
    }

    /// The first instruction of a protected region, whose `starts` are marked
    /// here: where a machine that stopped inside it comes back in.
    ///
    /// The dispatch outside branches to a `nop` just before the region rather
    /// than to its first instruction, as `csc` does. A branch to the start of
    /// a `try` is valid IL, but when two regions begin at the same instruction
    /// (a `try` with both catches and a `finally`) the JIT miscompiles it into
    /// a crash.
    pub(crate) fn emit_region_entry(&mut self, starts: &[Label]) -> Result<(), EmitError> {
        let Some(run) = &mut self.machine else {
            // `L: try { ... goto L; }` leaves to the label, and a label on
            // the region's first instruction is inside the region: the
            // `leave` would stay in it and skip the `finally`. A `nop` in
            // front keeps the two apart wherever a label may be waiting.
            if !self.labels.is_empty() {
                self.stream.emit(Instruction::Nop);
            }
            for &start in starts {
                self.stream.mark(start);
            }
            return Ok(());
        };
        let number = run.next_region;
        run.next_region += 1;
        let Some(label) = run.entries.get(number).copied() else {
            return Err(EmitError::new(
                "`MoveNext` entered more protected regions than were counted",
            ));
        };
        run.region_path.push(number);
        let path = run.region_path.clone();
        self.stream.mark(label);
        self.stream.emit(Instruction::Nop);
        for &start in starts {
            self.stream.mark(start);
        }
        self.emit_machine_dispatch(&path)
    }

    /// The start of a `finally` in a machine: a `leave` on the way out to
    /// suspend runs the handlers of every region it leaves, and the body has
    /// not finished, so the handler is skipped unless the machine is running
    /// — its state is `-1` — or done (§15.15, as C# compilers write it).
    ///
    /// An async machine asks the copy of the state in its local, as `csc`
    /// does, and not the field: once it has handed itself to an awaiter on
    /// the way out, another thread may already be running it and have set
    /// the field back to `-1`, and the `finally` would run on both.
    pub(crate) fn begin_guarded_finally(&mut self) -> Option<Label> {
        let run = self.machine.as_ref()?;
        let (state, slot) = (run.state, run.state_slot);
        let skip = self.stream.label();
        // An `async` iterator stopped at a `yield return` is in a negative
        // state too, so only `-1` — running — runs its `finally`s
        // (Roslyn's `ShouldEnterFinallyBlock`).
        let iterating = self
            .async_run
            .as_ref()
            .is_some_and(|run| run.plan.iterator.is_some());
        if self.async_run.is_some() {
            self.stream.emit(Instruction::LoadLocal(slot));
        } else {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(state));
        }
        if iterating {
            self.stream.emit(Instruction::LoadInt32(-1));
            self.stream.emit(Instruction::CompareEqual);
        } else {
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.emit(Instruction::CompareLess);
        }
        self.stream.emit(Instruction::BranchIfFalse(skip));
        Some(skip)
    }

    /// `this.<>1__state = state = value;` in an `async` machine's `MoveNext`.
    pub(crate) fn set_machine_state(&mut self, value: i32) {
        let Some(field) = self.machine.as_ref().map(|run| run.state) else {
            return;
        };
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(value));
        self.keep_state_local();
        self.stream.emit(Instruction::StoreField(field));
    }

    /// Keeps the state local of an async `MoveNext` in step with the value
    /// on the stack, which is about to be stored in the field.
    fn keep_state_local(&mut self) {
        if let Some(run) = &self.machine {
            let slot = run.state_slot;
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::StoreLocal(slot));
        }
    }

    /// The end of such a handler's body.
    pub(crate) fn end_guarded_finally(&mut self, skip: Option<Label>) {
        if let Some(skip) = skip {
            self.stream.mark(skip);
        }
    }

    /// The end of a protected region's body, on the way out.
    pub(crate) fn emit_region_exit(&mut self) {
        if let Some(run) = &mut self.machine {
            run.region_path.pop();
        }
    }

    /// The end of `MoveNext`: falling off the body is done, an exception is
    /// the builder's, and either way the state says the machine is finished.
    pub(crate) fn end_async_move_next(&mut self) -> Result<(), EmitError> {
        let Some(run) = self.async_run.take() else {
            return Ok(());
        };
        let Some(try_start) = self.async_try_start.take() else {
            return Ok(());
        };
        self.machine = None;
        self.exit = None;
        let plan = run.plan;
        let void = SigType::Primitive(ElementType::Void);

        self.stream.emit(Instruction::Leave(run.done));
        self.protected -= 1;
        let try_end = self.stream.label();
        self.stream.mark(try_end);

        // `catch (Exception e) { state = -2; builder.SetException(e); return; }`
        let exception = self
            .emitter
            .compilation
            .type_by_metadata_name("System.Exception")
            .map(Type::named)
            .ok_or_else(|| EmitError::new("the compilation has no `System.Exception`"))?;
        let exception_token = self.emitter.type_token(&exception)?;
        let exception_slot = self.temporary(&exception)?;
        let exception_sig = self.emitter.sig_type(&exception)?;
        let handler_start = self.stream.label();
        let handler_end = self.stream.label();
        self.stream.mark_handler(handler_start, 1);
        self.stream.emit(Instruction::StoreLocal(exception_slot));
        if plan.iterator.is_some() {
            // An `async` iterator's builder only completes; what it throws
            // goes to whoever waits on the promise.
            self.finish_async_iterator(&plan)?;
            self.fail_promise(&plan, exception_slot)?;
        } else {
            let set_exception = self.emitter.builder_member(
                &plan,
                "SetException",
                &method_signature(true, &void, &[exception_sig]),
            )?;
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadInt32(-2));
            self.stream.emit(Instruction::StoreField(plan.state));
            self.clear_fields(&plan.root_cleared, &plan.locals)?;
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream
                .emit(Instruction::LoadFieldAddress(plan.builder));
            self.stream.emit(Instruction::LoadLocal(exception_slot));
            self.stream
                .call_effect(Instruction::Call(set_exception), 2, 0);
        }
        self.stream.emit(Instruction::Leave(run.finished));
        self.stream.mark(handler_end);
        self.stream.region(ExceptionRegion {
            kind: HandlerKind::Catch(exception_token),
            try_start,
            try_end,
            handler_start,
            handler_end,
        });

        // An `async` iterator ends by saying `false` through its promise, and
        // a `yield return` left for the `true` beside it.
        if let Some(yielded) = run.yielded {
            self.stream.mark(run.done);
            self.finish_async_iterator(&plan)?;
            self.settle_promise(&plan, false)?;
            self.stream.emit(Instruction::Ret);
            self.stream.mark(yielded);
            self.settle_promise(&plan, true)?;
            self.stream.mark(run.finished);
            self.stream.emit(Instruction::Ret);
            return Ok(());
        }
        // `state = -2; builder.SetResult(result);`
        self.stream.mark(run.done);
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(-2));
        self.stream.emit(Instruction::StoreField(plan.state));
        self.clear_fields(&plan.root_cleared, &plan.locals)?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(plan.builder));
        let set_result = match run.result_slot {
            Some(slot) => {
                self.stream.emit(Instruction::LoadLocal(slot));
                self.emitter.builder_member(
                    &plan,
                    "SetResult",
                    &method_signature(true, &void, &[SigType::TypeParameter(0)]),
                )?
            }
            None => self.emitter.builder_member(
                &plan,
                "SetResult",
                &method_signature(true, &void, &[]),
            )?,
        };
        self.stream.call_effect(
            Instruction::Call(set_result),
            1 + usize::from(run.result_slot.is_some()),
            0,
        );
        self.stream.mark(run.finished);
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// Whether a statement is one of the shapes an `await` is left in, and
    /// emits it as the suspension it is where it is.
    pub(crate) fn emit_await_statement(
        &mut self,
        statement: &BoundStatement,
    ) -> Result<bool, EmitError> {
        if self.async_run.is_none() {
            return Ok(false);
        }
        let (await_expression, target) = match &statement.kind {
            BoundStatementKind::Expression(value) => match &value.kind {
                BoundExpressionKind::Await { .. } => (value, AwaitTarget::Dropped),
                BoundExpressionKind::Assignment { target, value } => {
                    match (&target.kind, &value.kind) {
                        (BoundExpressionKind::Local(local), BoundExpressionKind::Await { .. }) => {
                            (value.as_ref(), AwaitTarget::Local(*local))
                        }
                        _ => return Ok(false),
                    }
                }
                _ => return Ok(false),
            },
            BoundStatementKind::LocalDeclaration {
                local,
                initializer: Some(value),
            } if matches!(value.kind, BoundExpressionKind::Await { .. }) => {
                (value, AwaitTarget::Local(*local))
            }
            _ => return Ok(false),
        };
        self.emit_await(await_expression, target)?;
        Ok(true)
    }

    /// `await e`: ask the awaiter whether it is done; if not, park the
    /// awaiter and this machine with the builder and go; either way, the
    /// value is what `GetResult()` gives when the walk gets here.
    fn emit_await(
        &mut self,
        expression: &BoundExpression,
        target: AwaitTarget,
    ) -> Result<(), EmitError> {
        let BoundExpressionKind::Await { operand, awaiting } = &expression.kind else {
            return Err(EmitError::new("not an `await`"));
        };
        // A `dynamic` operand is waited on through sites: the runtime binder
        // finds its `GetAwaiter()`, and the awaiter's `IsCompleted` and
        // `GetResult()`, and the awaiter is kept as an `object` (Roslyn's
        // `MakeCallMaybeDynamic`).
        let awaiting = match awaiting {
            Some(awaiting) => Some(awaiting.as_ref()),
            None if matches!(operand.ty, Type::Dynamic) => None,
            None => {
                return Err(EmitError::new(format!(
                    "the operand of an `await` has no `GetAwaiter`{}",
                    self.at(expression.span)
                )));
            }
        };
        let awaiter_type = awaiting.map_or(Type::Dynamic, |awaiting| awaiting.awaiter.clone());
        let (number, resume) = self.next_suspension()?;
        let Some(run) = &self.async_run else {
            return Err(EmitError::new(
                "`await` outside the state machine it belongs to",
            ));
        };
        let plan_state = run.plan.state;
        let plan_builder = run.plan.builder;
        let machine_slot = run.machine_slot;
        let finished = run.finished;
        let inner_sig = run.plan.inner_sig.clone();
        let Some(awaiter_field) = run
            .plan
            .awaiters
            .iter()
            .find(|(ty, _)| *ty == awaiter_type)
            .map(|(_, token)| *token)
        else {
            return Err(EmitError::new("an awaiter with no field to wait in"));
        };
        let plan = run.plan.clone();

        let awaiter_is_value = self.emitter.is_value_type(&awaiter_type);
        let awaiter_slot = self.temporary(&awaiter_type)?;
        self.clear_current_before_await()?;

        // `awaiter = e.GetAwaiter();`
        match awaiting {
            None => self.emit_dynamic_get_awaiter(operand)?,
            // An extension `GetAwaiter` takes the operand as its argument,
            // boxed where it is a struct and its `this` is not.
            Some(awaiting) if let Some((type_arguments, this)) = &awaiting.extension => {
                self.emit_expression(operand, true)?;
                if self.emitter.is_value_type(&operand.ty) && !self.emitter.is_value_type(this) {
                    let token = self.emitter.type_token(&operand.ty)?;
                    self.stream.emit(Instruction::Box(token));
                }
                let get_awaiter = self.method_token_on(awaiting.get_awaiter, None)?;
                let get_awaiter = self.instantiated(get_awaiter, type_arguments)?;
                self.stream
                    .call_effect(Instruction::Call(get_awaiter), 1, 1);
            }
            Some(awaiting) => {
                let awaitable_slot = self.temporary(&operand.ty)?;
                self.emit_expression(operand, true)?;
                self.stream.emit(Instruction::StoreLocal(awaitable_slot));
                let get_awaiter =
                    self.method_token_on(awaiting.get_awaiter, Some(&awaiting.get_awaiter_type))?;
                if self.emitter.is_value_type(&operand.ty) {
                    self.stream
                        .emit(Instruction::LoadLocalAddress(awaitable_slot));
                    self.stream
                        .call_effect(Instruction::Call(get_awaiter), 1, 1);
                } else {
                    self.stream.emit(Instruction::LoadLocal(awaitable_slot));
                    self.stream
                        .call_effect(Instruction::CallVirtual(get_awaiter), 1, 1);
                }
            }
        }
        self.stream.emit(Instruction::StoreLocal(awaiter_slot));

        // `if (!awaiter.IsCompleted) { ... suspend ... }`
        let ready = self.stream.label();
        match awaiting {
            Some(awaiting) => {
                let is_completed = self.emitter.property_accessor(
                    awaiting.is_completed,
                    Some(&awaiting.is_completed_type),
                    false,
                )?;
                self.push_awaiter(awaiter_slot, awaiter_is_value);
                self.stream.call_effect(
                    if awaiter_is_value {
                        Instruction::Call(is_completed)
                    } else {
                        Instruction::CallVirtual(is_completed)
                    },
                    1,
                    1,
                );
            }
            None => self.emit_dynamic_is_completed(awaiter_slot)?,
        }
        self.stream.emit(Instruction::BranchIfTrue(ready));

        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(number));
        self.keep_state_local();
        self.stream.emit(Instruction::StoreField(plan_state));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadLocal(awaiter_slot));
        self.stream.emit(Instruction::StoreField(awaiter_field));
        let void = SigType::Primitive(ElementType::Void);
        let on_completed_signature = generic_method_signature(
            true,
            2,
            &void,
            &[
                SigType::ByRef(Box::new(SigType::MethodTypeParameter(0))),
                SigType::ByRef(Box::new(SigType::MethodTypeParameter(1))),
            ],
        );
        if awaiting.is_none() {
            self.emit_dynamic_on_completed(
                &plan,
                machine_slot,
                awaiter_slot,
                &on_completed_signature,
            )?;
        } else {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::StoreLocal(machine_slot));
            let on_completed_name = if self.awaiter_is_critical(&awaiter_type) {
                "AwaitUnsafeOnCompleted"
            } else {
                "AwaitOnCompleted"
            };
            let on_completed =
                self.emitter
                    .builder_member(&plan, on_completed_name, &on_completed_signature)?;
            let awaiter_sig = self.emitter.sig_type(&awaiter_type)?;
            let on_completed = self
                .emitter
                .spec_of(on_completed, &[awaiter_sig, inner_sig]);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream
                .emit(Instruction::LoadFieldAddress(plan_builder));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream
                .emit(Instruction::LoadFieldAddress(awaiter_field));
            self.stream
                .emit(Instruction::LoadLocalAddress(machine_slot));
            self.stream
                .call_effect(Instruction::Call(on_completed), 3, 0);
        }
        self.stream.emit(Instruction::Leave(finished));

        // Resumed: read the awaiter back, clear the field, and carry on.
        self.stream.mark(resume);
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadField(awaiter_field));
        self.stream.emit(Instruction::StoreLocal(awaiter_slot));
        if awaiter_is_value {
            let token = self.emitter.type_token(&awaiter_type)?;
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream
                .emit(Instruction::LoadFieldAddress(awaiter_field));
            self.stream.emit(Instruction::InitObject(token));
        } else {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadNull);
            self.stream.emit(Instruction::StoreField(awaiter_field));
        }
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadInt32(-1));
        self.keep_state_local();
        self.stream.emit(Instruction::StoreField(plan_state));

        // `value = awaiter.GetResult();`
        self.stream.mark(ready);
        if let AwaitTarget::Local(local) = target {
            self.begin_store(local);
        }
        let Some(awaiting) = awaiting else {
            let used = matches!(target, AwaitTarget::Local(_));
            self.emit_dynamic_get_result(awaiter_slot, used)?;
            if let AwaitTarget::Local(local) = target {
                self.end_store(local);
            }
            return Ok(());
        };
        let get_result =
            self.method_token_on(awaiting.get_result, Some(&awaiting.get_result_type))?;
        self.push_awaiter(awaiter_slot, awaiter_is_value);
        let gives = !matches!(expression.ty, Type::Void);
        self.stream.call_effect(
            if awaiter_is_value {
                Instruction::Call(get_result)
            } else {
                Instruction::CallVirtual(get_result)
            },
            1,
            usize::from(gives),
        );
        match target {
            AwaitTarget::Local(local) => self.end_store(local),
            AwaitTarget::Dropped => {
                if gives {
                    self.stream.emit(Instruction::Pop);
                }
            }
        }
        Ok(())
    }

    /// Parks a `dynamic` awaiter with the builder: through
    /// `AwaitUnsafeOnCompleted` where it is an `ICriticalNotifyCompletion`,
    /// and otherwise through `AwaitOnCompleted`, as the `INotifyCompletion`
    /// it must then be (Roslyn's `GenerateAwaitOnCompletedDynamic`):
    ///
    /// ```text
    /// critical = awaiter as ICriticalNotifyCompletion;
    /// if (critical == null) {
    ///     notify = (INotifyCompletion)awaiter;
    ///     builder.AwaitOnCompleted(ref notify, ref this);
    ///     notify = null;
    /// } else {
    ///     builder.AwaitUnsafeOnCompleted(ref critical, ref this);
    /// }
    /// critical = null;
    /// ```
    fn emit_dynamic_on_completed(
        &mut self,
        plan: &AsyncPlan,
        machine_slot: u16,
        awaiter_slot: u16,
        signature: &[u8],
    ) -> Result<(), EmitError> {
        let interface = |name: &str| {
            self.emitter
                .compilation
                .type_by_metadata_name(name)
                .map(Type::named)
                .ok_or_else(|| EmitError::new(format!("the compilation has no `{name}`")))
        };
        let critical_type = interface("System.Runtime.CompilerServices.ICriticalNotifyCompletion")?;
        let notify_type = interface("System.Runtime.CompilerServices.INotifyCompletion")?;
        let critical = self.temporary(&critical_type)?;
        let critical_token = self.emitter.type_token(&critical_type)?;
        self.stream.emit(Instruction::LoadLocal(awaiter_slot));
        self.stream.emit(Instruction::IsInstance(critical_token));
        self.stream.emit(Instruction::StoreLocal(critical));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::StoreLocal(machine_slot));
        let unsafe_path = self.stream.label();
        let parked = self.stream.label();
        self.stream.emit(Instruction::LoadLocal(critical));
        self.stream.emit(Instruction::BranchIfTrue(unsafe_path));

        let notify = self.temporary(&notify_type)?;
        let notify_token = self.emitter.type_token(&notify_type)?;
        self.stream.emit(Instruction::LoadLocal(awaiter_slot));
        self.stream.emit(Instruction::CastClass(notify_token));
        self.stream.emit(Instruction::StoreLocal(notify));
        self.emit_on_completed_call(
            plan,
            machine_slot,
            "AwaitOnCompleted",
            signature,
            &notify_type,
            notify,
        )?;
        self.stream.emit(Instruction::LoadNull);
        self.stream.emit(Instruction::StoreLocal(notify));
        self.stream.emit(Instruction::Branch(parked));

        self.stream.mark(unsafe_path);
        self.emit_on_completed_call(
            plan,
            machine_slot,
            "AwaitUnsafeOnCompleted",
            signature,
            &critical_type,
            critical,
        )?;
        self.stream.mark(parked);
        self.stream.emit(Instruction::LoadNull);
        self.stream.emit(Instruction::StoreLocal(critical));
        Ok(())
    }

    /// `builder.<name><T, TStateMachine>(ref slot, ref machine)` for an
    /// awaiter of type `T` held in `slot`, the machine being in
    /// `machine_slot`.
    fn emit_on_completed_call(
        &mut self,
        plan: &AsyncPlan,
        machine_slot: u16,
        name: &str,
        signature: &[u8],
        awaiter: &Type,
        slot: u16,
    ) -> Result<(), EmitError> {
        let method = self.emitter.builder_member(plan, name, signature)?;
        let awaiter_sig = self.emitter.sig_type(awaiter)?;
        let method = self
            .emitter
            .spec_of(method, &[awaiter_sig, plan.inner_sig.clone()]);
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream
            .emit(Instruction::LoadFieldAddress(plan.builder));
        self.stream.emit(Instruction::LoadLocalAddress(slot));
        self.stream
            .emit(Instruction::LoadLocalAddress(machine_slot));
        self.stream.call_effect(Instruction::Call(method), 3, 0);
        Ok(())
    }

    /// The awaiter as a receiver: a struct is called on its address.
    fn push_awaiter(&mut self, slot: u16, is_value: bool) {
        self.stream.emit(if is_value {
            Instruction::LoadLocalAddress(slot)
        } else {
            Instruction::LoadLocal(slot)
        });
    }

    /// Whether an awaiter promises not to need the execution context flowed,
    /// which is what lets the builder take the cheaper path.
    fn awaiter_is_critical(&self, awaiter: &Type) -> bool {
        self.emitter
            .compilation
            .type_by_metadata_name("System.Runtime.CompilerServices.ICriticalNotifyCompletion")
            .is_some_and(|critical| {
                awaiter.symbol() == Some(critical)
                    || self
                        .emitter
                        .binder
                        .constructed_from(awaiter, critical)
                        .is_some()
            })
    }
}

// -- the spiller -------------------------------------------------------------

/// Moves every `await` in a body into a statement of its own.
///
/// A machine suspends by returning from `MoveNext`, and nothing may be on the
/// evaluation stack when a method returns; an `await` in the middle of an
/// expression — `F(a, await b)` — has `a` on the stack. So the `await` is
/// bound to a temporary before the statement, and so is anything evaluated
/// ahead of it that a later expression could tell apart, which keeps the
/// order the source wrote (§12.4.4). What is left in place is the value, read
/// from the temporary.
///
/// `Err` names the shape that is not rewritten yet.
#[allow(clippy::too_many_arguments)]
fn spill_awaits(
    mut body: BoundBody,
    boolean: Type,
    integer: Type,
    exception: Type,
    rethrow: Option<SymbolId>,
    ref_like: &dyn Fn(&Type) -> bool,
    nullable: Option<SymbolId>,
    symbols: &rustlyn_semantics::Symbols,
    iterator: bool,
) -> Result<BoundBody, String> {
    // An `async` iterator keeps its dispose mode in a local of the body, so
    // that the machine hoists it like any other and the exits it takes are
    // statements the rewrite of an awaiting `finally` redirects.
    let start = body
        .statements
        .first()
        .map_or(TextSpan::new(0, 0), |statement| statement.span);
    let dispose_mode = iterator.then(|| {
        let id = LocalId(body.locals.len() as u32);
        body.locals.push(LocalSymbol {
            name: DISPOSE_MODE.to_string(),
            ty: boolean.clone(),
            span: start,
            by_ref: false,
            readonly_ref: false,
            readonly: false,
        });
        id
    });
    let mut spiller = Spiller {
        hoisting: Hoisting::Awaits,
        locals: &mut body.locals,
        boolean,
        integer,
        exception,
        rethrow,
        guarded: 0,
        ref_like,
        nullable,
        symbols,
        dispose_mode,
    };
    let statements = std::mem::take(&mut body.statements);
    let mut statements = spiller.statements(statements)?;
    // A walk disposed before it started goes straight to the end.
    if let Some(flag) = dispose_mode {
        statements.insert(0, spiller.leave_if_disposing(flag, start));
    }
    body.statements = statements;
    Ok(body)
}

/// Moves every [`SpillSequence`](BoundExpressionKind::SpillSequence) of a
/// body — its own statements', its lambdas' and its local functions' — into
/// statements ahead of the statement holding it, the way the `await`s of a
/// machine are moved: what is evaluated before it is kept in temporaries, so
/// that the order the source wrote is kept.
pub(crate) fn spill_sequences(
    mut body: BoundBody,
    boolean: Type,
    integer: Type,
    symbols: &rustlyn_semantics::Symbols,
) -> Result<BoundBody, String> {
    let mut spiller = Spiller {
        hoisting: Hoisting::Sequences,
        locals: &mut body.locals,
        boolean,
        integer,
        exception: Type::Error,
        rethrow: None,
        guarded: 0,
        // A local may hold a `ref struct`; only a machine's fields may not.
        ref_like: &|_| false,
        nullable: None,
        symbols,
        dispose_mode: None,
    };
    let statements = std::mem::take(&mut body.statements);
    body.statements = spiller.statements(statements)?;
    for lambda in &mut body.lambdas {
        let statement = std::mem::replace(
            &mut lambda.body,
            BoundStatement::new(BoundStatementKind::Empty, lambda.span),
        );
        lambda.body = spiller.nested(statement)?;
    }
    for function in &mut body.local_functions {
        let span = function.body.span;
        let statement = std::mem::replace(
            &mut function.body,
            BoundStatement::new(BoundStatementKind::Empty, span),
        );
        function.body = spiller.nested(statement)?;
    }
    Ok(body)
}

/// Whether anything in a body is a [`SpillSequence`](BoundExpressionKind::SpillSequence).
pub(crate) fn body_has_spill_sequences(body: &BoundBody) -> bool {
    fn holds(statement: &BoundStatement) -> bool {
        expressions_of(statement)
            .into_iter()
            .any(contains_spill_sequence)
            || substatements(statement).into_iter().any(holds)
    }
    body.statements.iter().any(holds)
        || body.lambdas.iter().any(|lambda| holds(&lambda.body))
        || body
            .local_functions
            .iter()
            .any(|function| holds(&function.body))
}

/// What a spiller moves out of expressions into statements of their own.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Hoisting {
    /// Every `await`, since a machine may only stop with the stack empty.
    Awaits,
    /// Every [`SpillSequence`](BoundExpressionKind::SpillSequence), whose
    /// statements may not run with anything on the stack beneath them.
    Sequences,
}

struct Spiller<'a> {
    hoisting: Hoisting,
    locals: &'a mut Vec<LocalSymbol>,
    /// `bool` and `int`, for the flags and conditions the rewrite writes.
    boolean: Type,
    integer: Type,
    /// `System.Exception`, for the one a `finally` that awaits has to hold.
    exception: Type,
    /// `ExceptionDispatchInfo.Throw(Exception)`, where the library has it.
    rethrow: Option<SymbolId>,
    /// How many `finally` blocks have been rewritten: each needs a label of
    /// its own.
    guarded: usize,
    /// Whether a value is a `ref struct`, which no temporary may keep across
    /// an `await`.
    ref_like: &'a dyn Fn(&Type) -> bool,
    /// `System.Nullable<T>`'s definition, where it is referenced.
    nullable: Option<SymbolId>,
    /// What the types are, to tell a reference from a value.
    symbols: &'a rustlyn_semantics::Symbols,
    /// An `async` iterator's dispose mode (see [`DISPOSE_MODE`]), which
    /// `yield break` sets and every resumption after a `yield return` asks.
    dispose_mode: Option<LocalId>,
}

impl Spiller<'_> {
    /// `local = value;` as a statement.
    fn assign(local: LocalId, value: BoundExpression, span: TextSpan) -> BoundStatement {
        let ty = value.ty.clone();
        BoundStatement::new(
            BoundStatementKind::Expression(BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(BoundExpression::new(
                        BoundExpressionKind::Local(local),
                        ty.clone(),
                        span,
                    )),
                    value: Box::new(value),
                },
                ty,
                span,
            )),
            span,
        )
    }

    /// `if (disposeMode) return;` in an `async` iterator, whose `return` is
    /// the end of the walk: a resumed body told to stop leaves through its
    /// `finally`s — an awaiting one included, which redirects the `return`
    /// to itself — and nowhere else (Roslyn jumps from one disposal label to
    /// the next for the same effect).
    fn leave_if_disposing(&self, flag: LocalId, span: TextSpan) -> BoundStatement {
        Self::when(
            Self::read(flag, &self.boolean, span),
            vec![BoundStatement::new(BoundStatementKind::Return(None), span)],
            span,
        )
    }

    /// `if (condition) { statements }`.
    fn when(
        condition: BoundExpression,
        statements: Vec<BoundStatement>,
        span: TextSpan,
    ) -> BoundStatement {
        BoundStatement::new(
            BoundStatementKind::If {
                condition,
                consequence: Box::new(BoundStatement::new(
                    BoundStatementKind::Block(statements),
                    span,
                )),
                alternative: None,
            },
            span,
        )
    }

    fn not(&self, operand: BoundExpression) -> BoundExpression {
        let span = operand.span;
        BoundExpression::new(
            BoundExpressionKind::Unary {
                operator: UnaryOperator::LogicalNot,
                operand: Box::new(operand),
            },
            self.boolean.clone(),
            span,
        )
    }

    /// `value == null`, for a reference, a `T` or a `T?` alike.
    fn is_null(value: BoundExpression, boolean: &Type) -> BoundExpression {
        let span = value.span;
        BoundExpression::new(
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Equality,
                left: Box::new(value),
                right: Box::new(BoundExpression::new(
                    BoundExpressionKind::Literal(rustlyn_semantics::ConstantValue::Null),
                    Type::Null,
                    span,
                )),
            },
            boolean.clone(),
            span,
        )
    }

    /// `value.GetValueOrDefault()`: what a `T?` known to hold something
    /// holds.
    fn value_inside(
        &self,
        value: BoundExpression,
        span: TextSpan,
    ) -> Result<BoundExpression, String> {
        let nullable = self
            .nullable
            .ok_or_else(|| "a `T?` with no `Nullable<T>` referenced".to_string())?;
        let method = self
            .symbols
            .lookup(nullable, "GetValueOrDefault")
            .iter()
            .copied()
            .find(|method| {
                self.symbols
                    .get(*method)
                    .as_method()
                    .is_some_and(|detail| detail.parameters.is_empty())
            })
            .ok_or_else(|| "a `Nullable<T>` with no `GetValueOrDefault()`".to_string())?;
        let inner = match &value.ty {
            Type::Named { type_arguments, .. } => type_arguments
                .first()
                .cloned()
                .ok_or_else(|| "a `T?` with no `T`".to_string())?,
            _ => return Err("a `T?` that is no construction".to_string()),
        };
        Ok(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: Some(Box::new(value)),
                method,
                type_arguments: Vec::new(),
                arguments: Vec::new(),
                virtual_call: false,
            },
            inner,
            span,
        ))
    }

    /// Whether a type is a `T?` of a struct, by its definition's name.
    fn is_nullable_value(&self, ty: &Type) -> bool {
        self.nullable
            .is_some_and(|nullable| ty.symbol() == Some(nullable))
    }

    /// Whether an expression holds anything this spiller moves out.
    fn holds(&self, expression: &BoundExpression) -> bool {
        match self.hoisting {
            Hoisting::Awaits => contains_await(expression),
            Hoisting::Sequences => contains_spill_sequence(expression),
        }
    }

    /// Whether a statement suspends the machine somewhere inside, which a
    /// handler or a `finally` may not do. Hoisting sequences suspends
    /// nothing: what a `finally` hoists stays inside it.
    fn suspends(&self, statement: &BoundStatement) -> bool {
        self.hoisting == Hoisting::Awaits && statement_awaits(statement)
    }

    fn read(local: LocalId, ty: &Type, span: TextSpan) -> BoundExpression {
        BoundExpression::new(BoundExpressionKind::Local(local), ty.clone(), span)
    }
    fn temp(&mut self, ty: &Type, span: TextSpan) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(LocalSymbol {
            name: format!("<>s__{}", self.locals.len() + 1),
            ty: ty.clone(),
            span,
            by_ref: false,
            readonly_ref: false,
            readonly: false,
        });
        id
    }

    fn statements(
        &mut self,
        statements: Vec<BoundStatement>,
    ) -> Result<Vec<BoundStatement>, String> {
        let mut out = Vec::with_capacity(statements.len());
        for statement in statements {
            self.statement(statement, &mut out)?;
        }
        Ok(out)
    }

    /// One statement, rewritten into as many as it takes, in order.
    fn statement(
        &mut self,
        statement: BoundStatement,
        out: &mut Vec<BoundStatement>,
    ) -> Result<(), String> {
        let span = statement.span;
        let mut prelude = Vec::new();
        let mut postlude = Vec::new();
        let kind = match statement.kind {
            BoundStatementKind::Block(statements) => {
                BoundStatementKind::Block(self.statements(statements)?)
            }
            // `var x = await e;` is already the shape `MoveNext` wants; only
            // what is inside the operand has to come out.
            BoundStatementKind::LocalDeclaration {
                local,
                initializer: Some(mut value),
            } => {
                if let BoundExpressionKind::Await { operand, .. } = &mut value.kind {
                    self.expression(operand, &mut prelude)?;
                } else {
                    self.expression(&mut value, &mut prelude)?;
                }
                BoundStatementKind::LocalDeclaration {
                    local,
                    initializer: Some(value),
                }
            }
            BoundStatementKind::Expression(mut value) => {
                match &mut value.kind {
                    BoundExpressionKind::Await { operand, .. } => {
                        self.expression(operand, &mut prelude)?;
                    }
                    BoundExpressionKind::Assignment {
                        target,
                        value: assigned,
                    } if matches!(target.kind, BoundExpressionKind::Local(_))
                        && matches!(assigned.kind, BoundExpressionKind::Await { .. }) =>
                    {
                        // `x = await e` where `x` is a local is left.
                        if let BoundExpressionKind::Await { operand, .. } = &mut assigned.kind {
                            self.expression(operand, &mut prelude)?;
                        }
                    }
                    // Any other place is written from a temporary, so that
                    // nothing of the place is on the stack meanwhile, and
                    // what locates it is kept from before the `await`.
                    BoundExpressionKind::Assignment {
                        target,
                        value: assigned,
                    } if !matches!(
                        target.kind,
                        BoundExpressionKind::Field { .. }
                            | BoundExpressionKind::ArrayAccess { .. }
                            | BoundExpressionKind::Property { .. }
                            | BoundExpressionKind::IndexerAccess { .. }
                    ) =>
                    {
                        self.expression(target, &mut prelude)?;
                        self.expression(assigned, &mut prelude)?;
                    }
                    _ => self.expression(&mut value, &mut prelude)?,
                }
                BoundStatementKind::Expression(value)
            }
            BoundStatementKind::If {
                mut condition,
                consequence,
                alternative,
            } => {
                self.expression(&mut condition, &mut prelude)?;
                BoundStatementKind::If {
                    condition,
                    consequence: Box::new(self.nested(*consequence)?),
                    alternative: match alternative {
                        Some(alternative) => Some(Box::new(self.nested(*alternative)?)),
                        None => None,
                    },
                }
            }
            // `while (await reader.WaitToReadAsync()) { ... }` becomes a
            // loop that never ends of its own: the condition is awaited
            // at the top of the body, and leaves when it says so. A
            // `continue` still comes back to the top, where the
            // condition is.
            BoundStatementKind::While { condition, body } if self.holds(&condition) => {
                let mut condition = condition;
                let mut head = Vec::new();
                self.expression(&mut condition, &mut head)?;
                let cond_span = condition.span;
                let leave = BoundStatement::new(BoundStatementKind::Break(0), cond_span);
                head.push(Self::when(self.not(condition), vec![leave], cond_span));
                head.push(self.nested(*body)?);
                BoundStatementKind::While {
                    condition: BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Boolean(true)),
                        self.boolean.clone(),
                        cond_span,
                    ),
                    body: Box::new(BoundStatement::new(BoundStatementKind::Block(head), span)),
                }
            }
            BoundStatementKind::While { condition, body } => BoundStatementKind::While {
                condition,
                body: Box::new(self.nested(*body)?),
            },
            // `do { ... } while (await more())` runs the body, then awaits
            // the condition at the bottom and leaves when it says so. A
            // `continue` would have to reach that bottom, which a loop that
            // never ends of its own cannot offer it.
            BoundStatementKind::DoWhile { body, condition } if self.holds(&condition) => {
                if continues_to(&body, 0) {
                    return Err(
                        "a `continue` in a `do` loop whose condition awaits is not rewritten yet"
                            .to_string(),
                    );
                }
                let mut condition = condition;
                let mut steps = vec![self.nested(*body)?];
                self.expression(&mut condition, &mut steps)?;
                let cond_span = condition.span;
                let leave = BoundStatement::new(BoundStatementKind::Break(0), cond_span);
                steps.push(Self::when(self.not(condition), vec![leave], cond_span));
                BoundStatementKind::While {
                    condition: BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Boolean(true)),
                        self.boolean.clone(),
                        cond_span,
                    ),
                    body: Box::new(BoundStatement::new(BoundStatementKind::Block(steps), span)),
                }
            }
            BoundStatementKind::DoWhile { body, condition } => BoundStatementKind::DoWhile {
                body: Box::new(self.nested(*body)?),
                condition,
            },
            BoundStatementKind::For {
                initializers,
                condition,
                incrementors,
                body,
            } => {
                if condition.as_ref().is_some_and(|value| self.holds(value))
                    || incrementors.iter().any(|value| self.holds(value))
                {
                    return Err(
                        "an `await` in the condition or the step of a `for` is not rewritten yet"
                            .to_string(),
                    );
                }
                // The initializers run once, before the loop: what they
                // await can come out in front of it.
                let mut kept = Vec::new();
                for initializer in initializers {
                    self.statement(initializer, &mut kept)?;
                }
                BoundStatementKind::For {
                    initializers: kept,
                    condition,
                    incrementors,
                    body: Box::new(self.nested(*body)?),
                }
            }
            BoundStatementKind::ForEach {
                local,
                mut collection,
                body,
                enumeration,
                walk,
                dimensions,
            } => {
                self.expression(&mut collection, &mut prelude)?;
                BoundStatementKind::ForEach {
                    local,
                    collection,
                    body: Box::new(self.nested(*body)?),
                    enumeration,
                    walk,
                    dimensions,
                }
            }
            // A `switch` whose `when` clauses await matches ahead of itself,
            // each label in turn noting the one that matched, and switches
            // on that: the sections, their `break`s and what their patterns
            // bound stay as they were.
            //
            // ```text
            // g = x; k = 0;
            // if (k == 0 && g is p1) { w = when1; if (w) k = 1; }
            // ...
            // switch (k) { case 1: ... default: ... }
            // ```
            BoundStatementKind::Switch {
                mut governing,
                sections,
            } if sections.iter().any(|section| {
                section.labels.iter().any(|label| match label {
                    BoundSwitchLabel::Case(case) => {
                        case.when.as_ref().is_some_and(|when| self.holds(when))
                    }
                    BoundSwitchLabel::Default => false,
                })
            }) =>
            {
                if sections
                    .iter()
                    .any(|section| section.statements.iter().any(goes_to_case))
                {
                    return Err(
                        "a `goto case` in a `switch` whose `when` awaits is not rewritten yet"
                            .to_string(),
                    );
                }
                self.expression(&mut governing, &mut prelude)?;
                let governing_type = governing.ty.clone();
                let held = self.temp(&governing_type, span);
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: held,
                        initializer: Some(governing),
                    },
                    span,
                ));
                let integer = self.integer.clone();
                let matched = self.temp(&integer, span);
                let number = |value: i32| {
                    BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Int32(value)),
                        integer.clone(),
                        span,
                    )
                };
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: matched,
                        initializer: Some(number(0)),
                    },
                    span,
                ));
                let mut next = 0;
                let mut switched = Vec::with_capacity(sections.len());
                for section in sections {
                    let mut labels = Vec::with_capacity(section.labels.len());
                    for label in section.labels {
                        let BoundSwitchLabel::Case(case) = label else {
                            labels.push(BoundSwitchLabel::Default);
                            continue;
                        };
                        next += 1;
                        let BoundCaseLabel { pattern, when } = *case;
                        let at = pattern.span;
                        let mut chosen = vec![Self::assign(matched, number(next), at)];
                        if let Some(mut when) = when {
                            let mut tested = Vec::new();
                            self.expression(&mut when, &mut tested)?;
                            tested.push(Self::when(when, chosen, at));
                            chosen = tested;
                        }
                        let unmatched = BoundExpression::new(
                            BoundExpressionKind::Binary {
                                operator: BinaryOperator::Equality,
                                left: Box::new(Self::read(matched, &integer, at)),
                                right: Box::new(number(0)),
                            },
                            self.boolean.clone(),
                            at,
                        );
                        let test = BoundExpression::new(
                            BoundExpressionKind::IsPattern {
                                operand: Box::new(Self::read(held, &governing_type, at)),
                                pattern: Box::new(pattern),
                            },
                            self.boolean.clone(),
                            at,
                        );
                        let both = BoundExpression::new(
                            BoundExpressionKind::Binary {
                                operator: BinaryOperator::LogicalAnd,
                                left: Box::new(unmatched),
                                right: Box::new(test),
                            },
                            self.boolean.clone(),
                            at,
                        );
                        prelude.push(Self::when(both, chosen, at));
                        labels.push(BoundSwitchLabel::Case(Box::new(BoundCaseLabel {
                            pattern: BoundPattern::new(
                                BoundPatternKind::Constant(number(next)),
                                at,
                            ),
                            when: None,
                        })));
                    }
                    switched.push(BoundSwitchSection {
                        labels,
                        statements: self.statements(section.statements)?,
                    });
                }
                BoundStatementKind::Switch {
                    governing: Self::read(matched, &integer, span),
                    sections: switched,
                }
            }
            BoundStatementKind::Switch {
                mut governing,
                mut sections,
            } => {
                self.expression(&mut governing, &mut prelude)?;
                for section in &mut sections {
                    let statements = std::mem::take(&mut section.statements);
                    section.statements = self.statements(statements)?;
                }
                BoundStatementKind::Switch {
                    governing,
                    sections,
                }
            }
            BoundStatementKind::Try {
                body,
                mut catches,
                finally,
            } => {
                let finally_awaits = finally
                    .as_deref()
                    .is_some_and(|finally| self.suspends(finally));
                // A `catch` that awaits cannot: no suspension may happen
                // inside a handler. Its body moves out after the `try`,
                // and the handler is left only noting which one caught —
                // the exception itself stays in the variable the handler
                // was given, which is a field of the machine like any
                // local.
                let mut moved = Vec::new();
                for (number, catch) in catches.iter_mut().enumerate() {
                    if !self.suspends(&catch.body) {
                        continue;
                    }
                    // Out of its `catch`, a handler's `throw;` rethrows
                    // what was caught from where it is kept: the variable
                    // the `catch` declared, or one made for it (Roslyn's
                    // `AwaitCatchFrame.pendingCaughtException`).
                    let caught = match catch.local {
                        Some(local) => local,
                        None => {
                            let local = self.temp(&catch.exception_type, span);
                            catch.local = Some(local);
                            local
                        }
                    };
                    let mut taken = std::mem::replace(
                        &mut catch.body,
                        BoundStatement::new(BoundStatementKind::Empty, span),
                    );
                    let caught_type = catch.exception_type.clone();
                    self.rethrow_from(&mut taken, caught, &caught_type);
                    moved.push((number, taken));
                }
                if !moved.is_empty() {
                    let integer = self.integer.clone();
                    let flag = self.temp(&integer, span);
                    let number = |value: i32| {
                        BoundExpression::new(
                            BoundExpressionKind::Literal(ConstantValue::Int32(value)),
                            integer.clone(),
                            span,
                        )
                    };
                    prelude.push(BoundStatement::new(
                        BoundStatementKind::LocalDeclaration {
                            local: flag,
                            initializer: Some(number(0)),
                        },
                        span,
                    ));
                    for (which, handler) in moved {
                        let mark = which as i32 + 1;
                        catches[which].body = Self::assign(flag, number(mark), span);
                        let caught = BoundExpression::new(
                            BoundExpressionKind::Binary {
                                operator: BinaryOperator::Equality,
                                left: Box::new(Self::read(flag, &integer, span)),
                                right: Box::new(number(mark)),
                            },
                            self.boolean.clone(),
                            span,
                        );
                        let handler = self.nested(handler)?;
                        postlude.push(Self::when(caught, vec![handler], span));
                    }
                }
                let body = Box::new(self.nested(*body)?);
                // A `finally` that awaits cannot run as one either: the
                // `try` is left with whatever happened noted — an
                // exception caught and kept, a `return` or a jump out
                // parked — and the `finally` runs after it as plain
                // statements, then throws or jumps as the `try` would have.
                if finally_awaits {
                    let finally = finally.expect("a finally that awaits exists");
                    let mut inside = vec![BoundStatement::new(
                        BoundStatementKind::Try {
                            body,
                            catches,
                            finally: None,
                        },
                        span,
                    )];
                    inside.append(&mut postlude);
                    let guarded = self.guard_awaiting_finally(inside, *finally, span)?;
                    out.extend(prelude);
                    out.extend(guarded);
                    return Ok(());
                }
                // A handler runs before the `finally`, so where there is
                // one the moved handlers go inside it: the `try` with
                // its catches, then the handlers, all under the
                // `finally`.
                if finally.is_some() && !postlude.is_empty() {
                    let mut inside = vec![BoundStatement::new(
                        BoundStatementKind::Try {
                            body,
                            catches,
                            finally: None,
                        },
                        span,
                    )];
                    inside.append(&mut postlude);
                    BoundStatementKind::Try {
                        body: Box::new(BoundStatement::new(
                            BoundStatementKind::Block(inside),
                            span,
                        )),
                        catches: Vec::new(),
                        finally,
                    }
                } else {
                    BoundStatementKind::Try {
                        body,
                        catches,
                        finally,
                    }
                }
            }
            // `await using` is the `try`/`finally` it means, written out
            // here because its `finally` awaits: rewritten as one, it is
            // taken apart like any other.
            BoundStatementKind::Using { resources, body }
                if resources.iter().any(|resource| resource.awaited.is_some()) =>
            {
                let lowered = Self::await_using(resources, *body, span);
                return self.statement(lowered, out);
            }
            BoundStatementKind::Using {
                mut resources,
                body,
            } => {
                for resource in &mut resources {
                    self.expression(&mut resource.value, &mut prelude)?;
                }
                BoundStatementKind::Using {
                    resources,
                    body: Box::new(self.nested(*body)?),
                }
            }
            BoundStatementKind::Lock {
                mut value,
                held,
                taken,
                scope,
                body,
            } => {
                self.expression(&mut value, &mut prelude)?;
                BoundStatementKind::Lock {
                    value,
                    held,
                    taken,
                    scope,
                    body: Box::new(self.nested(*body)?),
                }
            }
            BoundStatementKind::Return(Some(mut value)) => {
                self.expression(&mut value, &mut prelude)?;
                BoundStatementKind::Return(Some(value))
            }
            BoundStatementKind::Throw(Some(mut value)) => {
                self.expression(&mut value, &mut prelude)?;
                BoundStatementKind::Throw(Some(value))
            }
            BoundStatementKind::YieldReturn(mut value) if self.hoisting == Hoisting::Sequences => {
                self.expression(&mut value, &mut prelude)?;
                BoundStatementKind::YieldReturn(value)
            }
            // An `async` iterator resumed after its `yield return` stops
            // there if it is being disposed.
            BoundStatementKind::YieldReturn(mut value) if self.dispose_mode.is_some() => {
                let flag = self.dispose_mode.expect("an async iterator's dispose mode");
                self.expression(&mut value, &mut prelude)?;
                postlude.push(self.leave_if_disposing(flag, span));
                BoundStatementKind::YieldReturn(value)
            }
            // `yield break` is disposing of the walk from inside it: out
            // through the `finally`s, and never back.
            BoundStatementKind::YieldBreak if self.dispose_mode.is_some() => {
                let flag = self.dispose_mode.expect("an async iterator's dispose mode");
                let set = Self::assign(
                    flag,
                    BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Boolean(true)),
                        self.boolean.clone(),
                        span,
                    ),
                    span,
                );
                BoundStatementKind::Block(vec![
                    set,
                    BoundStatement::new(BoundStatementKind::Return(None), span),
                ])
            }
            BoundStatementKind::YieldReturn(_) => {
                return Err("a `yield return` outside an iterator".to_string());
            }
            other => other,
        };
        out.extend(prelude);
        out.push(BoundStatement::new(kind, span));
        out.extend(postlude);
        Ok(())
    }

    /// Rewrites every `throw;` of a handler that is moved out of its `catch`
    /// into a throw of what the `catch` caught, kept in `caught`:
    /// `ExceptionDispatchInfo.Throw(caught)`, which keeps the stack trace a
    /// `throw;` would have kept (Roslyn's `Rethrow`). One inside a `catch`
    /// nested in the handler rethrows that `catch`'s exception and stays —
    /// if that `catch` awaits too, it is moved in turn and rewritten then.
    fn rethrow_from(&self, statement: &mut BoundStatement, caught: LocalId, ty: &Type) {
        use BoundStatementKind as S;
        let span = statement.span;
        match &mut statement.kind {
            S::Throw(None) => {
                let exception = Self::read(caught, ty, span);
                statement.kind = match self.rethrow {
                    Some(throw) => S::Expression(BoundExpression::new(
                        BoundExpressionKind::Call {
                            receiver: None,
                            method: throw,
                            type_arguments: Vec::new(),
                            arguments: vec![exception],
                            virtual_call: false,
                        },
                        Type::Void,
                        span,
                    )),
                    None => S::Throw(Some(exception)),
                };
            }
            S::Block(statements) => {
                for statement in statements {
                    self.rethrow_from(statement, caught, ty);
                }
            }
            S::If {
                consequence,
                alternative,
                ..
            } => {
                self.rethrow_from(consequence, caught, ty);
                if let Some(alternative) = alternative {
                    self.rethrow_from(alternative, caught, ty);
                }
            }
            S::While { body, .. }
            | S::DoWhile { body, .. }
            | S::ForEach { body, .. }
            | S::For { body, .. }
            | S::Using { body, .. }
            | S::Lock { body, .. }
            | S::Fixed { body, .. } => self.rethrow_from(body, caught, ty),
            S::Switch { sections, .. } => {
                for section in sections {
                    for statement in &mut section.statements {
                        self.rethrow_from(statement, caught, ty);
                    }
                }
            }
            S::Try { body, finally, .. } => {
                self.rethrow_from(body, caught, ty);
                if let Some(finally) = finally {
                    self.rethrow_from(finally, caught, ty);
                }
            }
            _ => {}
        }
    }

    /// `await using (var a = x, b = y) body` as the statements it means:
    ///
    /// ```text
    /// var a = x;
    /// try {
    ///     var b = y;
    ///     try { body } finally { if (b != null) await b.DisposeAsync(); }
    /// } finally { if (a != null) await a.DisposeAsync(); }
    /// ```
    ///
    /// Each `finally` is the disposal the binder wrote for its resource; a
    /// resource with none — the `dynamic` one, disposed through the
    /// `IAsyncDisposable` after it — is only declared.
    fn await_using(
        resources: Vec<rustlyn_semantics::BoundUsingResource>,
        body: BoundStatement,
        span: TextSpan,
    ) -> BoundStatement {
        let mut inner = body;
        for resource in resources.into_iter().rev() {
            let declare = BoundStatement::new(
                BoundStatementKind::LocalDeclaration {
                    local: resource.local,
                    initializer: Some(resource.value),
                },
                span,
            );
            let guarded = match resource.awaited {
                Some(disposal) => BoundStatement::new(
                    BoundStatementKind::Try {
                        body: Box::new(inner),
                        catches: Vec::new(),
                        finally: Some(disposal),
                    },
                    span,
                ),
                None => inner,
            };
            inner = BoundStatement::new(BoundStatementKind::Block(vec![declare, guarded]), span);
        }
        inner
    }

    /// `try { inside } finally { finally }` where the `finally` awaits.
    ///
    /// What comes back runs `inside` under a handler that only keeps the
    /// exception, then the `finally` in the open, then does what the `try`
    /// was leaving to do: rethrows, returns the parked value, or takes the
    /// `break` or `continue` that was heading past it.
    fn guard_awaiting_finally(
        &mut self,
        mut inside: Vec<BoundStatement>,
        finally: BoundStatement,
        span: TextSpan,
    ) -> Result<Vec<BoundStatement>, String> {
        let integer = self.integer.clone();
        let exception = self.exception.clone();
        let number = |value: i32| {
            BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Int32(value)),
                integer.clone(),
                span,
            )
        };
        self.guarded += 1;
        let label = format!("<>finally{}", self.guarded);
        let pending = self.temp(&exception, span);
        let branch = self.temp(&integer, span);
        let mut parked: Option<(LocalId, Type)> = None;
        // A `goto` to a label outside the `try` leaves it too.
        let mut exits = Exits {
            inside: labels_within(&inside),
            ..Exits::default()
        };
        for statement in &mut inside {
            self.redirect_exits(statement, &label, branch, &mut parked, &mut exits, 0, 0);
        }

        let mut out = vec![
            BoundStatement::new(
                BoundStatementKind::LocalDeclaration {
                    local: pending,
                    initializer: Some(BoundExpression::new(
                        BoundExpressionKind::Default(exception.clone()),
                        exception.clone(),
                        span,
                    )),
                },
                span,
            ),
            BoundStatement::new(
                BoundStatementKind::LocalDeclaration {
                    local: branch,
                    initializer: Some(number(0)),
                },
                span,
            ),
            BoundStatement::new(
                BoundStatementKind::Try {
                    body: Box::new(BoundStatement::new(BoundStatementKind::Block(inside), span)),
                    catches: vec![BoundCatch {
                        exception_type: exception.clone(),
                        local: Some(pending),
                        filter: None,
                        body: BoundStatement::new(BoundStatementKind::Empty, span),
                    }],
                    finally: None,
                },
                span,
            ),
            BoundStatement::new(BoundStatementKind::Label(label), span),
        ];
        out.push(self.nested(finally)?);

        // Rethrow what the `try` threw.
        let caught = BoundExpression::new(
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Inequality,
                left: Box::new(Self::read(pending, &exception, span)),
                right: Box::new(BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::Null),
                    Type::Null,
                    span,
                )),
            },
            self.boolean.clone(),
            span,
        );
        let rethrow = match self.rethrow {
            Some(throw) => BoundStatement::new(
                BoundStatementKind::Expression(BoundExpression::new(
                    BoundExpressionKind::Call {
                        receiver: None,
                        method: throw,
                        type_arguments: Vec::new(),
                        arguments: vec![Self::read(pending, &exception, span)],
                        virtual_call: false,
                    },
                    Type::Void,
                    span,
                )),
                span,
            ),
            None => BoundStatement::new(
                BoundStatementKind::Throw(Some(Self::read(pending, &exception, span))),
                span,
            ),
        };
        out.push(Self::when(caught, vec![rethrow], span));

        // Then leave the way the `try` was leaving.
        let took = |value: i32| {
            BoundExpression::new(
                BoundExpressionKind::Binary {
                    operator: BinaryOperator::Equality,
                    left: Box::new(Self::read(branch, &integer, span)),
                    right: Box::new(number(value)),
                },
                self.boolean.clone(),
                span,
            )
        };
        if exits.returns {
            let value = parked
                .as_ref()
                .map(|(local, ty)| Self::read(*local, ty, span));
            out.push(Self::when(
                took(RETURNED),
                vec![BoundStatement::new(BoundStatementKind::Return(value), span)],
                span,
            ));
        }
        for outward in &exits.breaks {
            out.push(Self::when(
                took(broke(*outward)),
                vec![BoundStatement::new(
                    BoundStatementKind::Break(*outward),
                    span,
                )],
                span,
            ));
        }
        for outward in &exits.continues {
            out.push(Self::when(
                took(continued(*outward)),
                vec![BoundStatement::new(
                    BoundStatementKind::Continue(*outward),
                    span,
                )],
                span,
            ));
        }
        for (position, target) in exits.gotos.iter().enumerate() {
            out.push(Self::when(
                took(went(position)),
                vec![BoundStatement::new(
                    BoundStatementKind::Goto(target.clone()),
                    span,
                )],
                span,
            ));
        }
        Ok(out)
    }

    /// Turns every way out of a guarded `try` — a `return`, or a `break` or
    /// `continue` aimed at something outside it — into a note of which and a
    /// jump to `label`, where the `finally` waits.
    ///
    /// `loops` and `breakable` count the loops and switches between the
    /// statement and the `try`: a `break` inside its own loop stays.
    #[allow(clippy::too_many_arguments)]
    fn redirect_exits(
        &mut self,
        statement: &mut BoundStatement,
        label: &str,
        branch: LocalId,
        parked: &mut Option<(LocalId, Type)>,
        exits: &mut Exits,
        loops: usize,
        breakable: usize,
    ) {
        use BoundStatementKind as S;
        let span = statement.span;
        let integer = self.integer.clone();
        let jump = |this: &mut Self, mark: i32, first: Option<BoundStatement>| {
            let mut statements = Vec::new();
            statements.extend(first);
            statements.push(Self::assign(
                branch,
                BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::Int32(mark)),
                    integer.clone(),
                    span,
                ),
                span,
            ));
            statements.push(BoundStatement::new(S::Goto(label.to_string()), span));
            let _ = this;
            S::Block(statements)
        };
        match &mut statement.kind {
            S::Return(value) => {
                exits.returns = true;
                let first = value.take().map(|value| {
                    let local = match parked {
                        Some((local, _)) => *local,
                        None => {
                            let local = self.temp(&value.ty, span);
                            *parked = Some((local, value.ty.clone()));
                            local
                        }
                    };
                    Self::assign(local, value, span)
                });
                statement.kind = jump(self, RETURNED, first);
            }
            S::Goto(target) if !exits.inside.contains(target.as_str()) => {
                let position = match exits.gotos.iter().position(|known| known == target) {
                    Some(position) => position,
                    None => {
                        exits.gotos.push(target.clone());
                        exits.gotos.len() - 1
                    }
                };
                statement.kind = jump(self, went(position), None);
            }
            // `break outer;` may leave more than the loop around the `try`:
            // what is left of its way out is taken after the `finally`.
            S::Break(outward) if *outward >= breakable => {
                let outward = *outward - breakable;
                exits.breaks.insert(outward);
                statement.kind = jump(self, broke(outward), None);
            }
            S::Continue(outward) if *outward >= loops => {
                let outward = *outward - loops;
                exits.continues.insert(outward);
                statement.kind = jump(self, continued(outward), None);
            }
            S::Block(statements) => {
                for statement in statements {
                    self.redirect_exits(statement, label, branch, parked, exits, loops, breakable);
                }
            }
            S::If {
                consequence,
                alternative,
                ..
            } => {
                self.redirect_exits(consequence, label, branch, parked, exits, loops, breakable);
                if let Some(alternative) = alternative {
                    self.redirect_exits(
                        alternative,
                        label,
                        branch,
                        parked,
                        exits,
                        loops,
                        breakable,
                    );
                }
            }
            S::While { body, .. } | S::DoWhile { body, .. } | S::ForEach { body, .. } => {
                self.redirect_exits(body, label, branch, parked, exits, loops + 1, breakable + 1);
            }
            S::For {
                initializers, body, ..
            } => {
                for statement in initializers {
                    self.redirect_exits(statement, label, branch, parked, exits, loops, breakable);
                }
                self.redirect_exits(body, label, branch, parked, exits, loops + 1, breakable + 1);
            }
            S::Using { body, .. } | S::Lock { body, .. } | S::Fixed { body, .. } => {
                self.redirect_exits(body, label, branch, parked, exits, loops, breakable);
            }
            S::Switch { sections, .. } => {
                for section in sections {
                    for statement in &mut section.statements {
                        self.redirect_exits(
                            statement,
                            label,
                            branch,
                            parked,
                            exits,
                            loops,
                            breakable + 1,
                        );
                    }
                }
            }
            S::Try {
                body,
                catches,
                finally,
            } => {
                self.redirect_exits(body, label, branch, parked, exits, loops, breakable);
                for catch in catches {
                    self.redirect_exits(
                        &mut catch.body,
                        label,
                        branch,
                        parked,
                        exits,
                        loops,
                        breakable,
                    );
                }
                if let Some(finally) = finally {
                    self.redirect_exits(finally, label, branch, parked, exits, loops, breakable);
                }
            }
            _ => {}
        }
    }

    /// A statement in a position that holds exactly one: what it turns into
    /// is put back as a block where it turned into several.
    fn nested(&mut self, statement: BoundStatement) -> Result<BoundStatement, String> {
        let span = statement.span;
        let mut out = Vec::new();
        self.statement(statement, &mut out)?;
        Ok(if out.len() == 1 {
            out.pop().expect("one statement")
        } else {
            BoundStatement::new(BoundStatementKind::Block(out), span)
        })
    }

    /// Rewrites an expression so that no `await` is left inside it.
    fn expression(
        &mut self,
        expression: &mut BoundExpression,
        prelude: &mut Vec<BoundStatement>,
    ) -> Result<(), String> {
        if !self.holds(expression) {
            return Ok(());
        }
        let span = expression.span;
        // The statements go first, themselves hoisted, and the value stays;
        // anything the value still holds comes out after them.
        if let BoundExpressionKind::SpillSequence { statements, value } = &mut expression.kind {
            let statements = std::mem::take(statements);
            let value = std::mem::replace(
                &mut **value,
                BoundExpression::new(BoundExpressionKind::Sequence(Vec::new()), Type::Void, span),
            );
            for statement in statements {
                self.statement(statement, prelude)?;
            }
            *expression = value;
            return self.expression(expression, prelude);
        }
        // A sequence's steps before the last are done for what they do: the
        // ones up to the last that holds what comes out become statements,
        // in order, and the rest stay. The one that holds it is left as
        // what it comes to, and goes where that is nothing.
        //
        // Waiting keeps the steps before it where they stand where one of
        // them is a `ref struct`: one a step makes (the span a slice is taken
        // from) may not outlive the `await`, and is made again after it by
        // the path below. Anything else — the handler an interpolated string
        // is appended to, and the appends before the hole that waits — goes
        // ahead as it would: a local keeps it across the `await`.
        let holding = match &expression.kind {
            BoundExpressionKind::Sequence(steps) => steps
                .iter()
                .rposition(|step| self.holds(step))
                .filter(|last| {
                    self.hoisting == Hoisting::Sequences
                        || steps[..*last]
                            .iter()
                            .all(|step| matches!(step.ty, Type::Void) || !(self.ref_like)(&step.ty))
                }),
            _ => None,
        };
        if let Some(last) = holding
            && let BoundExpressionKind::Sequence(steps) = &mut expression.kind
        {
            let rest = steps.split_off(last);
            let before = std::mem::replace(steps, rest);
            for mut step in before {
                self.expression(&mut step, prelude)?;
                let at = step.span;
                prelude.push(BoundStatement::new(
                    BoundStatementKind::Expression(step),
                    at,
                ));
            }
            let BoundExpressionKind::Sequence(steps) = &mut expression.kind else {
                unreachable!("matched a sequence above");
            };
            self.expression(&mut steps[0], prelude)?;
            if self.hoisting == Hoisting::Sequences
                && steps.len() > 1
                && matches!(steps[0].ty, Type::Void)
            {
                let done = steps.remove(0);
                let at = done.span;
                prelude.push(BoundStatement::new(
                    BoundStatementKind::Expression(done),
                    at,
                ));
            }
            return Ok(());
        }
        if let BoundExpressionKind::Await { operand, .. } = &mut expression.kind
            && self.hoisting == Hoisting::Awaits
        {
            self.expression(operand, prelude)?;
            if matches!(expression.ty, Type::Void) {
                return Err(
                    "an `await` of nothing in the middle of an expression is not rewritten yet"
                        .to_string(),
                );
            }
            let temp = self.temp(&expression.ty, span);
            let ty = expression.ty.clone();
            let awaited = std::mem::replace(
                expression,
                BoundExpression::new(BoundExpressionKind::Local(temp), ty, span),
            );
            prelude.push(BoundStatement::new(
                BoundStatementKind::LocalDeclaration {
                    local: temp,
                    initializer: Some(awaited),
                },
                span,
            ));
            return Ok(());
        }
        // Where the operands after the first are evaluated only sometimes,
        // moving an `await` out of them would evaluate it always. `a && await
        // b` becomes `t = a; if (t) t = await b;`, and a conditional an `if`
        // with a branch per arm; the rest are refused.
        let ty = expression.ty.clone();
        match &mut expression.kind {
            // `new T(a) { X = await e }` is made first, into a temporary,
            // and each initializer then writes it in turn, as a statement of
            // its own: the object an initializer is written against exists
            // before anything of it runs (Roslyn lowers the initializer into
            // such a sequence before it spills). `r with { X = await e }` is
            // the copy made first the same way.
            BoundExpressionKind::ObjectCreation { initializers, .. }
            | BoundExpressionKind::With { initializers, .. }
                if initializers
                    .iter()
                    .any(|initializer| self.holds(initializer)) =>
            {
                let initializers = std::mem::take(initializers);
                self.expression(expression, prelude)?;
                let made = self.temp(&ty, span);
                let creation = std::mem::replace(expression, Self::read(made, &ty, span));
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: made,
                        initializer: Some(creation),
                    },
                    span,
                ));
                for mut initializer in initializers {
                    written_into(&mut initializer, made);
                    self.expression(&mut initializer, prelude)?;
                    let at = initializer.span;
                    prelude.push(BoundStatement::new(
                        BoundStatementKind::Expression(initializer),
                        at,
                    ));
                }
                return Ok(());
            }
            BoundExpressionKind::Binary {
                operator,
                left,
                right,
            } if matches!(
                operator,
                BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr
            ) && self.holds(right) =>
            {
                let and = *operator == BinaryOperator::LogicalAnd;
                self.expression(left, prelude)?;
                let temp = self.temp(&ty, span);
                let first = std::mem::replace(&mut **left, Self::read(temp, &ty, span));
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: temp,
                        initializer: Some(first),
                    },
                    span,
                ));
                let mut rest = Vec::new();
                self.expression(right, &mut rest)?;
                let second = std::mem::replace(&mut **right, Self::read(temp, &ty, span));
                rest.push(Self::assign(temp, second, span));
                let test = Self::read(temp, &ty, span);
                let test = if and { test } else { self.not(test) };
                prelude.push(Self::when(test, rest, span));
                *expression = Self::read(temp, &ty, span);
                return Ok(());
            }
            // `a ?? await b` is `l = a; if (l == null) r = await b;` and
            // then `l ?? r`, which reads `r` only where it was assigned.
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Coalesce,
                left,
                right,
            } if self.holds(right) && !matches!(left.ty, Type::Null) => {
                self.expression(left, prelude)?;
                let left_type = left.ty.clone();
                let held = self.temp(&left_type, span);
                let first = std::mem::replace(&mut **left, Self::read(held, &left_type, span));
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: held,
                        initializer: Some(first),
                    },
                    span,
                ));
                let right_type = right.ty.clone();
                let mut rest = Vec::new();
                self.expression(right, &mut rest)?;
                // `a ?? throw await e` makes the exception where the left is
                // null, and the throw, which has no value to keep, reads it
                // in place.
                if matches!(right.kind, BoundExpressionKind::Throw(_)) {
                    prelude.push(Self::when(
                        Self::is_null(Self::read(held, &left_type, span), &self.boolean),
                        rest,
                        span,
                    ));
                    return Ok(());
                }
                let other = self.temp(&right_type, span);
                let second = std::mem::replace(&mut **right, Self::read(other, &right_type, span));
                rest.push(Self::assign(other, second, span));
                prelude.push(Self::when(
                    Self::is_null(Self::read(held, &left_type, span), &self.boolean),
                    rest,
                    span,
                ));
                return Ok(());
            }
            // `c ? ref (await a).F : ref b.F` chooses a variable, which no
            // temporary can hold: each branch's `await`s run in an `if` of its
            // own, and the choice is made again after them from what they
            // left behind.
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } if (self.holds(consequence) || self.holds(alternative))
                && matches!(consequence.kind, BoundExpressionKind::RefArgument { .. })
                && matches!(alternative.kind, BoundExpressionKind::RefArgument { .. }) =>
            {
                self.expression(condition, prelude)?;
                let test_type = condition.ty.clone();
                let test = self.temp(&test_type, span);
                let chosen =
                    std::mem::replace(&mut **condition, Self::read(test, &test_type, span));
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: test,
                        initializer: Some(chosen),
                    },
                    span,
                ));
                let mut then = Vec::new();
                self.expression(consequence, &mut then)?;
                let mut otherwise = Vec::new();
                self.expression(alternative, &mut otherwise)?;
                prelude.push(BoundStatement::new(
                    BoundStatementKind::If {
                        condition: Self::read(test, &test_type, span),
                        consequence: Box::new(BoundStatement::new(
                            BoundStatementKind::Block(then),
                            span,
                        )),
                        alternative: Some(Box::new(BoundStatement::new(
                            BoundStatementKind::Block(otherwise),
                            span,
                        ))),
                    },
                    span,
                ));
                return Ok(());
            }
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } if self.holds(consequence) || self.holds(alternative) => {
                self.expression(condition, prelude)?;
                let temp = self.temp(&ty, span);
                let mut then = Vec::new();
                self.expression(consequence, &mut then)?;
                let chosen = std::mem::replace(&mut **consequence, Self::read(temp, &ty, span));
                then.push(Self::assign(temp, chosen, span));
                let mut otherwise = Vec::new();
                self.expression(alternative, &mut otherwise)?;
                let chosen = std::mem::replace(&mut **alternative, Self::read(temp, &ty, span));
                otherwise.push(Self::assign(temp, chosen, span));
                let test = std::mem::replace(&mut **condition, Self::read(temp, &ty, span));
                prelude.push(BoundStatement::new(
                    BoundStatementKind::If {
                        condition: test,
                        consequence: Box::new(BoundStatement::new(
                            BoundStatementKind::Block(then),
                            span,
                        )),
                        alternative: Some(Box::new(BoundStatement::new(
                            BoundStatementKind::Block(otherwise),
                            span,
                        ))),
                    },
                    span,
                ));
                *expression = Self::read(temp, &ty, span);
                return Ok(());
            }
            // `a?.M(await b)`: `r = a; if (r != null) { the awaits of the
            // access }`, and then `r?.M(...)` with them read back. The
            // access names `r` itself from then on, which is what its
            // placeholder stood for — or, for a `T?`, the value inside it.
            BoundExpressionKind::ConditionalAccess { receiver, access } if self.holds(access) => {
                let nullable = self.is_nullable_value(&receiver.ty);
                self.expression(receiver, prelude)?;
                // An element or a field is a place: what locates it is kept,
                // and the place is read again, so that a struct's method
                // still works on the element rather than on a copy.
                let place = matches!(
                    receiver.kind,
                    BoundExpressionKind::ArrayAccess { .. } | BoundExpressionKind::Field { .. }
                );
                if place {
                    for part in children_mut(receiver) {
                        if !is_pure(part) {
                            let part_type = part.ty.clone();
                            let held = self.temp(&part_type, span);
                            let value =
                                std::mem::replace(&mut *part, Self::read(held, &part_type, span));
                            prelude.push(BoundStatement::new(
                                BoundStatementKind::LocalDeclaration {
                                    local: held,
                                    initializer: Some(value),
                                },
                                span,
                            ));
                        }
                    }
                } else if !is_pure(receiver) {
                    let receiver_type = receiver.ty.clone();
                    let held = self.temp(&receiver_type, span);
                    let value =
                        std::mem::replace(&mut **receiver, Self::read(held, &receiver_type, span));
                    prelude.push(BoundStatement::new(
                        BoundStatementKind::LocalDeclaration {
                            local: held,
                            initializer: Some(value),
                        },
                        span,
                    ));
                }
                if nullable {
                    let value = self.value_inside((**receiver).clone(), span)?;
                    replace_accessed_value(access, &value);
                } else {
                    replace_accessed_value(access, receiver);
                }
                let mut rest = Vec::new();
                self.expression(access, &mut rest)?;
                let test = self.not(Self::is_null((**receiver).clone(), &self.boolean));
                prelude.push(Self::when(test, rest, span));
                return Ok(());
            }
            // A `switch` expression whose arms await is the chain of tests it
            // means, each arm's `when` and value run only where its pattern
            // matched:
            //
            // ```text
            // g = x;
            // if (g is p1) { w = when1; if (w) { r = value1; goto end; } }
            // ...
            // r = g switch { };  // throws: nothing matched
            // end:
            // ```
            BoundExpressionKind::Switch { governing, arms }
                if arms.iter().any(|arm| {
                    self.holds(&arm.value)
                        || arm.when.as_ref().is_some_and(|value| self.holds(value))
                }) =>
            {
                self.expression(governing, prelude)?;
                let governing_type = governing.ty.clone();
                let held = self.temp(&governing_type, span);
                let value =
                    std::mem::replace(&mut **governing, Self::read(held, &governing_type, span));
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: held,
                        initializer: Some(value),
                    },
                    span,
                ));
                let result = self.temp(&ty, span);
                self.guarded += 1;
                let end = format!("<>switch{}", self.guarded);
                for arm in std::mem::take(arms) {
                    let arm_span = arm.value.span;
                    let mut chosen = Vec::new();
                    let mut value = arm.value;
                    self.expression(&mut value, &mut chosen)?;
                    chosen.push(Self::assign(result, value, arm_span));
                    chosen.push(BoundStatement::new(
                        BoundStatementKind::Goto(end.clone()),
                        arm_span,
                    ));
                    let matched = match arm.when {
                        Some(mut when) => {
                            let mut tested = Vec::new();
                            self.expression(&mut when, &mut tested)?;
                            tested.push(Self::when(when, chosen, arm_span));
                            tested
                        }
                        None => chosen,
                    };
                    let test = BoundExpression::new(
                        BoundExpressionKind::IsPattern {
                            operand: Box::new(Self::read(held, &governing_type, span)),
                            pattern: Box::new(arm.pattern),
                        },
                        self.boolean.clone(),
                        arm_span,
                    );
                    prelude.push(Self::when(test, matched, arm_span));
                }
                // Nothing matched: the empty `switch` throws what the full one
                // would have.
                let unmatched = BoundExpression::new(
                    BoundExpressionKind::Switch {
                        governing: Box::new(Self::read(held, &governing_type, span)),
                        arms: Vec::new(),
                    },
                    ty.clone(),
                    span,
                );
                prelude.push(Self::assign(result, unmatched, span));
                prelude.push(BoundStatement::new(BoundStatementKind::Label(end), span));
                *expression = Self::read(result, &ty, span);
                return Ok(());
            }
            _ => {}
        }
        // A receiver of a type parameter is kept as it was before an `await`
        // among the arguments: `item.M(await F(ref item))` calls `M` on the
        // instance `item` held when the call began (Roslyn spills it). So is
        // the receiver of what an assignment writes to, where the `await` is
        // in the value: `item.P += await F(ref item)`.
        let has_receiver = matches!(
            &expression.kind,
            BoundExpressionKind::Call {
                receiver: Some(_),
                ..
            } | BoundExpressionKind::Property {
                receiver: Some(_),
                ..
            } | BoundExpressionKind::IndexerAccess { .. }
        );
        // The target of an assignment lists its own parts, the receiver first.
        let has_receiver = has_receiver
            || matches!(
                &expression.kind,
                BoundExpressionKind::Assignment { target, .. }
                    | BoundExpressionKind::CompoundAssignment { target, .. }
                    | BoundExpressionKind::Increment { target, .. }
                    if matches!(
                        target.kind,
                        BoundExpressionKind::Property {
                            receiver: Some(_),
                            ..
                        } | BoundExpressionKind::IndexerAccess { .. }
                    )
            );
        let indexes_assigned = matches!(
            &expression.kind,
            BoundExpressionKind::Assignment { target, .. }
                | BoundExpressionKind::CompoundAssignment { target, .. }
                if matches!(target.kind, BoundExpressionKind::IndexerAccess { .. })
        );
        let indexes = indexes_assigned
            || match &expression.kind {
                BoundExpressionKind::IndexerAccess { .. } => true,
                BoundExpressionKind::Increment { target, .. } => {
                    matches!(target.kind, BoundExpressionKind::IndexerAccess { .. })
                }
                _ => false,
            };
        // What an assignment writes to a field or an element is located
        // before the value's `await` and written after it: `a.x = await y`
        // writes to the object `a` held before, and `arr[i] = await y` to
        // that array at that index, whatever the `await` did to `a`, `arr`
        // or `i` (Roslyn spills the left side as a location).
        // A property's or an indexer's setter is a call, whose receiver and
        // arguments come before the value the same way — the receiver kept
        // as the place it is where it is a struct. A receiver of a type
        // parameter has its own keeping below.
        let locating = match &expression.kind {
            BoundExpressionKind::Assignment { target, .. }
            | BoundExpressionKind::CompoundAssignment { target, .. } => match &target.kind {
                BoundExpressionKind::Field {
                    receiver: Some(receiver),
                    ..
                } => Some(!receiver.ty.is_reference_type(self.symbols)),
                BoundExpressionKind::ArrayAccess { .. } => Some(false),
                BoundExpressionKind::Property {
                    receiver: Some(receiver),
                    ..
                }
                | BoundExpressionKind::IndexerAccess { receiver, .. }
                    if !matches!(
                        receiver.kind,
                        BoundExpressionKind::TypeExpression(_)
                            | BoundExpressionKind::This
                            | BoundExpressionKind::Base
                    ) && !matches!(receiver.ty, Type::TypeParameter(_) | Type::Dynamic) =>
                {
                    Some(!receiver.ty.is_reference_type(self.symbols))
                }
                _ => None,
            },
            _ => None,
        };
        let mut children = children_mut(expression);
        let Some(last) = children.iter().rposition(|child| self.holds(child)) else {
            return Ok(());
        };
        let mut value_starts = None;
        let mut kept: Option<(BoundExpression, BoundExpression)> = None;
        let count = children.len();
        // `item[^i]`: the length the index counts back from is read off the
        // receiver kept, not off the variable again. An assignment's value
        // comes after the indexer's arguments and is not one of them.
        let arguments_end = if indexes_assigned { count - 1 } else { count };
        for (index, child) in children.iter_mut().enumerate().take(last + 1) {
            // Where the value of an assignment is what awaits.
            if index == last && last + 1 == count {
                value_starts = Some(prelude.len());
            }
            if indexes
                && index < arguments_end
                && let Some((before, after)) = &kept
            {
                self.count_from(child, before, after);
            }
            self.expression(child, prelude)?;
            // A part of the place an assignment writes, ahead of an `await`
            // in the value: a struct's field is still a place, and what
            // locates it is kept; anything else is kept as a value.
            if let Some(struct_receiver) = locating
                && index < last
                && index + 1 < count
            {
                // Only the receiver can be a struct's place; an index is a
                // value.
                if struct_receiver && index == 0 {
                    self.spill_location(child, prelude);
                } else {
                    self.spill_value(child, prelude);
                }
                continue;
            }
            if index == 0 && index < last && has_receiver {
                let before = (**child).clone();
                if self.keep_receiver(child, prelude) {
                    kept = Some((before, (**child).clone()));
                    continue;
                }
            }
            // Everything evaluated ahead of the `await` that is not a plain
            // read is kept in a temporary, so that it is evaluated first
            // still. A place passed by reference stays a place — except
            // one an `in` parameter takes that a call reaches, whose
            // reference could not be kept across the `await`: Roslyn passes
            // a copy of its value then, and so does this.
            if index < last
                && let BoundExpressionKind::RefArgument {
                    kind: RefKind::In,
                    operand,
                } = &mut child.kind
                && reaches_through_a_call(operand)
            {
                let span = operand.span;
                let ty = operand.ty.clone();
                let temp = self.temp(&ty, span);
                let taken = std::mem::replace(
                    &mut **operand,
                    BoundExpression::new(BoundExpressionKind::Local(temp), ty, span),
                );
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: temp,
                        initializer: Some(taken),
                    },
                    span,
                ));
                continue;
            }
            // An element or field of a value type (or an element of a `T`
            // that may be one) is a place a call may be made on: what locates
            // it is kept instead of a copy of it, so the call still reaches
            // it.
            if index < last
                && matches!(
                    child.kind,
                    BoundExpressionKind::ArrayAccess { .. } | BoundExpressionKind::Field { .. }
                )
                && !child.ty.is_reference_type(self.symbols)
                // A field of a `T` that may turn out a class is read before
                // the `await`, as its value (`Program<T>.F[0] += await x`);
                // one of a `T : struct` is a place like any struct's.
                && !(matches!(child.kind, BoundExpressionKind::Field { .. })
                    && self.either_kind(&child.ty))
            {
                for part in children_mut(child) {
                    if !is_pure(part) {
                        let span = part.span;
                        let ty = part.ty.clone();
                        let temp = self.temp(&ty, span);
                        let taken = std::mem::replace(
                            &mut *part,
                            BoundExpression::new(BoundExpressionKind::Local(temp), ty, span),
                        );
                        prelude.push(BoundStatement::new(
                            BoundStatementKind::LocalDeclaration {
                                local: temp,
                                initializer: Some(taken),
                            },
                            span,
                        ));
                    }
                }
                continue;
            }
            if index < last
                && !is_pure(child)
                && !matches!(child.kind, BoundExpressionKind::RefArgument { .. })
            {
                // A `ref struct` may not outlast the `await` (a field may
                // never be one), so what is kept is what it was made from,
                // and it is made again after.
                if self.holds_ref_like(child) {
                    self.spill_parts(child, prelude);
                    continue;
                }
                let span = child.span;
                let ty = child.ty.clone();
                let temp = self.temp(&ty, span);
                let taken = std::mem::replace(
                    &mut **child,
                    BoundExpression::new(BoundExpressionKind::Local(temp), ty, span),
                );
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: temp,
                        initializer: Some(taken),
                    },
                    span,
                ));
            }
        }
        drop(children);
        // `item.P += await x` reads `item.P` before the `await` and writes it
        // after: `old = item.P; ...; item.P = (old += x)`, where the inner
        // compound assignment does the operation as the outer one would.
        if let Some(at) = value_starts
            && let BoundExpressionKind::CompoundAssignment {
                target,
                operator,
                value,
            } = &mut expression.kind
            && *operator != BinaryOperator::Coalesce
            && matches!(
                target.kind,
                BoundExpressionKind::Property { .. }
                    | BoundExpressionKind::IndexerAccess { .. }
                    | BoundExpressionKind::Field { .. }
                    | BoundExpressionKind::ArrayAccess { .. }
            )
            && !matches!(target.ty, Type::Dynamic)
            && !matches!(value.ty, Type::Dynamic)
        {
            let span = target.span;
            let target_type = target.ty.clone();
            let old = self.temp(&target_type, span);
            prelude.insert(
                at,
                BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: old,
                        initializer: Some((**target).clone()),
                    },
                    span,
                ),
            );
            let operator = *operator;
            let value = std::mem::replace(&mut **value, BoundExpression::error(span));
            let target = std::mem::replace(&mut **target, BoundExpression::error(span));
            let ty = expression.ty.clone();
            let changed = BoundExpression::new(
                BoundExpressionKind::CompoundAssignment {
                    target: Box::new(BoundExpression::new(
                        BoundExpressionKind::Local(old),
                        target_type,
                        span,
                    )),
                    operator,
                    value: Box::new(value),
                },
                ty.clone(),
                span,
            );
            expression.kind = BoundExpressionKind::Assignment {
                target: Box::new(target),
                value: Box::new(changed),
            };
        }
        // `item.P ??= await x` reads `item.P` first, and awaits only where it
        // was null: `old = item.P; if (old is null) { ...; old = (item.P = v); }`
        // and then `old ??= v`, which finds `old` set either way and gives
        // back what `??=` gives. A local is the same: `i ??= await x` runs
        // nothing of `x` where `i` has a value.
        if let Some(at) = value_starts
            && let BoundExpressionKind::CompoundAssignment {
                target,
                operator: BinaryOperator::Coalesce,
                value,
            } = &mut expression.kind
            && matches!(
                target.kind,
                BoundExpressionKind::Property { .. }
                    | BoundExpressionKind::IndexerAccess { .. }
                    | BoundExpressionKind::Field { .. }
                    | BoundExpressionKind::ArrayAccess { .. }
                    | BoundExpressionKind::Local(_)
                    | BoundExpressionKind::Parameter(_)
            )
            && !matches!(target.ty, Type::Dynamic)
        {
            let span = target.span;
            let target_type = target.ty.clone();
            let value_type = value.ty.clone();
            let mut awaited = prelude.split_off(at);
            let old = self.temp(&target_type, span);
            let given = self.temp(&value_type, span);
            let read = |local: LocalId, ty: &Type| {
                BoundExpression::new(BoundExpressionKind::Local(local), ty.clone(), span)
            };
            let value = std::mem::replace(&mut **value, read(given, &value_type));
            awaited.push(BoundStatement::new(
                BoundStatementKind::LocalDeclaration {
                    local: given,
                    initializer: Some(value),
                },
                span,
            ));
            awaited.push(Self::assign(
                old,
                BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: target.clone(),
                        value: Box::new(read(given, &value_type)),
                    },
                    target_type.clone(),
                    span,
                ),
                span,
            ));
            let target = std::mem::replace(&mut **target, read(old, &target_type));
            prelude.push(BoundStatement::new(
                BoundStatementKind::LocalDeclaration {
                    local: old,
                    initializer: Some(target),
                },
                span,
            ));
            let is_null = BoundExpression::new(
                BoundExpressionKind::IsPattern {
                    operand: Box::new(read(old, &target_type)),
                    pattern: Box::new(BoundPattern::new(
                        BoundPatternKind::Constant(BoundExpression::new(
                            BoundExpressionKind::Literal(ConstantValue::Null),
                            Type::Null,
                            span,
                        )),
                        span,
                    )),
                },
                self.boolean.clone(),
                span,
            );
            prelude.push(BoundStatement::new(
                BoundStatementKind::If {
                    condition: is_null,
                    consequence: Box::new(BoundStatement::new(
                        BoundStatementKind::Block(awaited),
                        span,
                    )),
                    alternative: None,
                },
                span,
            ));
        }
        Ok(())
    }
}

impl Spiller<'_> {
    /// Keeps a value in a temporary, ahead of an `await`, unless it cannot
    /// change: a constant, `this`, or a temporary of the spiller's own
    /// (Roslyn's `Spill` of an expression by value).
    fn spill_value(&mut self, value: &mut BoundExpression, prelude: &mut Vec<BoundStatement>) {
        match &value.kind {
            BoundExpressionKind::Literal(_)
            | BoundExpressionKind::This
            | BoundExpressionKind::Base
            | BoundExpressionKind::TypeExpression(_)
            | BoundExpressionKind::Default(_) => return,
            BoundExpressionKind::Local(local)
                if self
                    .locals
                    .get(local.0 as usize)
                    .is_some_and(|slot| slot.name.starts_with("<>s__") || slot.by_ref) =>
            {
                return;
            }
            _ => {}
        }
        if self.holds_ref_like(value) {
            self.spill_parts(value, prelude);
            return;
        }
        let span = value.span;
        let ty = value.ty.clone();
        let temp = self.temp(&ty, span);
        let taken = std::mem::replace(
            value,
            BoundExpression::new(BoundExpressionKind::Local(temp), ty, span),
        );
        prelude.push(BoundStatement::new(
            BoundStatementKind::LocalDeclaration {
                local: temp,
                initializer: Some(taken),
            },
            span,
        ));
    }

    /// Keeps what locates a struct whose field an assignment writes, ahead
    /// of an `await` in the value, leaving the struct itself to be reached
    /// after it (Roslyn's `fieldWithSpilledReceiver`): a local or a
    /// parameter is a place already; a field of a class is reached through
    /// the object, kept, and an element through the array and the indices,
    /// kept — and either is read once there and then, for nothing but the
    /// exception it throws, since `a.b.x = await e` fails on a null `a`
    /// before `e` runs where `a.x = await e` fails only on the store.
    fn spill_location(&mut self, place: &mut BoundExpression, prelude: &mut Vec<BoundStatement>) {
        let touch = |place: &BoundExpression, prelude: &mut Vec<BoundStatement>| {
            prelude.push(BoundStatement::new(
                BoundStatementKind::Expression(place.clone()),
                place.span,
            ));
        };
        match &mut place.kind {
            BoundExpressionKind::Field {
                receiver: Some(receiver),
                ..
            } => {
                if receiver.ty.is_reference_type(self.symbols) {
                    self.spill_value(receiver, prelude);
                    touch(place, prelude);
                } else {
                    self.spill_location(receiver, prelude);
                }
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                self.spill_value(array, prelude);
                for index in indices {
                    self.spill_value(index, prelude);
                }
                touch(place, prelude);
            }
            BoundExpressionKind::Dereference { operand } => self.spill_value(operand, prelude),
            _ => {}
        }
    }

    /// Whether values of a type are references: a class, or a type
    /// parameter constrained to be one.
    /// Keeps a receiver of a type parameter, a variable, as it is before an
    /// `await`: a `T : class` as a copy, and a `T` that may be either as a
    /// copy read where `T` turns out to be a class and the variable itself
    /// where it is a struct (Roslyn's `BoundComplexConditionalReceiver`).
    /// Whether it did.
    fn keep_receiver(
        &mut self,
        receiver: &mut BoundExpression,
        prelude: &mut Vec<BoundStatement>,
    ) -> bool {
        let (by_reference, either) = (
            self.held_by_reference(&receiver.ty),
            self.either_kind(&receiver.ty),
        );
        match receiver.kind {
            BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
                if by_reference || either => {}
            // An element of a `T[]` is kept as the array and the index, and
            // read as a copy where `T` is a class: the array may be one of
            // a derived type, which `ldelema` on it would refuse. A field of
            // a `T` is kept as the object it is read from.
            BoundExpressionKind::ArrayAccess { .. }
            | BoundExpressionKind::Field {
                receiver: Some(_), ..
            } if either => {
                for part in children_mut(receiver) {
                    if !is_pure(part) {
                        let span = part.span;
                        let ty = part.ty.clone();
                        let temp = self.temp(&ty, span);
                        let taken = std::mem::replace(
                            &mut *part,
                            BoundExpression::new(BoundExpressionKind::Local(temp), ty, span),
                        );
                        prelude.push(BoundStatement::new(
                            BoundStatementKind::LocalDeclaration {
                                local: temp,
                                initializer: Some(taken),
                            },
                            span,
                        ));
                    }
                }
            }
            _ => return false,
        }
        let span = receiver.span;
        let ty = receiver.ty.clone();
        let temp = self.temp(&ty, span);
        prelude.push(BoundStatement::new(
            BoundStatementKind::LocalDeclaration {
                local: temp,
                initializer: Some(receiver.clone()),
            },
            span,
        ));
        let copy = BoundExpression::new(BoundExpressionKind::Local(temp), ty.clone(), span);
        if by_reference {
            *receiver = copy;
            return true;
        }
        let by_reference = |operand: BoundExpression| {
            BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind: RefKind::Ref,
                    operand: Box::new(operand),
                },
                ty.clone(),
                span,
            )
        };
        let variable = std::mem::replace(receiver, BoundExpression::error(span));
        let default_is_null = BoundExpression::new(
            BoundExpressionKind::IsPattern {
                operand: Box::new(BoundExpression::new(
                    BoundExpressionKind::Default(ty.clone()),
                    ty.clone(),
                    span,
                )),
                pattern: Box::new(BoundPattern::new(
                    BoundPatternKind::Constant(BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Null),
                        Type::Null,
                        span,
                    )),
                    span,
                )),
            },
            self.boolean.clone(),
            span,
        );
        *receiver = BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(default_is_null),
                consequence: Box::new(by_reference(copy)),
                alternative: Box::new(by_reference(variable)),
            },
            ty,
            span,
        );
        true
    }

    /// Points the `Length` or `Count` an `Index` or a `Range` is counted
    /// from (`i.GetOffset(item.Length)`) at the receiver kept for `item`.
    fn count_from(
        &self,
        expression: &mut BoundExpression,
        variable: &BoundExpression,
        kept: &BoundExpression,
    ) {
        if let BoundExpressionKind::Call {
            method, arguments, ..
        } = &mut expression.kind
            && matches!(
                self.symbols.get(*method).name.as_str(),
                "GetOffset" | "GetOffsetAndLength"
            )
        {
            for argument in arguments {
                if let BoundExpressionKind::Property {
                    receiver: Some(receiver),
                    property,
                } = &mut argument.kind
                    && matches!(
                        self.symbols.get(*property).name.as_str(),
                        "Length" | "Count"
                    )
                    && match (&receiver.kind, &variable.kind) {
                        (BoundExpressionKind::Local(a), BoundExpressionKind::Local(b)) => a == b,
                        (BoundExpressionKind::Parameter(a), BoundExpressionKind::Parameter(b)) => {
                            a == b
                        }
                        _ => false,
                    }
                {
                    **receiver = kept.clone();
                }
            }
            return;
        }
        for child in children_mut(expression) {
            self.count_from(child, variable, kept);
        }
    }

    /// Whether a type is a type parameter that may be a class or a struct.
    fn either_kind(&self, ty: &Type) -> bool {
        matches!(ty, Type::TypeParameter(parameter) if self
            .symbols
            .get(*parameter)
            .as_type_parameter()
            .is_some_and(|detail| !detail.reference_type && !detail.value_type))
    }

    fn held_by_reference(&self, ty: &Type) -> bool {
        match ty {
            Type::TypeParameter(parameter) => self
                .symbols
                .get(*parameter)
                .as_type_parameter()
                .is_some_and(|detail| detail.reference_type),
            _ => ty.is_reference_type(self.symbols),
        }
    }

    /// Keeps in temporaries the parts of a value that cannot itself be kept —
    /// a `ref struct` such as the span over an inline array — so that only
    /// the last step is left to evaluate after the `await`. A place passed by
    /// reference keeps what it is reached through: the object a field is
    /// read from, and not the field.
    /// Whether an expression is, or reads, a `ref struct`.
    fn holds_ref_like(&self, expression: &mut BoundExpression) -> bool {
        (self.ref_like)(&expression.ty)
            || children_mut(expression)
                .into_iter()
                .any(|child| self.holds_ref_like(child))
    }

    fn spill_parts(&mut self, expression: &mut BoundExpression, prelude: &mut Vec<BoundStatement>) {
        for child in children_mut(expression) {
            if let BoundExpressionKind::RefArgument { operand, .. } = &mut child.kind {
                self.spill_parts(operand, prelude);
            } else if is_pure(child) || reads_a_local(child) {
                // `taken.Item1` of a local an earlier step of the sequence
                // assigns is read where it stands: kept ahead of the
                // `await`, it would be read before that step ran.
            } else if self.holds_ref_like(child) {
                // What reads a `ref struct` — the length of a span, a slice
                // of it — is made again after the `await` like the span
                // itself; only its other parts are kept.
                self.spill_parts(child, prelude);
            } else {
                let span = child.span;
                let ty = child.ty.clone();
                let temp = self.temp(&ty, span);
                let taken = std::mem::replace(
                    &mut *child,
                    BoundExpression::new(BoundExpressionKind::Local(temp), ty, span),
                );
                prelude.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: temp,
                        initializer: Some(taken),
                    },
                    span,
                ));
            }
        }
    }
}

/// Whether a variable is reached through a call: `M().f`, `M()[0]`.
fn reaches_through_a_call(place: &BoundExpression) -> bool {
    match &place.kind {
        BoundExpressionKind::Call { .. } | BoundExpressionKind::IndexerAccess { .. } => true,
        BoundExpressionKind::Field {
            receiver: Some(receiver),
            ..
        } => reaches_through_a_call(receiver),
        _ => false,
    }
}

/// Whether an expression reads a field of a local, and nothing else.
fn reads_a_local(expression: &BoundExpression) -> bool {
    match &expression.kind {
        BoundExpressionKind::Local(_) => true,
        BoundExpressionKind::Field {
            receiver: Some(receiver),
            ..
        } => reads_a_local(receiver),
        _ => false,
    }
}

/// Puts `with` where an access written against `?.`'s placeholder reads
/// it — but not inside a nested `?.`, whose placeholder is its own.
fn replace_accessed_value(expression: &mut BoundExpression, with: &BoundExpression) {
    if matches!(expression.kind, BoundExpressionKind::AccessedValue) {
        *expression = with.clone();
        return;
    }
    if let BoundExpressionKind::ConditionalAccess { receiver, .. } = &mut expression.kind {
        replace_accessed_value(receiver, with);
        return;
    }
    for child in children_mut(expression) {
        replace_accessed_value(child, with);
    }
}

/// Whether an expression reads something that nothing between now and an
/// `await` could change out from under it.
fn is_pure(expression: &BoundExpression) -> bool {
    match &expression.kind {
        BoundExpressionKind::Local(_)
        | BoundExpressionKind::Parameter(_)
        | BoundExpressionKind::Literal(_)
        | BoundExpressionKind::This
        | BoundExpressionKind::Base
        | BoundExpressionKind::TypeExpression(_)
        | BoundExpressionKind::Default(_)
        | BoundExpressionKind::SizeOf(_)
        | BoundExpressionKind::TypeOf(_)
        | BoundExpressionKind::Lambda(_)
        | BoundExpressionKind::UnboundLambda(_)
        | BoundExpressionKind::DelegateCreation { receiver: None, .. } => true,
        BoundExpressionKind::Conversion { operand, .. } => is_pure(operand),
        _ => false,
    }
}

/// The subexpressions of an expression, in the order they are evaluated.
///
/// The target of an assignment is a place rather than a value, so its own
/// parts are listed rather than the target itself.
pub(crate) fn children_mut(expression: &mut BoundExpression) -> Vec<&mut BoundExpression> {
    use BoundExpressionKind as K;
    let mut out: Vec<&mut BoundExpression> = Vec::new();
    match &mut expression.kind {
        K::Field { receiver, .. }
        | K::Property { receiver, .. }
        | K::MethodGroup { receiver, .. }
        | K::DelegateCreation { receiver, .. } => out.extend(receiver.as_deref_mut()),
        K::EventAssignment {
            receiver, handler, ..
        } => {
            out.extend(receiver.as_deref_mut());
            out.push(handler);
        }
        K::RefArgument { operand, .. }
        | K::Unary { operand, .. }
        | K::Conversion { operand, .. }
        | K::TypeTest { operand, .. }
        | K::IsPattern { operand, .. }
        | K::TryCast { operand, .. }
        | K::Dereference { operand }
        | K::AddressOf { operand }
        | K::MakeRef(operand)
        | K::RefValue(operand)
        | K::RefType(operand)
        | K::Await { operand, .. } => out.push(operand),
        K::StackAlloc {
            count, elements, ..
        } => {
            out.push(count);
            out.extend(elements.iter_mut());
        }
        K::FunctionPointerCall { pointer, arguments } => {
            out.push(pointer);
            out.extend(arguments.iter_mut());
        }
        K::Call {
            receiver,
            arguments,
            ..
        } => {
            out.extend(receiver.as_deref_mut());
            out.extend(arguments.iter_mut());
        }
        K::ObjectCreation {
            arguments,
            initializers,
            ..
        } => {
            out.extend(arguments.iter_mut());
            out.extend(initializers.iter_mut());
        }
        K::With {
            receiver,
            initializers,
        } => {
            out.push(receiver);
            out.extend(initializers.iter_mut());
        }
        K::TupleCreation(values)
        | K::Sequence(values)
        | K::InterpolatedString(values)
        | K::ArgList(values) => out.extend(values.iter_mut()),
        // The statements are not expressions of this one: they are hoisted
        // as statements before anything looks inside.
        K::SpillSequence { value, .. } => out.push(value),
        K::Throw(value) => out.extend(value.as_deref_mut()),
        K::Dynamic(operation) => {
            out.extend(operation.receiver.as_mut());
            out.extend(operation.arguments.iter_mut());
        }
        K::ConditionalAccess { receiver, access } => {
            out.push(receiver);
            out.push(access);
        }
        K::ArrayCreation {
            lengths, elements, ..
        } => {
            out.extend(lengths.iter_mut());
            out.extend(elements.iter_mut());
        }
        K::ArrayAccess { array, indices } => {
            out.push(array);
            out.extend(indices.iter_mut());
        }
        K::ArrayLength { array } => out.push(array),
        K::IndexerAccess {
            receiver,
            arguments,
            ..
        } => {
            out.push(receiver);
            out.extend(arguments.iter_mut());
        }
        K::Binary { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        K::Conditional {
            condition,
            consequence,
            alternative,
        } => {
            out.push(condition);
            out.push(consequence);
            out.push(alternative);
        }
        K::Assignment { target, value } | K::CompoundAssignment { target, value, .. } => {
            out.extend(children_mut(target));
            out.push(value);
        }
        K::Increment { target, .. } => out.extend(children_mut(target)),
        K::StringInsert { value, .. } => out.push(value),
        K::Switch { governing, arms } => {
            out.push(governing);
            for arm in arms {
                out.extend(arm.when.as_mut());
                out.push(&mut arm.value);
            }
        }
        K::Error
        | K::Unsupported(_)
        | K::Literal(_)
        | K::ArgListHandle
        | K::Local(_)
        | K::Parameter(_)
        | K::This
        | K::Base
        | K::TypeExpression(_)
        | K::NamespaceExpression(_)
        | K::UnboundLambda(_)
        | K::UnboundCollection(_)
        | K::UnboundCreation(_)
        | K::UnboundConditional(_)
        | K::UnboundSwitch(_)
        | K::Lambda(_)
        | K::SizeOf(_)
        | K::MethodAddress { .. }
        | K::AccessedValue
        | K::CreatedObject
        | K::TypeOf(_)
        | K::Default(_) => {}
    }
    out
}

/// The same, read-only.
pub(crate) fn children(expression: &BoundExpression) -> Vec<&BoundExpression> {
    use BoundExpressionKind as K;
    let mut out: Vec<&BoundExpression> = Vec::new();
    match &expression.kind {
        K::Field { receiver, .. }
        | K::Property { receiver, .. }
        | K::MethodGroup { receiver, .. }
        | K::DelegateCreation { receiver, .. } => out.extend(receiver.as_deref()),
        K::EventAssignment {
            receiver, handler, ..
        } => {
            out.extend(receiver.as_deref());
            out.push(handler);
        }
        K::RefArgument { operand, .. }
        | K::Unary { operand, .. }
        | K::Conversion { operand, .. }
        | K::TypeTest { operand, .. }
        | K::IsPattern { operand, .. }
        | K::TryCast { operand, .. }
        | K::Dereference { operand }
        | K::AddressOf { operand }
        | K::MakeRef(operand)
        | K::RefValue(operand)
        | K::RefType(operand)
        | K::Await { operand, .. } => out.push(operand),
        K::StackAlloc {
            count, elements, ..
        } => {
            out.push(count);
            out.extend(elements.iter());
        }
        K::FunctionPointerCall { pointer, arguments } => {
            out.push(pointer);
            out.extend(arguments.iter());
        }
        K::Call {
            receiver,
            arguments,
            ..
        } => {
            out.extend(receiver.as_deref());
            out.extend(arguments.iter());
        }
        K::ObjectCreation {
            arguments,
            initializers,
            ..
        } => {
            out.extend(arguments.iter());
            out.extend(initializers.iter());
        }
        K::With {
            receiver,
            initializers,
        } => {
            out.push(receiver);
            out.extend(initializers.iter());
        }
        K::TupleCreation(values)
        | K::Sequence(values)
        | K::InterpolatedString(values)
        | K::ArgList(values) => out.extend(values.iter()),
        K::SpillSequence { value, .. } => out.push(value),
        K::Throw(value) => out.extend(value.as_deref()),
        K::Dynamic(operation) => {
            out.extend(operation.receiver.as_ref());
            out.extend(operation.arguments.iter());
        }
        K::ConditionalAccess { receiver, access } => {
            out.push(receiver);
            out.push(access);
        }
        K::ArrayCreation {
            lengths, elements, ..
        } => {
            out.extend(lengths.iter());
            out.extend(elements.iter());
        }
        K::ArrayAccess { array, indices } => {
            out.push(array);
            out.extend(indices.iter());
        }
        K::ArrayLength { array } => out.push(array),
        K::IndexerAccess {
            receiver,
            arguments,
            ..
        } => {
            out.push(receiver);
            out.extend(arguments.iter());
        }
        K::Binary { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        K::Conditional {
            condition,
            consequence,
            alternative,
        } => {
            out.push(condition);
            out.push(consequence);
            out.push(alternative);
        }
        K::Assignment { target, value } | K::CompoundAssignment { target, value, .. } => {
            out.extend(children(target));
            out.push(value);
        }
        K::Increment { target, .. } => out.extend(children(target)),
        K::StringInsert { value, .. } => out.push(value),
        K::Switch { governing, arms } => {
            out.push(governing);
            for arm in arms {
                out.extend(arm.when.as_ref());
                out.push(&arm.value);
            }
        }
        K::Error
        | K::Unsupported(_)
        | K::Literal(_)
        | K::ArgListHandle
        | K::Local(_)
        | K::Parameter(_)
        | K::This
        | K::Base
        | K::TypeExpression(_)
        | K::NamespaceExpression(_)
        | K::UnboundLambda(_)
        | K::UnboundCollection(_)
        | K::UnboundCreation(_)
        | K::UnboundConditional(_)
        | K::UnboundSwitch(_)
        | K::Lambda(_)
        | K::SizeOf(_)
        | K::MethodAddress { .. }
        | K::AccessedValue
        | K::CreatedObject
        | K::TypeOf(_)
        | K::Default(_) => {}
    }
    out
}

/// Whether an `await` sits anywhere in an expression. A lambda's body is a
/// method of its own and does not count.
/// Whether a `continue` in the statement would reach the loop `loops` loops
/// out from it: a plain one inside a nested loop is that loop's, and
/// `continue outer;` passes over the loops it names past.
fn continues_to(statement: &BoundStatement, loops: usize) -> bool {
    use BoundStatementKind as S;
    match &statement.kind {
        S::Continue(outward) => *outward == loops,
        S::Block(statements) => statements.iter().any(|inner| continues_to(inner, loops)),
        S::If {
            consequence,
            alternative,
            ..
        } => {
            continues_to(consequence, loops)
                || alternative
                    .as_deref()
                    .is_some_and(|inner| continues_to(inner, loops))
        }
        S::Switch { sections, .. } => sections.iter().any(|section| {
            section
                .statements
                .iter()
                .any(|inner| continues_to(inner, loops))
        }),
        S::Try {
            body,
            catches,
            finally,
        } => {
            continues_to(body, loops)
                || catches.iter().any(|catch| continues_to(&catch.body, loops))
                || finally
                    .as_deref()
                    .is_some_and(|inner| continues_to(inner, loops))
        }
        S::Using { body, .. } | S::Lock { body, .. } | S::Fixed { body, .. } => {
            continues_to(body, loops)
        }
        S::While { body, .. }
        | S::DoWhile { body, .. }
        | S::ForEach { body, .. }
        | S::For { body, .. } => continues_to(body, loops + 1),
        _ => false,
    }
}

fn contains_spill_sequence(expression: &BoundExpression) -> bool {
    matches!(expression.kind, BoundExpressionKind::SpillSequence { .. })
        || children(expression)
            .into_iter()
            .any(contains_spill_sequence)
}

pub(crate) fn contains_await(expression: &BoundExpression) -> bool {
    matches!(expression.kind, BoundExpressionKind::Await { .. })
        || children(expression).into_iter().any(contains_await)
}

/// Every expression a statement holds directly, in the order they run.
pub(crate) fn expressions_of(statement: &BoundStatement) -> Vec<&BoundExpression> {
    use BoundStatementKind as S;
    match &statement.kind {
        S::LocalDeclaration { initializer, .. } => initializer.iter().collect(),
        S::Expression(value)
        | S::Throw(Some(value))
        | S::Return(Some(value))
        | S::YieldReturn(value) => vec![value],
        S::If { condition, .. } | S::While { condition, .. } | S::DoWhile { condition, .. } => {
            vec![condition]
        }
        S::For {
            condition,
            incrementors,
            ..
        } => condition.iter().chain(incrementors.iter()).collect(),
        S::ForEach { collection, .. } => vec![collection],
        S::Switch { governing, .. } => vec![governing],
        S::Using { resources, .. } => resources.iter().map(|resource| &resource.value).collect(),
        S::Lock { value, .. } => vec![value],
        S::ConstructorInitializer { arguments, .. } => arguments.iter().collect(),
        _ => Vec::new(),
    }
}

/// The statements a statement holds, in the order they run.
fn substatements(statement: &BoundStatement) -> Vec<&BoundStatement> {
    use BoundStatementKind as S;
    match &statement.kind {
        S::Block(statements) => statements.iter().collect(),
        S::If {
            consequence,
            alternative,
            ..
        } => std::iter::once(consequence.as_ref())
            .chain(alternative.as_deref())
            .collect(),
        S::While { body, .. }
        | S::DoWhile { body, .. }
        | S::ForEach { body, .. }
        | S::Lock { body, .. } => vec![body],
        // The disposals of an `await using` run after the body, the last
        // resource's first.
        S::Using { resources, body } => std::iter::once(body.as_ref())
            .chain(
                resources
                    .iter()
                    .rev()
                    .filter_map(|resource| resource.awaited.as_deref()),
            )
            .collect(),
        S::Fixed { declarations, body } => declarations
            .iter()
            .chain(std::iter::once(body.as_ref()))
            .collect(),
        S::For {
            initializers, body, ..
        } => initializers
            .iter()
            .chain(std::iter::once(body.as_ref()))
            .collect(),
        S::Switch { sections, .. } => sections
            .iter()
            .flat_map(|section| section.statements.iter())
            .collect(),
        S::Try {
            body,
            catches,
            finally,
        } => std::iter::once(body.as_ref())
            .chain(catches.iter().map(|catch| &catch.body))
            .chain(finally.as_deref())
            .collect(),
        _ => Vec::new(),
    }
}

/// The ways a guarded `try` was found leaving, so the statements after its
/// `finally` only test for the ones that happen.
#[derive(Default)]
struct Exits {
    returns: bool,
    /// For each `break` leaving, how many loops and switches past the ones
    /// around the `try` it still passes over.
    breaks: std::collections::BTreeSet<usize>,
    /// The same for each `continue`, in loops.
    continues: std::collections::BTreeSet<usize>,
    /// The labels written inside the `try`, which a `goto` reaches without
    /// leaving it.
    inside: std::collections::HashSet<String>,
    /// The labels outside it a `goto` inside it leaves for, in the order met.
    gotos: Vec<String>,
}

/// The branch flag of a `goto` to the `position`th label outside a guarded
/// `try`: below zero, apart from the other ways out.
fn went(position: usize) -> i32 {
    -1 - i32::try_from(position).unwrap_or(i32::MAX / 4)
}

/// The locals some statements take the address of with `&`.
fn addressed_locals(statements: &[BoundStatement]) -> std::collections::HashSet<LocalId> {
    fn expression(value: &BoundExpression, out: &mut std::collections::HashSet<LocalId>) {
        if let BoundExpressionKind::AddressOf { operand } = &value.kind
            && let BoundExpressionKind::Local(local) = operand.kind
        {
            out.insert(local);
        }
        for child in children(value) {
            expression(child, out);
        }
    }
    fn statement(value: &BoundStatement, out: &mut std::collections::HashSet<LocalId>) {
        for inner in expressions_of(value) {
            expression(inner, out);
        }
        for inner in substatements(value) {
            statement(inner, out);
        }
    }
    let mut out = std::collections::HashSet::new();
    for value in statements {
        statement(value, &mut out);
    }
    out
}

/// Puts `made` where an initializer names the object it is written against
/// ([`CreatedObject`](BoundExpressionKind::CreatedObject)): not inside an
/// object an initializer in it makes, which has its own.
fn written_into(expression: &mut BoundExpression, made: LocalId) {
    match &mut expression.kind {
        BoundExpressionKind::CreatedObject => {
            expression.kind = BoundExpressionKind::Local(made);
        }
        BoundExpressionKind::ObjectCreation { arguments, .. } => {
            for argument in arguments {
                written_into(argument, made);
            }
        }
        BoundExpressionKind::With { receiver, .. } => written_into(receiver, made),
        _ => {
            for child in children_mut(expression) {
                written_into(child, made);
            }
        }
    }
}

/// Whether a statement has a `goto case` or `goto default` of the `switch`
/// it is in: one inside a `switch` nested in it is that `switch`'s own.
fn goes_to_case(statement: &BoundStatement) -> bool {
    match &statement.kind {
        BoundStatementKind::GotoCase(_) => true,
        BoundStatementKind::Switch { .. } => false,
        _ => substatements(statement).into_iter().any(goes_to_case),
    }
}

/// Every label written in some statements, however deep.
fn labels_within(statements: &[BoundStatement]) -> std::collections::HashSet<String> {
    fn walk(statement: &BoundStatement, out: &mut std::collections::HashSet<String>) {
        if let BoundStatementKind::Label(name) = &statement.kind {
            out.insert(name.clone());
        }
        for inner in substatements(statement) {
            walk(inner, out);
        }
    }
    let mut out = std::collections::HashSet::new();
    for statement in statements {
        walk(statement, &mut out);
    }
    out
}

/// What the branch flag of a guarded `try` says after it: nothing, a
/// `return`, a `break`, a `continue`.
const RETURNED: i32 = 1;
const BROKE: i32 = 2;
const CONTINUED: i32 = 3;

/// The branch flag of a `break` that passes over `outward` more targets once
/// out of the `try`: `BROKE` for a plain one, and one number apart for each.
fn broke(outward: usize) -> i32 {
    BROKE + 2 * i32::try_from(outward).unwrap_or(i32::MAX / 4)
}

/// The same for a `continue`.
fn continued(outward: usize) -> i32 {
    CONTINUED + 2 * i32::try_from(outward).unwrap_or(i32::MAX / 4)
}

fn statement_awaits(statement: &BoundStatement) -> bool {
    expressions_of(statement).into_iter().any(contains_await)
        || substatements(statement).into_iter().any(statement_awaits)
}

/// The awaiter types a body waits with, each once, in order of first use.
fn collect_awaiters(statements: &[BoundStatement], out: &mut Vec<Type>) {
    fn expression(value: &BoundExpression, out: &mut Vec<Type>) {
        // The awaiter of a `dynamic` operand is `dynamic`, kept in an
        // `object`.
        let awaiter = match &value.kind {
            BoundExpressionKind::Await {
                awaiting: Some(awaiting),
                ..
            } => Some(awaiting.awaiter.clone()),
            BoundExpressionKind::Await {
                operand,
                awaiting: None,
            } if matches!(operand.ty, Type::Dynamic) => Some(Type::Dynamic),
            _ => None,
        };
        if let Some(awaiter) = awaiter
            && !out.contains(&awaiter)
        {
            out.push(awaiter);
        }
        for child in children(value) {
            expression(child, out);
        }
    }
    for statement in statements {
        for value in expressions_of(statement) {
            expression(value, out);
        }
        collect_awaiters(
            &substatements(statement)
                .into_iter()
                .cloned()
                .collect::<Vec<_>>(),
            out,
        );
    }
}

/// Whether a statement is one an `await` was left in: its own expression is
/// the `await`, or is an assignment of one.
fn awaits_directly(statement: &BoundStatement) -> bool {
    expressions_of(statement).into_iter().any(|value| {
        matches!(value.kind, BoundExpressionKind::Await { .. })
            || matches!(&value.kind, BoundExpressionKind::Assignment { value, .. }
                if matches!(value.kind, BoundExpressionKind::Await { .. }))
    })
}

/// The field a machine keeps a local of its body in: `<name>5__n`, after
/// the local's place in the body's table, the way Roslyn names a hoisted
/// local; an `async` iterator's dispose mode goes by the name Roslyn gives
/// its field.
fn hoisted_name(id: LocalId, local: &LocalSymbol) -> String {
    if local.name == DISPOSE_MODE {
        return DISPOSE_MODE.to_string();
    }
    format!("<{}>5__{}", local.name, id.0 + 1)
}

/// Whether a statement is a `yield return`.
pub(crate) fn yields_directly(statement: &BoundStatement) -> bool {
    matches!(statement.kind, BoundStatementKind::YieldReturn(_))
}

/// Every suspension in the order `MoveNext` reaches them, each with the
/// protected regions around it, and how many regions there are.
///
/// The regions are numbered in the order `MoveNext` enters them, which is
/// the order the walk below meets them: a `try` before its body, and a
/// `using` with several resources as one region per resource, nested.
pub(crate) fn collect_sites(
    statements: &[BoundStatement],
    is_site: &dyn Fn(&BoundStatement) -> bool,
) -> (Vec<AwaitSite>, usize) {
    fn walk(
        statement: &BoundStatement,
        is_site: &dyn Fn(&BoundStatement) -> bool,
        path: &mut Vec<usize>,
        regions: &mut usize,
        sites: &mut Vec<AwaitSite>,
    ) {
        use BoundStatementKind as S;
        if is_site(statement) {
            sites.push(AwaitSite {
                regions: path.clone(),
                yields: yields_directly(statement),
            });
        }
        match &statement.kind {
            S::Try {
                body,
                catches,
                finally,
            } => {
                let region = *regions;
                *regions += 1;
                path.push(region);
                walk(body, is_site, path, regions, sites);
                path.pop();
                for catch in catches {
                    walk(&catch.body, is_site, path, regions, sites);
                }
                if let Some(finally) = finally {
                    walk(finally, is_site, path, regions, sites);
                }
            }
            S::Using { resources, body } => {
                let opened = resources.len().max(1);
                for _ in 0..opened {
                    path.push(*regions);
                    *regions += 1;
                }
                walk(body, is_site, path, regions, sites);
                for _ in 0..opened {
                    path.pop();
                }
            }
            S::Lock { body, .. } => {
                path.push(*regions);
                *regions += 1;
                walk(body, is_site, path, regions, sites);
                path.pop();
            }
            S::ForEach {
                body, enumeration, ..
            } => {
                let disposes = enumeration
                    .as_deref()
                    .is_some_and(|enumeration| enumeration.dispose.is_some());
                if disposes {
                    path.push(*regions);
                    *regions += 1;
                }
                walk(body, is_site, path, regions, sites);
                if disposes {
                    path.pop();
                }
            }
            _ => {
                for inner in substatements(statement) {
                    walk(inner, is_site, path, regions, sites);
                }
            }
        }
    }
    let mut sites = Vec::new();
    let mut regions = 0;
    let mut path = Vec::new();
    for statement in statements {
        walk(statement, is_site, &mut path, &mut regions, &mut sites);
    }
    (sites, regions)
}
