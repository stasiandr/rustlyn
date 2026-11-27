//! Threads: state two threads touch with nothing between them, and Unity
//! called from where Unity does not allow it.
//!
//! Every body of the file is given the thread it runs on. Code runs where
//! it is called from — in a Unity project that is the main thread — unless
//! it was handed to something that runs it elsewhere: `Task.Run`, a
//! `Thread`, the thread pool, `Parallel.For`, a timer, an `AsyncCallback`,
//! the continuation of an `await` that said `ConfigureAwait(false)`. A
//! method of the file takes the threads of everything in the file that calls
//! it, so a private helper called from `Task.Run` is on a background thread
//! too.
//!
//! * RLN1001: a field written on one thread and read or written on another,
//!   where neither a `lock`, `Interlocked`, `Volatile` nor `volatile` stands
//!   between them. Adding to a `List` is a write of the field that holds it.
//! * RLN1002: what only Unity's main thread may touch — a `Transform`,
//!   `GetComponent`, `Instantiate`, `Time`, `Input`, `Physics` — reached from
//!   a background thread, where Unity throws.
//! * RLN1003: a local the body of `Parallel.For` writes, which every
//!   iteration writes at once.
//!
//! What runs before a background thread starts, or after it was awaited, in
//! the method that started it, is not a race with it; neither is a
//! constructor, which runs before anything else has the object.

use std::collections::{BTreeSet, HashMap, HashSet};

use rustlyn_diagnostics::Severity;
use rustlyn_semantics::{
    BoundBody, BoundExpression, BoundExpressionKind as E, BoundStatement, BoundStatementKind as S,
    ConstantValue, LocalId, MethodKind, Modifiers, SymbolId, SymbolKind, Symbols, Type, TypeKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::View;
use super::super::walk::{expression_children, statement_children};
use super::{AnalyzerDiagnostic, Facts};

/// Where a piece of code runs, before the threads of what calls a method are
/// known.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Ctx {
    /// Wherever the method `SymbolId` is called from.
    Entry(SymbolId),
    Main,
    /// The background thread started at `sites[_]`.
    Worker(usize),
}

/// Where code is sent to another thread.
#[derive(Clone, Debug)]
struct Site {
    /// `Task.Run in Load`.
    label: String,
    /// The method whose own code started it, and where.
    unit: SymbolId,
    at: u32,
    /// The method waits for it right there: what comes after in that method
    /// runs after it.
    awaited: bool,
    /// Its body runs on several threads at once, and the call returns when
    /// they are all done: to everything else it is the thread that called.
    parallel: bool,
    /// Where the code that started it runs.
    parent: Ctx,
}

/// A call of a method, or a delegate made of one.
#[derive(Clone, Debug)]
struct Call {
    callee: SymbolId,
    ctx: Ctx,
    unit: SymbolId,
    at: u32,
    in_lambda: bool,
}

/// One read or write of a field.
#[derive(Clone, Debug)]
struct Access {
    field: SymbolId,
    span: TextSpan,
    write: bool,
    /// `lock`, `Interlocked`, `Volatile` or a `volatile` field.
    synced: bool,
    ctx: Ctx,
    /// The method whose code it is, and whether inside a lambda there.
    unit: SymbolId,
    in_lambda: bool,
    /// In a constructor or a field's initializer.
    constructing: bool,
    /// The member it is in, as a message names it.
    member: String,
    /// The constant a write puts there: two writes of the same one cannot
    /// tell which came last.
    constant: Option<String>,
    /// A read that only copies the field into a local, `var socket =
    /// _socket;`: the code goes on with what it read, checks that, and a
    /// write afterwards does not reach it.
    snapshot: bool,
}

/// A use of what only Unity's main thread may touch.
#[derive(Clone, Debug)]
struct UnityUse {
    span: TextSpan,
    /// `Transform.position`.
    name: String,
    ctx: Ctx,
}

/// What walking the file gathered.
#[derive(Default)]
struct Gathered {
    sites: Vec<Site>,
    accesses: Vec<Access>,
    /// Each call or delegate of a method, with where the call runs.
    calls: Vec<Call>,
    unity: Vec<UnityUse>,
    /// RLN1003: span, name of the local, the `Parallel` site.
    parallel_writes: Vec<(TextSpan, String, usize)>,
    /// Methods that end in `return this`: a builder's.
    fluent: HashSet<SymbolId>,
}

/// Types whose members may be used from any thread: what holds them is
/// still a field, but what they hold is guarded by them.
fn is_thread_safe_type(name: &str) -> bool {
    name.starts_with("System.Collections.Concurrent.")
        || name.starts_with("System.Threading.")
        || name.starts_with("System.Collections.Immutable.")
        || name.starts_with("Cysharp.Threading.Tasks.Channel")
}

/// Collections a write goes into through a method.
fn is_plain_collection(name: &str) -> bool {
    matches!(
        name,
        "System.Collections.Generic.List"
            | "System.Collections.Generic.Dictionary"
            | "System.Collections.Generic.HashSet"
            | "System.Collections.Generic.Queue"
            | "System.Collections.Generic.Stack"
            | "System.Collections.Generic.LinkedList"
            | "System.Collections.Generic.SortedDictionary"
            | "System.Collections.Generic.SortedList"
            | "System.Collections.Generic.SortedSet"
            | "System.Collections.ArrayList"
            | "System.Collections.Hashtable"
            | "System.Collections.Queue"
            | "System.Collections.Stack"
            | "System.Text.StringBuilder"
    )
}

/// The methods of those collections that change them.
fn is_mutator(name: &str) -> bool {
    matches!(
        name,
        "Add"
            | "AddRange"
            | "Insert"
            | "InsertRange"
            | "Remove"
            | "RemoveAt"
            | "RemoveAll"
            | "RemoveRange"
            | "RemoveWhere"
            | "Clear"
            | "Enqueue"
            | "Dequeue"
            | "TryDequeue"
            | "Push"
            | "Pop"
            | "TryPop"
            | "TryAdd"
            | "Sort"
            | "Reverse"
            | "AddFirst"
            | "AddLast"
            | "RemoveFirst"
            | "RemoveLast"
            | "UnionWith"
            | "ExceptWith"
            | "IntersectWith"
            | "Append"
            | "AppendLine"
            | "AppendFormat"
    )
}

/// Unity's types whose static members belong to the main thread, beside
/// everything that derives from `UnityEngine.Object`.
const UNITY_MAIN_ONLY: &[&str] = &[
    "UnityEngine.Time",
    "UnityEngine.Input",
    "UnityEngine.Physics",
    "UnityEngine.Physics2D",
    "UnityEngine.Screen",
    "UnityEngine.Application",
    "UnityEngine.Resources",
    "UnityEngine.PlayerPrefs",
    "UnityEngine.Random",
    "UnityEngine.Graphics",
    "UnityEngine.QualitySettings",
    "UnityEngine.Cursor",
    "UnityEngine.GUI",
    "UnityEngine.GUILayout",
    "UnityEngine.SceneManagement.SceneManager",
];

/// How a call sends code to another thread: the name a message gives it, and
/// whether the code runs on several threads at once.
fn spawner(qualified: &str) -> Option<(&'static str, bool)> {
    Some(match qualified {
        "System.Threading.Tasks.Task.Run" => ("Task.Run", false),
        "System.Threading.Tasks.TaskFactory.StartNew" => ("Task.Factory.StartNew", false),
        "System.Threading.Tasks.Task.ContinueWith" => ("ContinueWith", false),
        "System.Threading.ThreadPool.QueueUserWorkItem" => ("ThreadPool.QueueUserWorkItem", false),
        "System.Threading.ThreadPool.UnsafeQueueUserWorkItem" => {
            ("ThreadPool.UnsafeQueueUserWorkItem", false)
        }
        "System.Threading.Tasks.Parallel.For" => ("Parallel.For", true),
        "System.Threading.Tasks.Parallel.ForEach" => ("Parallel.ForEach", true),
        "System.Threading.Tasks.Parallel.ForEachAsync" => ("Parallel.ForEachAsync", true),
        "System.Threading.Tasks.Parallel.Invoke" => ("Parallel.Invoke", true),
        "Cysharp.Threading.Tasks.UniTask.RunOnThreadPool" => ("UniTask.RunOnThreadPool", false),
        "Cysharp.Threading.Tasks.UniTask.Run" => ("UniTask.Run", false),
        _ => return None,
    })
}

/// The constructors that take code to run elsewhere.
fn spawning_type(qualified: &str) -> Option<&'static str> {
    Some(match qualified {
        "System.Threading.Thread" => "new Thread",
        "System.Threading.Timer" => "System.Threading.Timer",
        "System.Threading.Tasks.Task" => "new Task",
        _ => return None,
    })
}

/// Events raised on a thread of the pool.
fn is_worker_event(qualified: &str) -> bool {
    matches!(
        qualified,
        "System.Timers.Timer.Elapsed" | "System.Net.Sockets.SocketAsyncEventArgs.Completed"
    ) || qualified.starts_with("System.IO.FileSystemWatcher.")
}

pub(in super::super) fn threads(
    view: &mut View<'_>,
    facts: &Facts,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    let thread_static = thread_static_fields(view);
    let unity_object = view
        .compilation()
        .type_by_metadata_name("UnityEngine.Object");
    let symbols = view.compilation().symbols();
    let mut gathered = Gathered::default();
    let mut units: Vec<SymbolId> = Vec::new();
    let mut unity_cache: HashMap<SymbolId, bool> = HashMap::new();

    for body in &facts.bodies {
        if body.broken {
            continue;
        }
        let Some(owner) = view.model.declared_symbol(&body.owner) else {
            continue;
        };
        let owner_symbol = symbols.get(owner);
        let constructing = matches!(owner_symbol.kind, SymbolKind::Field)
            || owner_symbol.as_method().is_some_and(|method| {
                matches!(
                    method.method_kind,
                    MethodKind::Constructor | MethodKind::StaticConstructor
                )
            });
        units.push(owner);
        let mut walk = Walk {
            view,
            symbols,
            body: &body.bound,
            names: names_of(&body.bound),
            unit: owner,
            member: member_name(symbols, owner, &body.owner),
            constructing,
            in_lambda: false,
            locked: 0,
            ctx: Ctx::Entry(owner),
            parallel: None,
            lambda: None,
            here: 0,
            constant: None,
            snapshot: false,
            awaited: HashSet::new(),
            thread_static: &thread_static,
            unity_object,
            unity_cache: &mut unity_cache,
            out: &mut gathered,
        };
        for statement in &body.bound.statements {
            walk.statement(statement);
        }
        for function in &body.bound.local_functions {
            units.push(function.symbol);
            walk.unit = function.symbol;
            walk.ctx = Ctx::Entry(function.symbol);
            walk.constructing = false;
            walk.locked = 0;
            walk.statement(&function.body);
        }
    }

    let threads = resolve(&units, &gathered.calls);
    let concrete = |ctx: Ctx| -> Vec<Ctx> {
        match ctx {
            Ctx::Entry(unit) => threads
                .get(&unit)
                .map(|set| set.iter().copied().collect())
                .unwrap_or_else(|| vec![Ctx::Main]),
            other => vec![other],
        }
    };
    let setup: HashSet<SymbolId> = units
        .iter()
        .copied()
        .filter(|&unit| is_setup(view, symbols, unit) || gathered.fluent.contains(&unit))
        .collect();
    let before = before_sites(&gathered.sites, &gathered.calls);
    let order = Order {
        sites: &gathered.sites,
        before: &before,
        setup: &setup,
        concrete: &concrete,
    };

    // RLN1001: once for each field in each member, at its first access there
    // that meets another thread.
    let mut by_field: HashMap<SymbolId, Vec<(usize, Ctx)>> = HashMap::new();
    for (index, access) in gathered.accesses.iter().enumerate() {
        if access.constructing {
            continue;
        }
        for ctx in concrete(access.ctx) {
            by_field.entry(access.field).or_default().push((index, ctx));
        }
    }
    let mut reported: HashSet<(SymbolId, SymbolId, bool)> = HashSet::new();
    let mut fields: Vec<_> = by_field.into_iter().collect();
    fields.sort_by_key(|(field, _)| *field);
    for (field, uses) in fields {
        // Two reads race with nothing: a field nobody writes has no partner
        // for any of them.
        if !uses
            .iter()
            .any(|&(index, _)| gathered.accesses[index].write)
        {
            continue;
        }
        // Nor do two accesses that cannot be at the same time, which only
        // the threads they are on say: a field used on one thread alone has
        // no partner, however many times it is used.
        let mut threads: Vec<Ctx> = uses.iter().map(|&(_, ctx)| ctx).collect();
        threads.sort_unstable();
        threads.dedup();
        if !threads
            .iter()
            .any(|&x| threads.iter().any(|&y| order.concurrent(x, y)))
        {
            continue;
        }
        for &(a, ca) in &uses {
            let first = &gathered.accesses[a];
            let key = (field, first.unit, first.in_lambda);
            if first.synced || first.snapshot || reported.contains(&key) {
                continue;
            }
            let partner = uses.iter().find(|&&(b, cb)| {
                let second = &gathered.accesses[b];
                !second.snapshot
                    && (first.write || second.write)
                    && !(first.write
                        && second.write
                        && first.constant.is_some()
                        && first.constant == second.constant)
                    && order.concurrent(ca, cb)
                    && !order.ordered(first, ca, second, cb)
            });
            let Some(&(b, cb)) = partner else {
                continue;
            };
            let second = &gathered.accesses[b];
            reported.insert(key);
            let name = &symbols.get(field).name;
            let verb = |write: bool| if write { "written" } else { "read" };
            found.push(AnalyzerDiagnostic::new(
                "RLN1001",
                Severity::Warning,
                first.span,
                format!(
                    "'{name}' is {} {} and {} {} with no lock between them",
                    verb(first.write),
                    describe(&gathered.sites, ca, &first.member),
                    verb(second.write),
                    describe(&gathered.sites, cb, &second.member),
                ),
            ));
        }
    }

    // RLN1002.
    for used in &gathered.unity {
        let Some(Ctx::Worker(site)) = concrete(used.ctx)
            .into_iter()
            .find(|ctx| matches!(ctx, Ctx::Worker(_)))
        else {
            continue;
        };
        found.push(AnalyzerDiagnostic::new(
            "RLN1002",
            Severity::Warning,
            used.span,
            format!(
                "'{}' can only be used on Unity's main thread, and this runs on a background thread ({})",
                used.name, gathered.sites[site].label
            ),
        ));
    }

    // RLN1003.
    for (span, name, site) in &gathered.parallel_writes {
        found.push(AnalyzerDiagnostic::new(
            "RLN1003",
            Severity::Warning,
            *span,
            format!(
                "'{name}' is written by every iteration of {} at once, with no lock",
                gathered.sites[*site].label
            ),
        ));
    }
}

/// Which threads each method of the file runs on: those of its callers in
/// the file, and the main thread for one nothing in the file calls, which is
/// called from somewhere the file does not show — Unity, for a message.
fn resolve(units: &[SymbolId], calls: &[Call]) -> HashMap<SymbolId, BTreeSet<Ctx>> {
    let called: HashSet<SymbolId> = calls.iter().map(|call| call.callee).collect();
    let mut threads: HashMap<SymbolId, BTreeSet<Ctx>> = HashMap::new();
    for &unit in units {
        let mut set = BTreeSet::new();
        if !called.contains(&unit) {
            set.insert(Ctx::Main);
        }
        threads.insert(unit, set);
    }
    loop {
        let mut changed = false;
        for call in calls {
            if !threads.contains_key(&call.callee) {
                continue;
            }
            let from: Vec<Ctx> = match call.ctx {
                Ctx::Entry(caller) => threads
                    .get(&caller)
                    .map(|set| set.iter().copied().collect())
                    .unwrap_or_default(),
                other => vec![other],
            };
            let set = threads.get_mut(&call.callee).expect("present");
            for ctx in from {
                changed |= set.insert(ctx);
            }
        }
        if !changed {
            break;
        }
    }
    threads
}

/// Members that set an object up before anything else uses it: Unity's and
/// Morpeh's first messages, `Init…`, and a builder's methods, which give the
/// object back to be configured further before it is sent off.
fn is_setup(view: &View<'_>, symbols: &Symbols, unit: SymbolId) -> bool {
    let symbol = symbols.get(unit);
    let name = symbol.name.as_str();
    if matches!(
        name,
        "Awake" | "OnAwake" | "Start" | "OnEnable" | "OnCreate" | "Setup" | "SetUp"
    ) || name.starts_with("Init")
    {
        return true;
    }
    let Some(container) = symbol.container else {
        return false;
    };
    symbol.as_method().is_some()
        && matches!(view.model.type_of_symbol(unit), Type::Named { symbol, .. } if symbol == container)
}

/// For each site, the methods the method that starts it calls before it
/// does, and what those call in turn: they ran before the thread did.
fn before_sites(sites: &[Site], calls: &[Call]) -> Vec<HashSet<SymbolId>> {
    let mut callees: HashMap<SymbolId, Vec<SymbolId>> = HashMap::new();
    for call in calls {
        callees.entry(call.unit).or_default().push(call.callee);
    }
    // A call made before `at` in `unit`, outside its lambdas.
    let earlier = |call: &Call, unit: SymbolId, at: u32| {
        call.unit == unit && !call.in_lambda && call.at < at && !matches!(call.ctx, Ctx::Worker(_))
    };
    sites
        .iter()
        .map(|site| {
            // Where the thread starts: at the site, and where something in
            // the file calls the method that starts it.
            let mut starts: Vec<(SymbolId, u32)> = vec![(site.unit, site.at)];
            starts.extend(
                calls
                    .iter()
                    .filter(|call| call.callee == site.unit && !call.in_lambda)
                    .map(|call| (call.unit, call.at)),
            );
            let mut found: HashSet<SymbolId> = HashSet::new();
            let mut pending: Vec<SymbolId> = calls
                .iter()
                .filter(|call| starts.iter().any(|&(unit, at)| earlier(call, unit, at)))
                .map(|call| call.callee)
                .collect();
            while let Some(next) = pending.pop() {
                if next != site.unit && found.insert(next) {
                    pending.extend(callees.get(&next).into_iter().flatten().copied());
                }
            }
            // Only what nothing calls at any other time: `CloseSocket` that
            // `Start` calls first, and `Stop` calls later, runs while the
            // thread does.
            loop {
                let late: Vec<SymbolId> = found
                    .iter()
                    .copied()
                    .filter(|&method| {
                        calls.iter().any(|call| {
                            call.callee == method
                                && !found.contains(&call.unit)
                                && !starts.iter().any(|&(unit, at)| earlier(call, unit, at))
                        })
                    })
                    .collect();
                if late.is_empty() {
                    break;
                }
                for method in late {
                    found.remove(&method);
                }
            }
            found
        })
        .collect()
}

/// What an expression is under the conversions the binder put around it.
fn unconverted(expression: &BoundExpression) -> &BoundExpression {
    match &expression.kind {
        E::Conversion { operand, .. } => unconverted(operand),
        _ => expression,
    }
}

/// What decides whether two accesses can happen at once.
struct Order<'a> {
    sites: &'a [Site],
    before: &'a [HashSet<SymbolId>],
    setup: &'a HashSet<SymbolId>,
    concrete: &'a dyn Fn(Ctx) -> Vec<Ctx>,
}

impl Order<'_> {
    /// The threads `ctx` stands for to everything outside it: the body of a
    /// `Parallel` call is, to them, the thread that waits for it.
    fn effective(&self, ctx: Ctx, out: &mut Vec<Ctx>, depth: usize) {
        match ctx {
            Ctx::Worker(index) if self.sites[index].parallel && depth < 16 => {
                for parent in (self.concrete)(self.sites[index].parent) {
                    self.effective(parent, out, depth + 1);
                }
            }
            other => out.push(other),
        }
    }

    /// Whether code on `a` and code on `b` can run at the same time.
    fn concurrent(&self, a: Ctx, b: Ctx) -> bool {
        if let (Ctx::Worker(x), Ctx::Worker(y)) = (a, b)
            && x == y
        {
            return self.sites[x].parallel;
        }
        let (mut left, mut right) = (Vec::new(), Vec::new());
        self.effective(a, &mut left, 0);
        self.effective(b, &mut right, 0);
        left.iter().any(|&x| {
            right.iter().any(|&y| match (x, y) {
                (Ctx::Main, Ctx::Main) => false,
                (Ctx::Worker(x), Ctx::Worker(y)) => x != y,
                _ => true,
            })
        })
    }

    /// Whether one of the two runs before the other's thread starts: in
    /// the method that starts it, before it does or after waiting for it; in
    /// what that method calls first; or while the object is set up.
    fn ordered(&self, a: &Access, ca: Ctx, b: &Access, cb: Ctx) -> bool {
        let first = |worker: Ctx, other: &Access, other_ctx: Ctx| {
            let Ctx::Worker(index) = worker else {
                return false;
            };
            if matches!(other_ctx, Ctx::Worker(_)) {
                return false;
            }
            let site = &self.sites[index];
            if other.in_lambda {
                return false;
            }
            (other.unit == site.unit && (other.span.start() < site.at || site.awaited))
                || self.before[index].contains(&other.unit)
                || (self.setup.contains(&other.unit) && !self.setup.contains(&site.unit))
        };
        first(ca, b, cb) || first(cb, a, ca)
    }
}

/// The dotted name of a symbol, without the arity metadata gives a generic
/// type: `System.Collections.Generic.List`.
fn qualified(symbols: &Symbols, symbol: SymbolId) -> String {
    let name = symbols.qualified_name(symbol);
    if !name.contains('`') {
        return name;
    }
    name.split('.')
        .map(|part| part.split('`').next().unwrap_or(part))
        .collect::<Vec<_>>()
        .join(".")
}

/// Where the name of a member access can start: after its receiver, where
/// the receiver was written; anywhere in it for an implicit `this`.
fn after_receiver(receiver: Option<&BoundExpression>, span: TextSpan) -> u32 {
    match receiver {
        Some(receiver)
            if receiver.span.end() < span.end() && receiver.span.start() >= span.start() =>
        {
            receiver.span.end()
        }
        _ => span.start(),
    }
}

fn describe(sites: &[Site], ctx: Ctx, member: &str) -> String {
    match ctx {
        Ctx::Worker(index) => format!("on a background thread ({})", sites[index].label),
        _ => format!("on the main thread (in {member})"),
    }
}

/// The name a message gives the member a body belongs to.
fn member_name(symbols: &Symbols, owner: SymbolId, node: &SyntaxNode) -> String {
    let symbol = symbols.get(owner);
    if symbol
        .as_method()
        .is_some_and(|method| matches!(method.method_kind, MethodKind::Constructor))
    {
        return "the constructor".to_string();
    }
    if matches!(
        node.kind(),
        SyntaxKind::GetAccessorDeclaration | SyntaxKind::SetAccessorDeclaration
    ) && let Some(container) = symbol.container
    {
        return symbols.get(container).name.clone();
    }
    symbol.name.clone()
}

/// Where a body names each symbol.
fn names_of(body: &BoundBody) -> HashMap<SymbolId, Vec<TextSpan>> {
    let mut names: HashMap<SymbolId, Vec<TextSpan>> = HashMap::new();
    for (at, symbol) in &body.symbols {
        names.entry(*symbol).or_default().push(*at);
    }
    // In order of place, so that the first one from some place on is found
    // without looking at all of them.
    for spans in names.values_mut() {
        spans.sort_by_key(|at| at.start());
    }
    names
}

/// Fields marked `[ThreadStatic]`: each thread has its own.
fn thread_static_fields(view: &View<'_>) -> HashSet<SymbolId> {
    let mut found = HashSet::new();
    for node in view.root.descendants() {
        if node.kind() != SyntaxKind::FieldDeclaration {
            continue;
        }
        let marked = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::AttributeList)
            .any(|list| {
                let text = list.text().to_string();
                text.contains("ThreadStatic")
            });
        if !marked {
            continue;
        }
        for declarator in node
            .descendants()
            .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        {
            if let Some(symbol) = view.model.declared_symbol(&declarator) {
                found.insert(symbol);
            }
        }
    }
    found
}

struct Walk<'w, 'v> {
    view: &'w View<'v>,
    symbols: &'w Symbols,
    body: &'w BoundBody,
    /// Where the body names each symbol, by the binder.
    names: HashMap<SymbolId, Vec<TextSpan>>,
    unit: SymbolId,
    member: String,
    constructing: bool,
    in_lambda: bool,
    locked: u32,
    ctx: Ctx,
    /// Inside the body of a `Parallel` call: the lambda's span and the site.
    parallel: Option<(TextSpan, usize)>,
    /// The span of the lambda being walked, the innermost.
    lambda: Option<TextSpan>,
    /// Where the expression being walked starts.
    here: u32,
    /// The constant the assignment being walked writes.
    constant: Option<String>,
    /// Walking a local's initializer that is nothing but a field.
    snapshot: bool,
    /// Calls an `await` waits for right where they are made.
    awaited: HashSet<TextSpan>,
    thread_static: &'w HashSet<SymbolId>,
    unity_object: Option<SymbolId>,
    unity_cache: &'w mut HashMap<SymbolId, bool>,
    out: &'w mut Gathered,
}

impl Walk<'_, '_> {
    fn statement(&mut self, statement: &BoundStatement) {
        if let S::Return(Some(value)) = &statement.kind
            && !self.in_lambda
            && matches!(unconverted(value).kind, E::This)
        {
            self.out.fluent.insert(self.unit);
        }
        if let S::Lock { value, body, .. } = &statement.kind {
            self.expression(value);
            self.locked += 1;
            self.statement(body);
            self.locked -= 1;
            return;
        }
        if let S::LocalDeclaration {
            initializer: Some(value),
            ..
        } = &statement.kind
            && self.watched(unconverted(value)).is_some()
        {
            self.snapshot = true;
            self.expression(value);
            self.snapshot = false;
            return;
        }
        let (statements, expressions) = statement_children(statement);
        if matches!(statement.kind, S::DoWhile { .. }) {
            for child in statements {
                self.statement(child);
            }
            for child in expressions {
                self.expression(child);
            }
            return;
        }
        for child in expressions {
            self.expression(child);
        }
        for child in statements {
            self.statement(child);
        }
    }

    fn qualified(&self, symbol: SymbolId) -> String {
        qualified(self.symbols, symbol)
    }

    /// The qualified name of a named type, without its arguments.
    fn type_name(&self, ty: &Type) -> Option<String> {
        match ty {
            Type::Named { symbol, .. } => Some(self.qualified(*symbol)),
            _ => None,
        }
    }

    /// A new site for code sent elsewhere from here.
    fn site(&mut self, label: &str, at: u32, awaited: bool, parallel: bool) -> usize {
        self.out.sites.push(Site {
            label: format!("{label} in {}", self.member),
            unit: self.unit,
            at,
            awaited,
            parallel,
            parent: self.ctx,
        });
        self.out.sites.len() - 1
    }

    fn push_call(&mut self, callee: SymbolId, ctx: Ctx) {
        self.out.calls.push(Call {
            callee,
            ctx,
            unit: self.unit,
            at: self.here,
            in_lambda: self.in_lambda,
        });
    }

    /// Whether `receiver` is a local made inside the lambda being walked:
    /// an object only this run of it has.
    fn own_object(&self, receiver: Option<&BoundExpression>) -> bool {
        let (Some(lambda), Some(receiver)) = (self.lambda, receiver) else {
            return false;
        };
        let E::Local(local) = receiver.kind else {
            return false;
        };
        self.body
            .locals
            .get(local.0 as usize)
            .is_some_and(|symbol| lambda.contains_span(symbol.span))
    }

    /// Whether a field is worth watching: one of the program's, not a
    /// constant, and not of a type that guards itself.
    fn watched_field(&self, field: SymbolId) -> bool {
        let symbol = self.symbols.get(field);
        if symbol.locations.is_empty()
            || symbol.modifiers.contains(Modifiers::CONST)
            || self.thread_static.contains(&field)
        {
            return false;
        }
        let ty = self.view.model.type_of_symbol(field);
        !self
            .type_name(&ty)
            .is_some_and(|name| is_thread_safe_type(&name))
    }

    /// An auto-property of the program: a field under another name.
    fn auto_property(&self, property: SymbolId) -> bool {
        let symbol = self.symbols.get(property);
        let Some(detail) = symbol.as_property() else {
            return false;
        };
        !symbol.locations.is_empty()
            && !detail.is_indexer
            && detail.getter.is_none()
            && detail.setter.is_none()
            && !symbol.modifiers.contains(Modifiers::ABSTRACT)
            && symbol.container.is_some_and(|container| {
                self.symbols.get(container).type_kind() != Some(TypeKind::Interface)
            })
            && !self
                .type_name(&self.view.model.type_of_symbol(property))
                .is_some_and(|name| is_thread_safe_type(&name))
    }

    /// Whether `receiver` is this object or none: what the field is of is
    /// shared by every method of the type.
    fn shared_receiver(receiver: Option<&BoundExpression>) -> bool {
        match receiver {
            None => true,
            Some(receiver) => matches!(receiver.kind, E::This | E::Base),
        }
    }

    /// The name token of `member` inside `span`: the first one from `after`
    /// on, where the binder kept it; the end of `span` otherwise.
    fn name_span(&self, span: TextSpan, member: SymbolId, after: u32) -> TextSpan {
        let found = self
            .names
            .get(&member)
            .and_then(|spans| {
                let from = spans.partition_point(|at| at.start() < after);
                spans[from..]
                    .iter()
                    .take_while(|at| at.start() < span.end())
                    .find(|at| span.contains_span(**at))
            })
            .copied();
        if let Some(found) = found {
            return found;
        }
        let name = &self.symbols.get(member).name;
        let around = self
            .view
            .root
            .find_node(span)
            .unwrap_or_else(|| self.view.root.clone());
        if let Some(token) = around.descendant_tokens().find(|token| {
            let at = token.span();
            at.start() >= after && span.contains_span(at) && token.value_text() == name.as_str()
        }) {
            return token.span();
        }
        let length = self.symbols.get(member).name.len() as u32;
        if span.length() >= length {
            TextSpan::new(span.end() - length, length)
        } else {
            span
        }
    }

    /// The name of the field or property `expression` reads.
    fn member_span(&self, expression: &BoundExpression, member: SymbolId) -> TextSpan {
        let after = match &expression.kind {
            E::Field { receiver, .. } | E::Property { receiver, .. } => {
                after_receiver(receiver.as_deref(), expression.span)
            }
            _ => expression.span.start(),
        };
        self.name_span(expression.span, member, after)
    }

    fn record(&mut self, member: SymbolId, span: TextSpan, write: bool, synced: bool) {
        let volatile = self
            .symbols
            .get(member)
            .modifiers
            .contains(Modifiers::VOLATILE);
        self.out.accesses.push(Access {
            field: member,
            span,
            write,
            synced: synced || self.locked > 0 || volatile,
            ctx: self.ctx,
            unit: self.unit,
            in_lambda: self.in_lambda,
            constructing: self.constructing && !self.in_lambda,
            member: self.member.clone(),
            constant: if write { self.constant.clone() } else { None },
            snapshot: !write && self.snapshot,
        });
    }

    /// The field or auto-property `expression` names on this object, if it
    /// is one worth watching.
    fn watched(&self, expression: &BoundExpression) -> Option<SymbolId> {
        match &expression.kind {
            E::Field { receiver, field }
                if Self::shared_receiver(receiver.as_deref()) && self.watched_field(*field) =>
            {
                Some(*field)
            }
            E::Property { receiver, property }
                if Self::shared_receiver(receiver.as_deref()) && self.auto_property(*property) =>
            {
                Some(*property)
            }
            _ => None,
        }
    }

    /// `target` is written.
    fn write(&mut self, target: &BoundExpression) {
        if let Some(member) = self.watched(target) {
            let span = self.member_span(target, member);
            self.record(member, span, true, false);
            return;
        }
        match &target.kind {
            // `this.pos.x = 1` writes `pos` when it is a struct.
            E::Field {
                receiver: Some(receiver),
                ..
            } if self.is_struct(&receiver.ty) => self.write(receiver),
            // `cells[i] = x` and `map[key] = x` write what the field holds.
            E::ArrayAccess { array, indices } => {
                self.write(array);
                for index in indices {
                    self.expression(index);
                }
            }
            E::IndexerAccess {
                receiver,
                arguments,
                ..
            } => {
                if self.watched(receiver).is_some() {
                    self.write(receiver);
                } else {
                    self.expression(receiver);
                }
                for argument in arguments {
                    self.expression(argument);
                }
            }
            E::Local(local) => {
                self.local_written(*local, target.span);
            }
            E::Conversion { operand, .. } => self.write(operand),
            _ => self.expression(target),
        }
    }

    fn is_struct(&self, ty: &Type) -> bool {
        matches!(ty, Type::Named { symbol, .. }
            if matches!(self.symbols.get(*symbol).type_kind(), Some(TypeKind::Struct | TypeKind::RecordStruct)))
    }

    /// RLN1003: a local of the method around a `Parallel` body, written in
    /// it with no lock.
    fn local_written(&mut self, local: LocalId, span: TextSpan) {
        let Some((lambda, site)) = self.parallel else {
            return;
        };
        if self.locked > 0 {
            return;
        }
        let Some(symbol) = self.body.locals.get(local.0 as usize) else {
            return;
        };
        if lambda.contains_span(symbol.span) {
            return;
        }
        self.out
            .parallel_writes
            .push((span, symbol.name.clone(), site));
    }

    /// Whether `member` (a method, property or field) is Unity's and only
    /// for the main thread.
    fn unity_main_only(&mut self, member: SymbolId) -> bool {
        let symbol = self.symbols.get(member);
        if symbol.name.starts_with("op_")
            || matches!(
                symbol.name.as_str(),
                "Equals" | "GetHashCode" | "ReferenceEquals" | "GetInstanceID" | "ToString"
            )
        {
            return false;
        }
        let Some(container) = symbol.container else {
            return false;
        };
        if let Some(&known) = self.unity_cache.get(&container) {
            return known;
        }
        let name = self.qualified(container);
        let answer = name.starts_with("UnityEngine.")
            && (UNITY_MAIN_ONLY.contains(&name.as_str())
                || self.derives_from_unity_object(container));
        self.unity_cache.insert(container, answer);
        answer
    }

    fn derives_from_unity_object(&self, ty: SymbolId) -> bool {
        let Some(object) = self.unity_object else {
            return false;
        };
        let mut current = Some(ty);
        for _ in 0..64 {
            let Some(at) = current else {
                return false;
            };
            if at == object {
                return true;
            }
            current = self
                .view
                .model
                .binder()
                .base_class_of(at)
                .and_then(|base| base.symbol());
        }
        false
    }

    fn unity_use(&mut self, member: SymbolId, span: TextSpan, after: u32) {
        if !self.unity_main_only(member) {
            return;
        }
        let symbol = self.symbols.get(member);
        let owner = symbol
            .container
            .map(|container| self.symbols.get(container).name.clone())
            .unwrap_or_default();
        let name = format!("{owner}.{}", symbol.name);
        let span = self.name_span(span, member, after);
        self.out.unity.push(UnityUse {
            span,
            name,
            ctx: self.ctx,
        });
    }

    /// Code `argument` hands over to run on the thread `site`: a lambda is
    /// walked there, a method is called from there.
    fn send(&mut self, argument: &BoundExpression, site: usize) -> bool {
        match &argument.kind {
            E::Conversion { operand, .. } => self.send(operand, site),
            E::Lambda(index) => {
                let Some(lambda) = self.body.lambdas.get(*index) else {
                    return false;
                };
                let saved = (
                    self.ctx,
                    self.in_lambda,
                    self.locked,
                    self.parallel,
                    self.lambda,
                );
                self.lambda = Some(lambda.span);
                self.ctx = Ctx::Worker(site);
                self.in_lambda = true;
                self.locked = 0;
                if self.out.sites[site].parallel {
                    self.parallel = Some((lambda.span, site));
                }
                self.statement(&lambda.body);
                (
                    self.ctx,
                    self.in_lambda,
                    self.locked,
                    self.parallel,
                    self.lambda,
                ) = saved;
                true
            }
            E::DelegateCreation {
                method, receiver, ..
            } => {
                self.push_call(*method, Ctx::Worker(site));
                if let Some(receiver) = receiver {
                    self.expression(receiver);
                }
                true
            }
            E::MethodGroup { candidates, .. } => {
                for candidate in candidates {
                    self.push_call(*candidate, Ctx::Worker(site));
                }
                true
            }
            _ => false,
        }
    }

    fn arguments_to(&mut self, arguments: &[BoundExpression], site: Option<usize>) {
        for argument in arguments {
            if let Some(site) = site
                && self.send(argument, site)
            {
                continue;
            }
            // An `AsyncCallback` runs on a thread of the pool.
            if site.is_none()
                && self
                    .type_name(&argument.ty)
                    .is_some_and(|name| name == "System.AsyncCallback")
            {
                let callback = self.site("AsyncCallback", argument.span.start(), false, false);
                if self.send(argument, callback) {
                    continue;
                }
            }
            match &argument.kind {
                E::RefArgument { operand, .. } => self.write(operand),
                _ => self.expression(argument),
            }
        }
    }

    fn expression(&mut self, expression: &BoundExpression) {
        self.here = expression.span.start();
        match &expression.kind {
            E::Field { receiver, field } => {
                if self.watched(expression).is_some() {
                    let span = self.member_span(expression, *field);
                    self.record(*field, span, false, false);
                }
                let after = after_receiver(receiver.as_deref(), expression.span);
                self.unity_use(*field, expression.span, after);
                if let Some(receiver) = receiver {
                    self.expression(receiver);
                }
            }
            E::Property { receiver, property } => {
                if self.watched(expression).is_some() {
                    let span = self.member_span(expression, *property);
                    self.record(*property, span, false, false);
                }
                let after = after_receiver(receiver.as_deref(), expression.span);
                self.unity_use(*property, expression.span, after);
                if let Some(receiver) = receiver {
                    self.expression(receiver);
                }
            }
            E::Assignment { target, value } => {
                self.constant = match &unconverted(value).kind {
                    E::Literal(constant) => Some(format!("{constant:?}")),
                    _ => None,
                };
                self.write(target);
                self.constant = None;
                self.expression(value);
            }
            E::CompoundAssignment { target, value, .. } => {
                self.write(target);
                self.expression(value);
            }
            E::Increment { target, .. } => self.write(target),
            E::Call {
                receiver,
                method,
                arguments,
                ..
            } => self.call(expression, receiver.as_deref(), *method, arguments),
            E::ObjectCreation {
                constructor,
                arguments,
                initializers,
            } => {
                let site = constructor.and_then(|constructor| {
                    let container = self.symbols.get(constructor).container?;
                    let label = spawning_type(&self.qualified(container))?;
                    Some(self.site(label, expression.span.start(), false, false))
                });
                if let Some(constructor) = constructor {
                    self.push_call(*constructor, self.ctx);
                }
                self.arguments_to(arguments, site);
                for initializer in initializers {
                    self.expression(initializer);
                }
            }
            E::EventAssignment {
                receiver,
                event,
                add,
                handler,
            } => {
                if let Some(receiver) = receiver {
                    self.expression(receiver);
                }
                let qualified = self.qualified(*event);
                if *add && is_worker_event(&qualified) {
                    let label = format!(
                        "{}.{}",
                        self.symbols
                            .get(self.symbols.get(*event).container.unwrap_or(*event))
                            .name,
                        self.symbols.get(*event).name
                    );
                    let site = self.site(&label, expression.span.start(), false, false);
                    if self.send(handler, site) {
                        return;
                    }
                }
                self.expression(handler);
            }
            E::DelegateCreation {
                method, receiver, ..
            } => {
                if !self.own_object(receiver.as_deref()) {
                    self.push_call(*method, self.ctx);
                }
                if let Some(receiver) = receiver {
                    self.expression(receiver);
                }
            }
            E::MethodGroup {
                candidates,
                receiver,
            } => {
                for candidate in candidates {
                    self.push_call(*candidate, self.ctx);
                }
                if let Some(receiver) = receiver {
                    self.expression(receiver);
                }
            }
            E::Lambda(index) => {
                let Some(lambda) = self.body.lambdas.get(*index) else {
                    return;
                };
                // A lambda kept for later runs where it is called, which is
                // most often where it was made; what it switches to with
                // `ConfigureAwait(false)` stays in it.
                let saved = (self.ctx, self.in_lambda, self.lambda);
                self.in_lambda = true;
                self.lambda = Some(lambda.span);
                self.statement(&lambda.body);
                (self.ctx, self.in_lambda, self.lambda) = saved;
            }
            E::Await { operand, .. } => {
                let waited = self.waited_call(operand);
                if let Some(span) = waited {
                    self.awaited.insert(span);
                }
                self.expression(operand);
                if let Some(switch) = self.thread_switch(operand) {
                    self.ctx = match switch {
                        Some(label) => {
                            let site = self.site(label, expression.span.end(), true, false);
                            Ctx::Worker(site)
                        }
                        None => Ctx::Main,
                    };
                }
            }
            _ => {
                for child in expression_children(expression) {
                    self.expression(child);
                }
            }
        }
    }

    /// The call an `await` waits for: its operand, or what
    /// `ConfigureAwait` was called on.
    fn waited_call(&self, operand: &BoundExpression) -> Option<TextSpan> {
        match &operand.kind {
            E::Conversion { operand, .. } => self.waited_call(operand),
            E::Call {
                receiver: Some(receiver),
                method,
                ..
            } if self.symbols.get(*method).name == "ConfigureAwait" => Some(receiver.span),
            E::Call { .. } => Some(operand.span),
            _ => None,
        }
    }

    /// Where an awaited operand leaves the code after it: `Some(Some(label))`
    /// on a background thread, `Some(None)` back on the main one.
    fn thread_switch(&self, operand: &BoundExpression) -> Option<Option<&'static str>> {
        let E::Call {
            method, arguments, ..
        } = &operand.kind
        else {
            return None;
        };
        let name = self.qualified(*method);
        if name.ends_with(".ConfigureAwait")
            && arguments.first().is_some_and(|argument| {
                matches!(argument.kind, E::Literal(ConstantValue::Boolean(false)))
            })
        {
            return Some(Some("after ConfigureAwait(false)"));
        }
        match name.as_str() {
            "Cysharp.Threading.Tasks.UniTask.SwitchToThreadPool"
            | "Cysharp.Threading.Tasks.UniTask.SwitchToTaskPool" => {
                Some(Some("after UniTask.SwitchToThreadPool"))
            }
            "Cysharp.Threading.Tasks.UniTask.SwitchToMainThread"
            | "Cysharp.Threading.Tasks.UniTask.Yield"
            | "Cysharp.Threading.Tasks.UniTask.NextFrame" => Some(None),
            _ => None,
        }
    }

    fn call(
        &mut self,
        call: &BoundExpression,
        receiver: Option<&BoundExpression>,
        method: SymbolId,
        arguments: &[BoundExpression],
    ) {
        let qualified = self.qualified(method);
        let container = self
            .symbols
            .get(method)
            .container
            .map(|container| self.qualified(container))
            .unwrap_or_default();

        // `Interlocked.Increment(ref count)`, `Volatile.Read(ref flag)`.
        if container == "System.Threading.Interlocked" || container == "System.Threading.Volatile" {
            let read = qualified.ends_with(".Read");
            for argument in arguments {
                if let E::RefArgument { operand, .. } = &argument.kind
                    && let Some(member) = self.watched(operand)
                {
                    let span = self.member_span(operand, member);
                    self.record(member, span, !read, true);
                    continue;
                }
                self.expression(argument);
            }
            return;
        }

        // `items.Add(x)` changes what the field `items` holds.
        let mut receiver_done = false;
        if let Some(receiver) = receiver
            && is_mutator(&self.symbols.get(method).name)
            && is_plain_collection(&container)
            && self.watched(receiver).is_some()
        {
            self.write(receiver);
            receiver_done = true;
        }

        let after = after_receiver(receiver, call.span);
        self.unity_use(method, call.span, after);
        let site = spawner(&qualified).map(|(label, parallel)| {
            let awaited = self.awaited.contains(&call.span);
            self.site(label, call.span.start(), awaited, parallel)
        });
        // `ContinueWith` runs its continuation on the pool, after what it
        // continues: the receiver is not sent.
        if let Some(receiver) = receiver
            && !receiver_done
        {
            self.expression(receiver);
        }
        if !self.own_object(receiver) {
            self.push_call(method, self.ctx);
        }
        self.arguments_to(arguments, site);
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::{found, found_with};

    /// Just enough of the framework and of Unity for the analyzer to know
    /// them by name.
    const STUBS: &str = "\
namespace System { public delegate void Action(); public delegate void Action<T>(T a); public delegate T Func<T>(); public delegate void AsyncCallback(IAsyncResult r); public interface IAsyncResult { } }
namespace System.Threading.Tasks {
  public class Task { public static Task Run(System.Action a) => null; public static Task Run(System.Func<Task> a) => null; public TaskAwaiter GetAwaiter() => default; public ConfiguredTaskAwaitable ConfigureAwait(bool c) => default; public static Task Delay(int ms) => null; }
  public struct TaskAwaiter : System.Runtime.CompilerServices.INotifyCompletion { public bool IsCompleted => true; public void GetResult() { } public void OnCompleted(System.Action a) { } }
  public struct ConfiguredTaskAwaitable { public TaskAwaiter GetAwaiter() => default; }
  public static class Parallel { public static void For(int from, int to, System.Action<int> body) { } }
}
namespace System.Runtime.CompilerServices { public interface INotifyCompletion { void OnCompleted(System.Action a); } public class AsyncTaskMethodBuilder { } }
namespace System.Threading {
  public delegate void ThreadStart();
  public class Thread { public Thread(ThreadStart start) { } public void Start() { } }
  public static class Interlocked { public static int Increment(ref int v) => v; }
  public static class ThreadPool { public static bool QueueUserWorkItem(System.Action<object> a) => true; }
}
namespace System.Collections.Generic { public class List<T> { public void Add(T item) { } public int Count => 0; } }
namespace System.Collections.Concurrent { public class ConcurrentQueue<T> { public void Enqueue(T item) { } } }
namespace UnityEngine {
  public class Object { }
  public class Component : Object { public Transform transform => null; public T GetComponent<T>() => default; }
  public class Transform : Component { public int position { get; set; } }
  public class Behaviour : Component { }
  public class MonoBehaviour : Behaviour { }
  public static class Time { public static float deltaTime => 0; }
  public static class Debug { public static void Log(object o) { } }
  public struct Mathf { public static float Abs(float f) => f; }
}
";

    fn with_stubs(code: &str) -> String {
        format!("{code}\n{STUBS}")
    }

    fn plt(code: &str, id: &str) -> Vec<String> {
        found_with(&with_stubs(code), id)
    }

    #[test]
    fn a_field_written_in_task_run_and_read_in_update_races() {
        let code = "\
using System.Threading.Tasks;
class Loader : UnityEngine.MonoBehaviour {
  int progress;
  void Start() { Task.Run(() => { progress = 5; }); }
  void Update() { UnityEngine.Debug.Log(progress); }
}";
        assert_eq!(plt(code, "RLN1001"), ["progress", "progress"]);
        let all = found(&with_stubs(code));
        assert!(
            all.iter().any(|entry| entry.starts_with("RLN1001@")),
            "{all:?}"
        );
    }

    #[test]
    fn the_message_names_both_threads() {
        let code = "\
using System.Threading.Tasks;
class Loader {
  int progress;
  void Start() { Task.Run(() => progress = 5); }
  void Update() { System.Console.WriteLine(progress); }
}
namespace System { public static class Console { public static void WriteLine(object o) { } } }";
        let text = with_stubs(code);
        let semantic = super::super::super::tests::compile(&[("C.cs", &text)], false).unwrap();
        let all = semantic
            .analyzer_diagnostics(std::path::Path::new("/p/C.cs"), None)
            .unwrap();
        let message = &all
            .iter()
            .find(|diagnostic| diagnostic.id == "RLN1001")
            .expect("RLN1001")
            .message;
        assert_eq!(
            message,
            "'progress' is written on a background thread (Task.Run in Start) and read on the main thread (in Update) with no lock between them"
        );
    }

    #[test]
    fn a_lock_on_both_sides_or_interlocked_is_no_race() {
        let code = "\
using System.Threading;
using System.Threading.Tasks;
class Counter {
  readonly object gate = new object();
  int locked;
  int atomic;
  volatile bool done;
  void Start() {
    Task.Run(() => { lock (gate) { locked++; } Interlocked.Increment(ref atomic); done = true; });
  }
  int Read() { lock (gate) { return locked; } }
  bool Done() => done;
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn a_lock_on_one_side_only_reports_the_other() {
        let code = "\
using System.Threading.Tasks;
class Counter {
  readonly object gate = new object();
  int count;
  void Start() { Task.Run(() => { lock (gate) { count++; } }); }
  int Read() => count;
}";
        assert_eq!(plt(code, "RLN1001"), ["count"]);
    }

    #[test]
    fn a_private_helper_called_from_a_thread_runs_on_it() {
        let code = "\
using System.Threading;
class Server {
  int clients;
  void Start() { new Thread(Accept).Start(); }
  void Accept() { Grow(); }
  void Grow() { clients = clients + 1; }
  public int Clients => clients;
}";
        // The write in `Grow` and the read in `Clients`; the read in `Grow`
        // only meets other reads.
        assert_eq!(plt(code, "RLN1001"), ["clients", "clients"]);
    }

    #[test]
    fn what_runs_before_the_thread_or_after_awaiting_it_is_no_race() {
        let code = "\
using System.Threading.Tasks;
class Loader {
  int result;
  async void Load() {
    result = 0;
    await Task.Run(() => { result = 42; });
    System.Console.WriteLine(result);
  }
}
namespace System { public static class Console { public static void WriteLine(object o) { } } }";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn adding_to_a_list_from_a_thread_is_a_write() {
        let code = "\
using System.Collections.Generic;
using System.Collections.Concurrent;
using System.Threading.Tasks;
class Log {
  readonly List<string> lines = new List<string>();
  readonly ConcurrentQueue<string> queue = new ConcurrentQueue<string>();
  void Start() { Task.Run(() => { lines.Add(\"a\"); queue.Enqueue(\"b\"); }); }
  int Count() => lines.Count;
}";
        assert_eq!(plt(code, "RLN1001"), ["lines", "lines"]);
    }

    #[test]
    fn the_constructor_and_two_main_thread_methods_do_not_race() {
        let code = "\
class Plain {
  int a;
  Plain() { a = 1; }
  void Update() { a = a + 1; }
  void LateUpdate() { a = 2; }
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn after_configure_await_false_the_code_is_on_the_pool() {
        let code = "\
using System.Threading.Tasks;
class Fetch : UnityEngine.MonoBehaviour {
  int status;
  async void Start() {
    await Task.Delay(10).ConfigureAwait(false);
    status = 1;
    var t = transform;
  }
  void Update() { if (status == 1) { } }
}";
        assert_eq!(plt(code, "RLN1001"), ["status", "status"]);
        assert_eq!(plt(code, "RLN1002"), ["transform"]);
    }

    #[test]
    fn unity_api_from_a_thread_is_reported_and_plain_math_is_not() {
        let code = "\
using System.Threading.Tasks;
class Mover : UnityEngine.MonoBehaviour {
  void Start() {
    Task.Run(() => {
      transform.position = 1;
      var body = GetComponent<Mover>();
      var dt = UnityEngine.Time.deltaTime;
      UnityEngine.Debug.Log(UnityEngine.Mathf.Abs(1));
    });
    transform.position = 2;
  }
}";
        assert_eq!(
            plt(code, "RLN1002"),
            ["transform", "position", "GetComponent", "deltaTime"]
        );
    }

    #[test]
    fn a_local_every_parallel_iteration_writes() {
        let code = "\
using System.Threading.Tasks;
class Sum {
  int Total(int n) {
    int sum = 0;
    Parallel.For(0, n, i => { int own = i; own++; sum += i; });
    return sum;
  }
}";
        assert_eq!(plt(code, "RLN1003"), ["sum"]);
    }

    #[test]
    fn a_field_every_parallel_iteration_writes_races_with_itself() {
        let code = "\
using System.Threading.Tasks;
class Sum {
  int total;
  void Run(int n) { Parallel.For(0, n, i => { total += i; }); }
}";
        assert_eq!(plt(code, "RLN1001"), ["total"]);
    }

    #[test]
    fn thread_static_fields_are_each_threads_own() {
        let code = "\
using System.Threading.Tasks;
class Cache {
  [System.ThreadStatic] static int scratch;
  void Start() { Task.Run(() => { scratch = 1; }); }
  int Read() => scratch;
}
namespace System { public class ThreadStaticAttribute : Attribute { } public class Attribute { } }";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    // What a real game client and server showed.

    #[test]
    fn what_setup_writes_before_the_thread_starts_is_no_race_but_disposing_is() {
        let code = "\
using System.Threading.Tasks;
class Cache {
  System.Collections.Generic.List<int> responses;
  void OnAwake() { responses = new System.Collections.Generic.List<int>(); }
  void OnUpdate() { Task.Run(() => { responses.Add(1); }); }
  void Dispose() { responses = null; }
}";
        assert_eq!(plt(code, "RLN1001"), ["responses", "responses"]);
        let text = with_stubs(code);
        let at = |needle: &str| text.find(needle).unwrap();
        let semantic = super::super::super::tests::compile(&[("C.cs", &text)], false).unwrap();
        let starts: Vec<usize> = semantic
            .analyzer_diagnostics(std::path::Path::new("/p/C.cs"), None)
            .unwrap()
            .iter()
            .filter(|d| d.id == "RLN1001")
            .map(|d| d.span.start() as usize)
            .collect();
        assert_eq!(starts, [at("responses.Add"), at("responses = null")]);
    }

    #[test]
    fn a_builder_configured_before_it_is_sent_is_no_race() {
        let code = "\
using System.Threading.Tasks;
class Http {
  string url;
  int retries;
  public Http Url(string value) { url = value; return this; }
  public Http Retries(int value) { retries = value; return this; }
  public void Send() { Task.Run(() => { Get(url, retries); }); }
  static void Get(string u, int r) { }
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn what_the_starting_method_calls_first_runs_before_the_thread() {
        let code = "\
using System.Threading.Tasks;
class Cover {
  float radius;
  void Scan() { radius = 2; }
  public void Run() { Scan(); Task.Run(() => { Use(radius); }); }
  static void Use(float r) { }
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn parallel_for_returns_when_its_body_is_done() {
        let code = "\
using System.Threading.Tasks;
class Bake {
  int[] positions;
  public void Prepare(int n) { Parallel.For(0, n, i => { Use(positions[i]); }); }
  public void Execute() { Prepare(4); positions = null; }
  static void Use(int p) { }
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn an_object_made_inside_the_parallel_body_is_its_own() {
        let code = "\
using System.Threading.Tasks;
class Grid {
  int count;
  public void Add() { count++; }
}
class Cover {
  public void Run(int n) { Parallel.For(0, n, i => { var grid = new Grid(); grid.Add(); }); }
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn a_method_only_the_thread_calls_is_on_that_thread_once_per_member() {
        let code = "\
using System.Threading.Tasks;
class Lock {
  bool acquired;
  public bool IsAcquired => acquired;
  public void TryAcquire() { Task.Run(() => { Acquire(); }); }
  public void Acquire() { acquired = false; acquired = true; }
}";
        assert_eq!(plt(code, "RLN1001"), ["acquired", "acquired"]);
        let text = with_stubs(code);
        let semantic = super::super::super::tests::compile(&[("C.cs", &text)], false).unwrap();
        let messages: Vec<String> = semantic
            .analyzer_diagnostics(std::path::Path::new("/p/C.cs"), None)
            .unwrap()
            .into_iter()
            .filter(|d| d.id == "RLN1001")
            .map(|d| d.message)
            .collect();
        assert_eq!(
            messages,
            [
                "'acquired' is read on the main thread (in IsAcquired) and written on a background thread (Task.Run in TryAcquire) with no lock between them",
                "'acquired' is written on a background thread (Task.Run in TryAcquire) and read on the main thread (in IsAcquired) with no lock between them",
            ]
        );
    }

    #[test]
    fn a_method_called_before_the_thread_and_again_later_is_not_before_it() {
        let code = "\
using System.Threading.Tasks;
class Responder {
  object socket;
  public void Start() { Close(); socket = new object(); Task.Run(() => Receive()); }
  public void Stop() { Close(); }
  void Close() { socket = null; }
  void Receive() { Use(socket); }
  static void Use(object o) { }
}";
        assert_eq!(plt(code, "RLN1001"), ["socket", "socket"]);
    }

    #[test]
    fn what_the_caller_runs_before_the_starting_method_is_before_the_thread() {
        let code = "\
using System.Threading.Tasks;
class Window {
  float radius;
  void OnGUI() { Scan(); Compute(); }
  void Scan() { radius = 2; }
  void Compute() { Task.Run(() => Use(radius)); }
  static void Use(float r) { }
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn a_builder_returning_this_under_another_type_is_set_up_first() {
        let code = "\
using System.Threading.Tasks;
interface IHttp { }
class Http : IHttp {
  string url;
  public IHttp Url(string value) { url = value; return this; }
  public void Send() { Task.Run(() => { Get(url); }); }
  static void Get(string u) { }
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn two_threads_writing_the_same_constant_do_not_race_with_each_other() {
        let code = "\
using System.Threading.Tasks;
class Watch {
  bool changed;
  void Start() { Task.Run(() => { changed = true; }); Task.Run(() => { changed = true; }); }
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }

    #[test]
    fn a_field_copied_into_a_local_is_read_once() {
        let code = "\
using System.Threading.Tasks;
class Responder {
  object socket;
  public void Start() { Task.Run(() => Send()); }
  public void Stop() { socket = null; }
  void Send() { var copy = socket; if (copy == null) return; Use(copy); }
  static void Use(object o) { }
}";
        assert!(
            plt(code, "RLN1001").is_empty(),
            "{:?}",
            plt(code, "RLN1001")
        );
    }
}
