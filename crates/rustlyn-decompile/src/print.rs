//! Writing expressions and statements out as C#.
//!
//! Precedence decides the parentheses, names decide what a local is called,
//! and where a local is first assigned decides where it is declared. None of
//! that is in the IL; all of it is what makes the output read as source.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use rustlyn_metadata::signature::TypeSig;

use crate::ir::{BinOp, Body, Cmp, Expr, Interpolation, Stmt, UnOp};
use crate::names::MethodRef;
use crate::stack::MethodContext;

/// A variable a body declares: a local of the method, or a temporary the
/// decompiler could not fold away.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Var {
    Local(u16),
    Slot(u32),
}

/// Prints a body with the names and declarations worked out for it.
#[derive(Clone, Debug)]
pub struct Printer<'c, 'a> {
    /// Names suggested for locals by whoever made them.
    pub hints: HashMap<u16, String>,
    ctx: &'c MethodContext<'a>,
    param_names: Vec<String>,
    var_names: HashMap<Var, String>,
    var_types: HashMap<Var, TypeSig>,
    /// The `ref` variables bound to references that are read-only.
    readonly_refs: HashSet<Var>,
    /// The type parameters of the local functions being printed.
    extra_method_params: std::rc::Rc<std::cell::RefCell<Vec<String>>>,
    /// The names of the types nested in the one printed and in those
    /// enclosing it.
    nested_names: HashSet<String>,
    /// Variables declared by the statement at each path, when the first
    /// assignment doubles as the declaration.
    inline_declarations: HashSet<(Vec<usize>, Var)>,
    /// Variables only ever passed as `out` and never read: `out T _`.
    discards: HashSet<Var>,
    /// Variables declared in the block at each path, each right before
    /// the statement (by index) that first uses it.
    top_declarations: HashMap<Vec<usize>, Vec<(usize, Var)>>,
    out: String,
    indent: usize,
    /// The printed names of the type the body belongs to and of the types
    /// it is nested in, innermost first.
    own_type_names: Vec<String>,
    /// Whether variables print as `V_n`/`S_n`/`A_n`, for debugging.
    raw: bool,
    /// The path of the statement being printed, for the blocks nested in
    /// its expressions.
    current_path: Vec<usize>,
    /// The offsets at which the cases of the switches being printed start,
    /// and the case each is: a `goto` there is `goto case`.
    case_labels: HashMap<u32, String>,
    /// The paths of the `switch` statements: its sections are one scope.
    switch_paths: HashSet<Vec<usize>>,
    /// The `out var` declarations written, so that a second `out` of the
    /// same variable in the statement does not declare it again.
    declared_inline: std::cell::RefCell<HashSet<(Vec<usize>, Var)>>,
    /// The paths of the bodies of `using`s written as declarations: they
    /// are the block around them.
    flat_bodies: HashSet<Vec<usize>>,
}

/// Where lambda bodies hang in the path space: past any statement index.
const LAMBDA_PATH_BASE: usize = 1 << 40;

const KEYWORDS: &[&str] = &[
    "abstract",
    "as",
    "base",
    "bool",
    "break",
    "byte",
    "case",
    "catch",
    "char",
    "checked",
    "class",
    "const",
    "continue",
    "decimal",
    "default",
    "delegate",
    "do",
    "double",
    "else",
    "enum",
    "event",
    "explicit",
    "extern",
    "false",
    "finally",
    "fixed",
    "float",
    "for",
    "foreach",
    "goto",
    "if",
    "implicit",
    "in",
    "int",
    "interface",
    "internal",
    "is",
    "lock",
    "long",
    "namespace",
    "new",
    "null",
    "object",
    "operator",
    "out",
    "override",
    "params",
    "private",
    "protected",
    "public",
    "readonly",
    "ref",
    "return",
    "sbyte",
    "sealed",
    "short",
    "sizeof",
    "stackalloc",
    "static",
    "string",
    "struct",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "uint",
    "ulong",
    "unchecked",
    "unsafe",
    "ushort",
    "using",
    "virtual",
    "void",
    "volatile",
    "while",
];

impl<'c, 'a> Printer<'c, 'a> {
    /// A printer for a body, given the parameter names.
    pub fn new(
        ctx: &'c MethodContext<'a>,
        param_names: Vec<String>,
        slot_types: &HashMap<u32, TypeSig>,
    ) -> Self {
        let mut var_types = HashMap::new();
        for (index, ty) in ctx.locals.iter().enumerate() {
            var_types.insert(Var::Local(index as u16), ty.clone());
        }
        for (id, ty) in slot_types {
            var_types.insert(Var::Slot(*id), ty.clone());
        }
        let own = match &ctx.this_type {
            TypeSig::ByRef(inner) => inner.as_ref(),
            other => other,
        };
        let nested_names = match own {
            TypeSig::Class(token) | TypeSig::ValueType(token)
                if token.table() == rustlyn_metadata::table::TYPE_DEF =>
            {
                ctx.resolver.nested_names_in_scope(token.row())
            }
            TypeSig::Generic { definition, .. } => match definition.as_ref() {
                TypeSig::Class(token) | TypeSig::ValueType(token)
                    if token.table() == rustlyn_metadata::table::TYPE_DEF =>
                {
                    ctx.resolver.nested_names_in_scope(token.row())
                }
                _ => HashSet::new(),
            },
            _ => HashSet::new(),
        };
        let mut own_type_names = Vec::new();
        if let TypeSig::Generic { .. } | TypeSig::Class(_) | TypeSig::ValueType(_) = own {
            let mut name = ctx.resolver.type_name(own, &ctx.generics);
            loop {
                own_type_names.push(name.clone());
                // `Outer<T>.Inner` encloses `Inner`; the generic arguments
                // never hold a dot at the top level, so the last one splits.
                let Some(at) = split_enclosing(&name) else {
                    break;
                };
                name.truncate(at);
            }
        }
        Self {
            hints: HashMap::new(),
            ctx,
            param_names,
            var_names: HashMap::new(),
            var_types,
            readonly_refs: HashSet::new(),
            extra_method_params: std::rc::Rc::default(),
            nested_names,
            inline_declarations: HashSet::new(),
            discards: HashSet::new(),
            top_declarations: HashMap::new(),
            out: String::new(),
            indent: 0,
            own_type_names,
            raw: false,
            current_path: Vec::new(),
            case_labels: HashMap::new(),
            switch_paths: HashSet::new(),
            declared_inline: std::cell::RefCell::new(HashSet::new()),
            flat_bodies: HashSet::new(),
        }
    }

    /// The body as text, indented by the given number of levels.
    #[must_use]
    pub fn body(mut self, stmts: &[Stmt], indent: usize) -> String {
        self.indent = indent;
        if !self.raw {
            self.plan(stmts);
        }
        // `ref readonly T r = ref F()` of a call returning `ref readonly`.
        for stmt in stmts {
            stmt.walk_exprs(&mut |expr| {
                if let Expr::Assign(target, value) = expr
                    && let Some(var) = var_of(target)
                    && matches!(self.var_types.get(&var), Some(TypeSig::ByRef(_)))
                    && self.is_readonly_ref(value)
                {
                    self.readonly_refs.insert(var);
                }
            });
        }
        self.block_contents(stmts, &mut Vec::new());
        self.out
    }

    /// A single expression, with names as they would be in the body.
    #[must_use]
    pub fn expression(mut self, expr: &Expr) -> String {
        let mut refs: HashMap<Var, Vec<Reference>> = HashMap::new();
        let mut path = Vec::new();
        collect_expr(expr, &mut path, 0, false, &mut refs);
        self.name_all(&refs);
        self.expr(expr, 0)
    }

    /// The type parameters in scope: the method's, and those of the local
    /// functions being printed.
    fn generics(&self) -> std::borrow::Cow<'_, crate::names::Generics> {
        let extra = self.extra_method_params.borrow();
        if extra.is_empty() {
            return std::borrow::Cow::Borrowed(&self.ctx.generics);
        }
        let mut generics = self.ctx.generics.clone();
        generics.method_params.extend(extra.iter().cloned());
        std::borrow::Cow::Owned(generics)
    }

    fn type_name(&self, ty: &TypeSig) -> String {
        let name = self.ctx.resolver.type_name(ty, &self.generics());
        // A type nested in the one being printed, or in one enclosing it,
        // goes by its own name.
        for own in &self.own_type_names {
            if name.starts_with(own.as_str()) && name[own.len()..].starts_with('.') {
                return name[own.len() + 1..].to_string();
            }
        }
        // Another type named like one of those is hidden by it, and so is
        // one named like a method of the type printed: `Handle` in a class
        // with a `Handle(int)`.
        let head = name.split(['<', '.', '[']).next().unwrap_or(&name);
        if self.nested_names.contains(head)
            || (!head.is_empty()
                && head.chars().next().is_some_and(char::is_uppercase)
                && self.ctx.resolver.has_method_named(self.own_type(), head))
        {
            return self
                .ctx
                .resolver
                .qualified()
                .type_name(ty, &self.generics());
        }
        name
    }

    fn type_of(&self, expr: &Expr) -> Option<TypeSig> {
        let slot_types: HashMap<u32, TypeSig> = self
            .var_types
            .iter()
            .filter_map(|(var, ty)| match var {
                Var::Slot(id) => Some((*id, ty.clone())),
                Var::Local(_) => None,
            })
            .collect();
        crate::simplify::Typer {
            ctx: self.ctx,
            slot_types: &slot_types,
            extra_locals: std::cell::RefCell::new(Vec::new()),
            hints: std::cell::RefCell::new(HashMap::new()),
        }
        .type_of(expr)
    }

    /// Whether a member's declaring type encloses the one whose body is
    /// printed: its static members are in scope unqualified.
    fn is_enclosing_type(&self, declaring: &TypeSig) -> bool {
        let name = self.ctx.resolver.type_name(declaring, &self.ctx.generics);
        self.own_type_names.iter().skip(1).any(|own| *own == name)
    }

    /// The type whose body is printed.
    fn own_type(&self) -> &TypeSig {
        match &self.ctx.this_type {
            TypeSig::ByRef(inner) => inner.as_ref(),
            other => other,
        }
    }

    /// Whether a member's declaring type is the one whose body is printed,
    /// so the qualifier can go.
    fn is_own_type(&self, declaring: &TypeSig) -> bool {
        let own = match &self.ctx.this_type {
            TypeSig::ByRef(inner) => inner.as_ref(),
            other => other,
        };
        let strip = |ty: &TypeSig| match ty {
            TypeSig::Generic { definition, .. } => (**definition).clone(),
            other => other.clone(),
        };
        strip(declaring) == strip(own)
    }

    fn line(&mut self, text: &str) {
        for _ in 0..self.indent {
            self.out.push('\t');
        }
        self.out.push_str(text);
        self.out.push('\n');
    }

    // ----- declarations -----

    /// Decides where every variable is declared: at its first assignment when
    /// that assignment is in the block every other use is inside, at the top
    /// of that block otherwise.
    fn plan(&mut self, stmts: &[Stmt]) {
        let mut refs: HashMap<Var, Vec<Reference>> = HashMap::new();
        collect_block(stmts, &mut Vec::new(), &mut refs);
        self.switch_paths.clear();
        self.flat_bodies.clear();
        switch_paths(
            stmts,
            &mut Vec::new(),
            &mut self.switch_paths,
            &mut self.flat_bodies,
        );
        self.name_all(&refs);
        for (var, uses) in &refs {
            if uses.iter().any(|r| r.binding) {
                // A `foreach`, `using`, `catch` or pattern declares it.
                continue;
            }
            if let [only] = uses.as_slice()
                && only.out_arg
                && matches!(var, Var::Local(_))
            {
                self.discards.insert(*var);
                continue;
            }
            let mut lca = common_prefix(uses.iter().map(|r| r.block.as_slice()));
            // Uses in two blocks of one statement (two `case`s of a
            // `switch`) share that statement, not a block: the variable is
            // declared in the block around the statement.
            if lca.len() % 2 == 1 {
                lca.pop();
            }
            // The position, in the LCA block, of the statement each use is in.
            let position = |r: &Reference| -> usize {
                if r.block.len() == lca.len() {
                    r.stmt
                } else {
                    r.block[lca.len()]
                }
            };
            let first = uses.iter().map(position).min().unwrap_or(0);
            // An `out` argument declares the variable as `out var` when
            // something reads it afterwards; one that is only written is
            // declared plainly, the way it was.
            let read_elsewhere = uses.iter().any(|r| !r.out_arg && !r.declaring);
            let declares_here = uses.iter().any(|r| {
                r.block.len() == lca.len()
                    && r.stmt == first
                    && r.declaring
                    && (!r.out_arg || read_elsewhere)
            });
            let header_here = uses
                .iter()
                .any(|r| r.block.len() == lca.len() && r.stmt == first && r.header);
            let inside_first_stmt = uses
                .iter()
                .any(|r| r.block.len() > lca.len() && r.block[lca.len()] == first);
            // `if (d.TryGetValue(k, out var v)) { use(v); }`: a variable
            // declared in an `if` condition is in scope in its branches and
            // after it.
            let out_in_if = declares_here
                && uses.iter().any(|r| {
                    r.block.len() == lca.len() && r.stmt == first && r.declaring && r.out_arg
                })
                && {
                    let mut path = lca.clone();
                    path.push(first);
                    matches!(stmt_at(stmts, &path), Some(Stmt::If { .. }))
                };
            // `while (F(out var x))` scopes `x` to the loop: one read after
            // it is declared before.
            let loop_scoped = uses.iter().any(|r| r.out_arg && r.declaring)
                && {
                    let mut path = lca.clone();
                    path.push(first);
                    matches!(
                        stmt_at(stmts, &path),
                        Some(Stmt::While { .. } | Stmt::DoWhile { .. } | Stmt::For { .. })
                    )
                }
                && uses.iter().any(|r| position(r) > first);
            // `while (F(out var x)) { use(x); }`: declared in the condition of
            // a `while` or a `for` and used nowhere after it, the variable is
            // the loop's own, a new one each time round, as a lambda that
            // captures it sees. Declared before the loop, every lambda would
            // share one. (A `do`'s condition comes after its body, which
            // could not see it.)
            let out_in_loop = declares_here
                && uses.iter().any(|r| {
                    r.block.len() == lca.len() && r.stmt == first && r.declaring && r.out_arg
                })
                && {
                    let mut path = lca.clone();
                    path.push(first);
                    matches!(
                        stmt_at(stmts, &path),
                        Some(Stmt::While { .. } | Stmt::For { .. })
                    )
                }
                && !uses.iter().any(|r| position(r) > first);
            if declares_here
                && !loop_scoped
                && (!inside_first_stmt || header_here || out_in_if || out_in_loop)
            {
                let mut path = lca.clone();
                path.push(first);
                self.inline_declarations.insert((path, *var));
            } else {
                self.top_declarations
                    .entry(lca)
                    .or_default()
                    .push((first, *var));
            }
        }
        for vars in self.top_declarations.values_mut() {
            vars.sort_by_key(|(first, var)| match var {
                Var::Local(at) => (*first, 0, u32::from(*at)),
                Var::Slot(id) => (*first, 1, *id),
            });
        }
    }

    fn name_all(&mut self, refs: &HashMap<Var, Vec<Reference>>) {
        // A name may be reused by variables whose scopes do not overlap:
        // two lambdas may each have an `x`. A variable's scope is the block
        // all its uses share.
        // The sections of a `switch` are one scope in C#: a variable of
        // one section is in all of them.
        let scope_of = |uses: &[Reference]| -> Vec<usize> {
            let mut scope = common_prefix(uses.iter().map(|r| r.block.as_slice()));
            // A `using` declaration's body is the block around it.
            while let Some(at) =
                (2..=scope.len()).find(|at| self.flat_bodies.contains(&scope[..*at]))
            {
                scope.truncate(at - 2);
            }
            if let Some(at) = (0..scope.len()).find(|at| self.switch_paths.contains(&scope[..*at]))
            {
                scope.truncate(at);
                scope.push(usize::MAX);
            }
            scope
        };
        let overlaps = |a: &[usize], b: &[usize]| a.starts_with(b) || b.starts_with(a);
        let mut taken: Vec<(String, Vec<usize>)> = self
            .param_names
            .iter()
            .map(|name| (name.clone(), Vec::new()))
            .collect();
        let mut vars: Vec<&Var> = refs.keys().collect();
        vars.sort_by_key(|var| match var {
            Var::Local(at) => (0, u32::from(*at)),
            Var::Slot(id) => (1, *id),
        });
        for var in vars {
            let scope = scope_of(&refs[var]);
            let suggested = match var {
                Var::Local(at) => self.hints.get(at).cloned(),
                Var::Slot(_) => None,
            };
            let uses = &refs[var];
            // A construct that binds the variable names it; then the `out`
            // parameter it is passed as; then what is stored into it, when
            // every store says the same; then where every read takes it.
            let binding_hint = uses
                .iter()
                .filter(|r| r.binding)
                .find_map(|r| r.hint.as_deref().map(|hint| self.foreach_hint(hint)));
            let out_hint = uses
                .iter()
                .filter(|r| r.out_arg)
                .find_map(|r| r.hint.clone());
            let store_hint = {
                let stores: Vec<&Option<String>> = uses
                    .iter()
                    .filter(|r| r.declaring && !r.out_arg && !r.binding)
                    .map(|r| &r.hint)
                    .collect();
                if !stores.is_empty() && stores.iter().all(|hint| *hint == stores[0]) {
                    stores[0].clone()
                } else {
                    None
                }
            };
            let load_hint = {
                let by_address = self
                    .var_types
                    .get(var)
                    .is_some_and(|ty| self.ctx.resolver.is_value_type(ty));
                let reads = uses
                    .iter()
                    .filter(|r| {
                        !(r.declaring
                            || r.out_arg
                            || r.compound
                            || r.load_hint.is_some()
                            || (r.receiver && by_address))
                    })
                    .count();
                let hinted: Vec<&str> =
                    uses.iter().filter_map(|r| r.load_hint.as_deref()).collect();
                let distinct: std::collections::BTreeSet<&str> = hinted.iter().copied().collect();
                (distinct.len() == 1 && hinted.len() == reads)
                    .then(|| distinct.iter().next().map(|s| (*s).to_string()))
                    .flatten()
            };
            let mut hint = suggested
                .or(binding_hint)
                .or(out_hint)
                .or(store_hint)
                .or(load_hint)
                .or_else(|| self.var_types.get(var).map(|ty| self.hint_for_type(ty)))
                .unwrap_or_else(|| "value".to_string());
            // Only an `int` counter is an `i`.
            if hint == "i" && !matches!(self.var_types.get(var), Some(TypeSig::Int32)) {
                hint = self
                    .var_types
                    .get(var)
                    .map_or_else(|| "num".to_string(), |ty| self.hint_for_type(ty));
            }
            let base = sanitize(&hint);
            let mut name = base.clone();
            let mut counter = 2;
            while KEYWORDS.contains(&name.as_str())
                || taken
                    .iter()
                    .any(|(used, used_scope)| *used == name && overlaps(used_scope, &scope))
            {
                name = format!("{base}{counter}");
                counter += 1;
            }
            taken.push((name.clone(), scope));
            self.var_names.insert(*var, name);
        }
    }

    /// Resolves a `foreach` hint that names the collection variable: the
    /// singular of its name, or `item`.
    fn foreach_hint(&self, hint: &str) -> String {
        let source = if let Some(at) = hint.strip_prefix(FOREACH_ARG) {
            at.parse::<usize>()
                .ok()
                .and_then(|at| self.param_names.get(at).cloned())
        } else if let Some(at) = hint.strip_prefix(FOREACH_LOCAL) {
            at.parse::<u16>()
                .ok()
                .and_then(|at| self.var_names.get(&Var::Local(at)).cloned())
        } else {
            return hint.to_string();
        };
        source
            .and_then(|name| singular(&name))
            .unwrap_or_else(|| "item".to_string())
    }

    /// A name for a variable of a type, the way readers expect: `num` for a
    /// number, `text` for a string, `list` for a list.
    fn hint_for_type(&self, ty: &TypeSig) -> String {
        match ty {
            TypeSig::Boolean => "flag".into(),
            TypeSig::Char => "c".into(),
            TypeSig::SByte
            | TypeSig::Byte
            | TypeSig::Int16
            | TypeSig::UInt16
            | TypeSig::Int32
            | TypeSig::UInt32
            | TypeSig::Int64
            | TypeSig::UInt64
            | TypeSig::Single
            | TypeSig::Double
            | TypeSig::IntPtr
            | TypeSig::UIntPtr => "num".into(),
            TypeSig::String => "text".into(),
            TypeSig::Object => "obj".into(),
            TypeSig::Vector(_) | TypeSig::Array { .. } => "array".into(),
            TypeSig::Pointer(_) => "ptr".into(),
            TypeSig::ByRef(inner) => self.hint_for_type(inner),
            TypeSig::Var(_) | TypeSig::MVar(_) => "val".into(),
            TypeSig::Generic {
                definition,
                arguments,
            } => {
                let name = self.type_name(definition);
                if name == "Nullable" || name.ends_with('?') {
                    return arguments
                        .first()
                        .map_or_else(|| "value".into(), |inner| self.hint_for_type(inner));
                }
                if name.starts_with('(') {
                    return "tuple".into();
                }
                camel_of_type(&name)
            }
            TypeSig::Class(_) | TypeSig::ValueType(_) => {
                let name = self.type_name(ty);
                match name.as_str() {
                    "Exception" => "ex".into(),
                    "decimal" => "num".into(),
                    _ => camel_of_type(&name),
                }
            }
            _ => "value".into(),
        }
    }

    fn var_name(&self, var: Var) -> String {
        if self.raw {
            return match var {
                Var::Local(at) => format!("V_{at}"),
                Var::Slot(id) => format!("S_{id}"),
            };
        }
        self.var_names
            .get(&var)
            .cloned()
            .unwrap_or_else(|| match var {
                Var::Local(at) => format!("V_{at}"),
                Var::Slot(id) => format!("S_{id}"),
            })
    }

    fn var_type(&self, var: Var) -> String {
        match self.var_types.get(&var) {
            Some(TypeSig::ByRef(inner)) if self.readonly_refs.contains(&var) => {
                format!("ref readonly {}", self.type_name(inner))
            }
            // No source names an anonymous type.
            Some(ty) if self.ctx.resolver.mentions_anonymous(ty) => "var".to_string(),
            Some(ty) => self.type_name(ty),
            None => "var".to_string(),
        }
    }

    /// Whether a reference may only be read through: what a call returning
    /// `ref readonly` gives.
    fn is_readonly_ref(&self, value: &Expr) -> bool {
        let value = match value {
            Expr::Unary(UnOp::AddressOf, inner) => inner.as_ref(),
            other => other,
        };
        match value {
            Expr::Call { method, .. } => method.sig.returns_required.iter().any(|token| {
                self.ctx.resolver.raw_name(*token).as_deref()
                    == Some("System.Runtime.InteropServices.InAttribute")
            }),
            Expr::Property {
                declaring, name, ..
            } => self.ctx.resolver.property_is_readonly_ref(declaring, name),
            // An element of a `ReadOnlySpan<T>` is read-only.
            Expr::Indexer { receiver, .. } => self.type_of(receiver).is_some_and(|ty| {
                matches!(&ty, TypeSig::Generic { definition, .. }
                    if matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                        if self.ctx.resolver.raw_name(*token).as_deref() == Some("System.ReadOnlySpan`1")))
            }),
            _ => false,
        }
    }

    // ----- statements -----

    fn block_contents(&mut self, stmts: &[Stmt], path: &mut Vec<usize>) {
        let declarations = self.top_declarations.get(path).cloned().unwrap_or_default();
        for (index, stmt) in stmts.iter().enumerate() {
            // A variable is declared right before the statement that first
            // uses it, not at the top of the block.
            for (first, var) in &declarations {
                if *first == index || (index == 0 && *first < index) {
                    // A `ref` variable is declared bound to something: to
                    // nothing, until it is given a reference.
                    let text = match self.var_types.get(var) {
                        Some(TypeSig::ByRef(inner)) => format!(
                            "scoped {} {} = ref System.Runtime.CompilerServices.Unsafe.NullRef<{}>();",
                            self.var_type(*var),
                            self.var_name(*var),
                            self.type_name(inner)
                        ),
                        _ => format!("{} {};", self.var_type(*var), self.var_name(*var)),
                    };
                    self.line(&text);
                }
            }
            path.push(index);
            // A `using` that runs to the end of its block is a using
            // declaration: one line and no extra nesting.
            if index + 1 == stmts.len()
                && let Stmt::Using {
                    local: Some(local),
                    resource,
                    body,
                } = stmt
                && !body.is_empty()
            {
                self.current_path.clone_from(path);
                let var = Var::Local(*local);
                let (prefix, resource) = match resource {
                    Expr::Await(inner) => ("await ", inner.as_ref()),
                    other => ("", other),
                };
                let text = format!(
                    "{prefix}using {} {} = {};",
                    self.var_type(var),
                    self.var_name(var),
                    self.expr(resource, 0)
                );
                self.line(&text);
                path.push(0);
                self.block_contents(body, path);
                path.pop();
                path.pop();
                continue;
            }
            self.stmt(stmt, path);
            path.pop();
        }
        // A label labels a statement: at the end of a block, an empty one.
        if let Some(Stmt::Label(target)) = stmts.last()
            && !self.case_labels.contains_key(target)
        {
            self.line(";");
        }
    }

    fn block(&mut self, stmts: &[Stmt], path: &mut Vec<usize>, block_index: usize) {
        self.line("{");
        self.indent += 1;
        path.push(block_index);
        self.block_contents(stmts, path);
        path.pop();
        self.indent -= 1;
        self.line("}");
    }

    /// The declaration prefix for an assignment that declares its target.
    fn declared_assignment(&self, target: &Expr, path: &[usize]) -> Option<String> {
        let var = var_of(target)?;
        self.inline_declarations
            .contains(&(path.to_vec(), var))
            .then(|| format!("{} ", self.var_type(var)))
    }

    #[allow(clippy::too_many_lines)]
    fn stmt(&mut self, stmt: &Stmt, path: &mut Vec<usize>) {
        self.current_path.clone_from(path);
        match stmt {
            Stmt::Expr(expr) => {
                let text = match expr {
                    // `x = (c ? a : b)`: a conditional assigned is bracketed.
                    Expr::Assign(target, value) => {
                        let prefix = self.declared_assignment(target, path).unwrap_or_default();
                        let value = match var_of(target) {
                            Some(var) => self.bound(var, value, !prefix.is_empty()),
                            None => self.expr(value, 3),
                        };
                        format!("{prefix}{} = {value}", self.expr(target, 1))
                    }
                    // `c ? a() : b()` is not a statement: it was an `if`.
                    Expr::Conditional(condition, a, b) => {
                        let branch = |value: &Expr| vec![Stmt::Expr(value.clone())];
                        let replaced = Stmt::If {
                            condition: (**condition).clone(),
                            then: branch(a),
                            otherwise: branch(b),
                        };
                        self.stmt(&replaced, path);
                        return;
                    }
                    // A call returning a reference, for its side effects.
                    Expr::Unary(UnOp::AddressOf | UnOp::Deref, inner)
                        if matches!(inner.as_ref(), Expr::Call { .. }) =>
                    {
                        self.expr(inner, 0)
                    }
                    // A value computed for nothing but its side effects.
                    other if !is_statement_expression(other) => {
                        format!("_ = {}", self.expr(other, 1))
                    }
                    other => self.expr(other, 0),
                };
                self.line(&format!("{text};"));
            }
            Stmt::Declare { local, value } => {
                let var = Var::Local(*local);
                let text = match value {
                    Some(value) => format!(
                        "{} {} = {};",
                        self.var_type(var),
                        self.var_name(var),
                        self.assigned(var, value, 3)
                    ),
                    None => format!("{} {};", self.var_type(var), self.var_name(var)),
                };
                self.line(&text);
            }
            Stmt::Return(None) => self.line("return;"),
            Stmt::Return(Some(value)) => {
                // A body returning a reference returns `ref` whatever it
                // is: an element, a call's reference, a `ref` variable.
                let by_ref = matches!(self.ctx.returns, TypeSig::ByRef(_))
                    && !matches!(value, Expr::Unary(UnOp::AddressOf, _));
                let text = format!(
                    "return {}{};",
                    if by_ref { "ref " } else { "" },
                    self.expr(value, 0)
                );
                self.line(&text);
            }
            Stmt::Throw(None) => self.line("throw;"),
            Stmt::Throw(Some(value)) => {
                let text = format!("throw {};", self.expr(value, 0));
                self.line(&text);
            }
            Stmt::If {
                condition,
                then,
                otherwise,
            } => {
                let text = format!("if ({})", self.expr(condition, 0));
                self.line(&text);
                self.block(then, path, 0);
                let mut otherwise = otherwise.as_slice();
                let mut block_index = 1;
                let mut sub_path: Vec<usize> = Vec::new();
                loop {
                    if otherwise.is_empty() {
                        break;
                    }
                    // `else if`: an else holding one `if`.
                    if let [
                        Stmt::If {
                            condition,
                            then,
                            otherwise: inner,
                        },
                    ] = otherwise
                        && !self.top_declarations.contains_key(&full_path(
                            path,
                            &sub_path,
                            block_index,
                        ))
                    {
                        // The condition is the inner `if`'s, and so are the
                        // variables it declares.
                        let mut inner_path = full_path(path, &sub_path, block_index);
                        inner_path.push(0);
                        let saved = std::mem::replace(&mut self.current_path, inner_path);
                        let text = format!("else if ({})", self.expr(condition, 0));
                        self.current_path = saved;
                        self.line(&text);
                        sub_path.push(block_index);
                        sub_path.push(0);
                        path.extend(sub_path.iter().copied());
                        let depth = sub_path.len();
                        self.block(then, path, 0);
                        for _ in 0..depth {
                            path.pop();
                        }
                        otherwise = inner;
                        block_index = 1;
                        continue;
                    }
                    self.line("else");
                    path.extend(sub_path.iter().copied());
                    let depth = sub_path.len();
                    self.block(otherwise, path, block_index);
                    for _ in 0..depth {
                        path.pop();
                    }
                    break;
                }
            }
            Stmt::While { condition, body } => {
                let text = format!("while ({})", self.expr(condition, 0));
                self.line(&text);
                self.block(body, path, 0);
            }
            Stmt::DoWhile { body, condition } => {
                self.line("do");
                self.block(body, path, 0);
                let text = format!("while ({});", self.expr(condition, 0));
                self.line(&text);
            }
            Stmt::For {
                initializer,
                condition,
                step,
                body,
            } => {
                let init = match initializer.as_deref() {
                    Some(Stmt::Expr(Expr::Assign(target, value))) => {
                        let prefix = self.declared_assignment(target, path).unwrap_or_default();
                        let value = match var_of(target) {
                            Some(var) => self.assigned(var, value, 3),
                            None => self.expr(value, 3),
                        };
                        format!("{prefix}{} = {value}", self.expr(target, 1))
                    }
                    Some(Stmt::Expr(other)) => self.expr(other, 0),
                    _ => String::new(),
                };
                let step_text = step
                    .as_ref()
                    .map_or(String::new(), |step| self.expr(step, 0));
                let text = format!("for ({init}; {}; {step_text})", self.expr(condition, 0));
                self.line(&text);
                self.block(body, path, 0);
            }
            Stmt::ForEach {
                local,
                source,
                body,
            } => {
                let var = Var::Local(*local);
                let (prefix, source) = match source {
                    Expr::Await(inner) => ("await ", inner.as_ref()),
                    other => ("", other),
                };
                let text = format!(
                    "{prefix}foreach ({} {} in {})",
                    self.var_type(var),
                    self.var_name(var),
                    self.expr(source, 0)
                );
                self.line(&text);
                self.block(body, path, 0);
            }
            Stmt::Using {
                local,
                resource,
                body,
            } => {
                let (prefix, resource) = match resource {
                    Expr::Await(inner) => ("await ", inner.as_ref()),
                    other => ("", other),
                };
                let text = match local {
                    Some(local) => {
                        let var = Var::Local(*local);
                        format!(
                            "{prefix}using ({} {} = {})",
                            self.var_type(var),
                            self.var_name(var),
                            self.expr(resource, 0)
                        )
                    }
                    None => format!("{prefix}using ({})", self.expr(resource, 0)),
                };
                self.line(&text);
                self.block(body, path, 0);
            }
            Stmt::Lock { target, body } => {
                let text = format!("lock ({})", self.expr(target, 0));
                self.line(&text);
                self.block(body, path, 0);
            }
            Stmt::Fixed { local, init, body } => {
                let var = Var::Local(*local);
                let init = match init {
                    Expr::Unary(UnOp::AddressOf, inner) => format!("&{}", self.expr(inner, 14)),
                    other => self.expr(other, 0),
                };
                let text = format!(
                    "fixed ({} {} = {init})",
                    self.var_type(var),
                    self.var_name(var)
                );
                self.line(&text);
                self.block(body, path, 0);
            }
            Stmt::Switch { value, cases } => {
                let text = format!("switch ({})", self.expr(value, 0));
                self.line(&text);
                self.line("{");
                let mut starts = Vec::new();
                for case in cases {
                    // `goto case` in a switch nested in this one is that
                    // switch's: a section jumped to from there keeps its
                    // label, in sight anywhere in the switch.
                    if let Some(Stmt::Label(at)) = case.body.first()
                        && let Some(label) = case.labels.first()
                        && !cases
                            .iter()
                            .any(|case| jumps_from_nested_switch(&case.body, *at, false))
                    {
                        let text = match label {
                            Some(label) => format!("case {}", self.expr(label, 0)),
                            None => "default".to_string(),
                        };
                        self.case_labels.insert(*at, text);
                        starts.push(*at);
                    }
                }
                for (index, case) in cases.iter().enumerate() {
                    for label in &case.labels {
                        match label {
                            Some(label) => {
                                let text = format!("case {}:", self.expr(label, 0));
                                self.line(&text);
                            }
                            None => self.line("default:"),
                        }
                    }
                    self.indent += 1;
                    path.push(index);
                    // A `using` declaration is not allowed straight in a
                    // switch section: the section gets braces.
                    let braced = matches!(case.body.last(), Some(Stmt::Using { local: Some(_), body, .. }) if !body.is_empty());
                    if braced {
                        self.line("{");
                        self.indent += 1;
                    }
                    self.block_contents(&case.body, path);
                    if braced {
                        self.indent -= 1;
                        self.line("}");
                    }
                    path.pop();
                    if !case.body.last().is_some_and(Stmt::ends_flow) {
                        self.line("break;");
                    }
                    self.indent -= 1;
                }
                self.line("}");
                for at in starts {
                    self.case_labels.remove(&at);
                }
            }
            Stmt::Try {
                body,
                catches,
                finally,
            } => {
                self.line("try");
                self.block(body, path, 0);
                for (index, catch) in catches.iter().enumerate() {
                    let mut header = String::from("catch");
                    // `catch (object)` is no C#: a filter's handler, typed
                    // by nothing, catches everything, as a bare `catch` does.
                    if let Some(ty) = &catch.ty
                        && !(*ty == TypeSig::Object && catch.variable.is_none())
                    {
                        let _ = write!(header, " ({}", self.type_name(ty));
                        if let Some(variable) = catch.variable {
                            let _ = write!(header, " {}", self.var_name(Var::Local(variable)));
                        }
                        header.push(')');
                    }
                    if let Some(filter) = &catch.filter {
                        let _ = write!(header, " when ({})", self.expr(filter, 0));
                    }
                    self.line(&header);
                    self.block(&catch.body, path, index + 1);
                }
                if let Some(finally) = finally {
                    self.line("finally");
                    self.block(finally, path, catches.len() + 1);
                }
            }
            Stmt::Checked(body) => {
                self.line("checked");
                self.block(body, path, 0);
            }
            Stmt::Break => self.line("break;"),
            Stmt::Continue => self.line("continue;"),
            Stmt::Goto(target) => {
                let text = match self.case_labels.get(target) {
                    Some(case) => format!("goto {case};"),
                    None => format!("goto IL_{target:04x};"),
                };
                self.line(&text);
            }
            Stmt::Label(target) if self.case_labels.contains_key(target) => {}
            Stmt::Label(target) => {
                let saved = self.indent;
                self.indent = saved.saturating_sub(1);
                let text = format!("IL_{target:04x}:");
                self.line(&text);
                self.indent = saved;
            }
            Stmt::Comment(text) => {
                let text = format!("// {text}");
                self.line(&text);
            }
            Stmt::YieldReturn(value) => {
                let text = format!("yield return {};", self.expr(value, 0));
                self.line(&text);
            }
            Stmt::YieldBreak => self.line("yield break;"),
            Stmt::EnterTry(state) => {
                let text = format!("// try (state {state})");
                self.line(&text);
            }
            Stmt::LocalFunction {
                name,
                type_params,
                params,
                outs,
                returns,
                constraints,
                body,
            } => {
                // Its own type parameters are in scope in it.
                self.extra_method_params
                    .borrow_mut()
                    .extend(type_params.iter().cloned());
                let names: Vec<String> = params
                    .iter()
                    .enumerate()
                    .map(|(at, param)| {
                        let var = Var::Local(*param);
                        if outs.get(at).copied().unwrap_or(false)
                            && let Some(TypeSig::ByRef(inner)) = self.var_types.get(&var)
                        {
                            return format!("out {} {}", self.type_name(inner), self.var_name(var));
                        }
                        format!("{} {}", self.var_type(var), self.var_name(var))
                    })
                    .collect();
                // An `await` of its own makes it `async`; one in a lambda
                // inside it does not.
                let mut awaits = false;
                for stmt in body {
                    stmt.walk_exprs(&mut |e| awaits |= matches!(e, Expr::Await(_)));
                }
                let prefix = if awaits { "async " } else { "" };
                let generic = if type_params.is_empty() {
                    String::new()
                } else {
                    format!("<{}>", type_params.join(", "))
                };
                let text = format!(
                    "{prefix}{} {name}{generic}({}){constraints}",
                    self.type_name(returns),
                    names.join(", ")
                );
                self.line(&text);
                self.block(body, path, 0);
                let mut extra = self.extra_method_params.borrow_mut();
                let keep = extra.len() - type_params.len();
                extra.truncate(keep);
            }
        }
    }

    // ----- expressions -----

    /// An expression, parenthesised when its precedence is below what its
    /// position needs.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn expr(&self, expr: &Expr, needed: u8) -> String {
        let (text, precedence) = self.expr_inner(expr);
        if precedence < needed {
            format!("({text})")
        } else {
            text
        }
    }

    /// `new int[n][]`: the size goes before the brackets of an element
    /// that is itself an array.
    fn array_creation(&self, element: &TypeSig, dimensions: &str) -> String {
        let mut base = element;
        let mut suffix = String::new();
        loop {
            match base {
                TypeSig::Vector(inner) => {
                    suffix.push_str("[]");
                    base = inner;
                }
                TypeSig::Array { element, rank } => {
                    suffix.push('[');
                    suffix.push_str(&",".repeat((*rank as usize).saturating_sub(1)));
                    suffix.push(']');
                    base = element;
                }
                _ => break,
            }
        }
        format!("new {}[{dimensions}]{suffix}", self.type_name(base))
    }

    /// `{ A = 1, [k] = v, x }`: members set, indexers set, elements added.
    fn initializer(&self, initializer: &[(String, Expr)]) -> String {
        let members: Vec<String> = initializer
            .iter()
            .map(|(name, value)| match (name.as_str(), value) {
                // A collection element; a tuple is the several arguments of
                // one `Add`.
                ("", Expr::Tuple(items)) => {
                    let texts: Vec<String> = items.iter().map(|item| self.expr(item, 1)).collect();
                    format!("{{ {} }}", texts.join(", "))
                }
                ("", other) => self.expr(other, 1),
                // An indexer set: the keys, then the value.
                ("[]", Expr::Tuple(items)) if items.len() >= 2 => {
                    let (value, keys) = items.split_last().unwrap_or((&items[0], &[]));
                    let texts: Vec<String> = keys.iter().map(|key| self.expr(key, 1)).collect();
                    format!("[{}] = {}", texts.join(", "), self.expr(value, 1))
                }
                (name, value) => format!("{name} = {}", self.expr(value, 1)),
            })
            .collect();
        format!("{{ {} }}", members.join(", "))
    }

    #[allow(clippy::too_many_lines)]
    fn expr_inner(&self, expr: &Expr) -> (String, u8) {
        const PRIMARY: u8 = 15;
        const UNARY: u8 = 14;
        match expr {
            Expr::This => ("this".into(), PRIMARY),
            Expr::Base => ("base".into(), PRIMARY),
            Expr::Arg(at) => (
                // Declared as `@delegate`, so used as it too.
                self.param_names.get(*at as usize).map_or_else(
                    || format!("arg{at}"),
                    |name| {
                        if is_keyword(name) {
                            format!("@{name}")
                        } else {
                            name.clone()
                        }
                    },
                ),
                PRIMARY,
            ),
            Expr::Local(at) => (self.var_name(Var::Local(*at)), PRIMARY),
            Expr::Slot(id) => (self.var_name(Var::Slot(*id)), PRIMARY),
            Expr::CaughtException => ("<exception>".into(), PRIMARY),
            Expr::Int(n) => match *n {
                n if n == i64::from(i32::MAX) => ("int.MaxValue".into(), PRIMARY),
                n if n == i64::from(i32::MIN) => ("int.MinValue".into(), PRIMARY),
                n => (n.to_string(), if n < 0 { UNARY } else { PRIMARY }),
            },
            Expr::Long(n) => match *n {
                i64::MAX => ("long.MaxValue".into(), PRIMARY),
                i64::MIN => ("long.MinValue".into(), PRIMARY),
                n => (format!("{n}L"), if n < 0 { UNARY } else { PRIMARY }),
            },
            Expr::Float(f, single) => {
                if let Some(name) = well_known_float(*f, *single) {
                    return (name.into(), PRIMARY);
                }
                (
                    float_text(*f, *single),
                    if *f < 0.0 { UNARY } else { PRIMARY },
                )
            }
            Expr::Bool(b) => (b.to_string(), PRIMARY),
            Expr::Char(c) => (char_literal(*c), PRIMARY),
            Expr::Str(s) => (string_literal(s), PRIMARY),
            Expr::Null => ("null".into(), PRIMARY),
            Expr::EnumMember(ty, name) => (format!("{}.{name}", self.type_name(ty)), PRIMARY),
            Expr::Default(ty) => (format!("default({})", self.type_name(ty)), PRIMARY),
            // `typeof(List<>)`: a generic type named without arguments is
            // the open one.
            Expr::TypeOf(ty @ (TypeSig::Class(token) | TypeSig::ValueType(token))) => {
                let name = self
                    .ctx
                    .resolver
                    .open_generic_name(*token)
                    .unwrap_or_else(|| self.type_name(ty));
                (format!("typeof({name})"), PRIMARY)
            }
            Expr::TypeOf(ty) => (format!("typeof({})", self.type_name(ty)), PRIMARY),
            // `sizeof(nint)` wants an unsafe context; its `Size` does not.
            Expr::SizeOf(ty @ (TypeSig::IntPtr | TypeSig::UIntPtr)) => {
                (format!("{}.Size", self.type_name(ty)), PRIMARY)
            }
            Expr::SizeOf(ty) => (format!("sizeof({})", self.type_name(ty)), PRIMARY),
            Expr::Unary(op, inner) => {
                // `-(-x)`, `!(!x)`: a unary inside a unary is bracketed.
                let need = if matches!(inner.as_ref(), Expr::Unary(..)) {
                    PRIMARY
                } else {
                    UNARY
                };
                let text = self.expr(inner, need);
                match op {
                    UnOp::Neg => (format!("-{text}"), UNARY),
                    UnOp::BitNot => (format!("~{text}"), UNARY),
                    UnOp::Not => (format!("!{text}"), UNARY),
                    UnOp::AddressOf => (format!("ref {text}"), UNARY),
                    UnOp::Deref => (format!("*{text}"), UNARY),
                }
            }
            Expr::Binary(op, left, right) => {
                let precedence = op.precedence();
                let same_op = |side: &Expr| matches!(side, Expr::Binary(other, ..) if other == op);
                let (left_need, right_need) = match op {
                    // `a ?? (b + c)`: only primaries go unbracketed around
                    // `??`, but a `??` chain reads on.
                    BinOp::Coalesce => (PRIMARY, if same_op(right) { precedence } else { PRIMARY }),
                    // `a || (b && c)`, `(a == b) & (c == d)`: mixed logical
                    // and bitwise operators are bracketed for the reader.
                    BinOp::LogicalAnd | BinOp::LogicalOr | BinOp::And | BinOp::Or | BinOp::Xor => {
                        let boost = if matches!(op, BinOp::And | BinOp::Or | BinOp::Xor) {
                            UNARY
                        } else {
                            Cmp::Eq.precedence()
                        };
                        (if same_op(left) { precedence } else { boost }, boost)
                    }
                    _ => (precedence, precedence + 1),
                };
                (
                    format!(
                        "{} {} {}",
                        self.operand(left, right, left_need),
                        op.text(),
                        self.operand(right, left, right_need)
                    ),
                    precedence,
                )
            }
            Expr::Compare {
                op,
                left,
                right,
                float,
                unordered,
            } => {
                let precedence = op.precedence();
                // A reference test of a type whose `==` is its own (Unity's
                // `Object`) is `is null`: `== null` would call the operator.
                if matches!(op, Cmp::Eq | Cmp::Ne)
                    && **right == Expr::Null
                    && self
                        .type_of(left)
                        .is_some_and(|ty| self.ctx.resolver.has_equality_operator(&ty))
                {
                    let test = if *op == Cmp::Eq {
                        "is null"
                    } else {
                        "is not null"
                    };
                    return (format!("{} {test}", self.expr(left, PRIMARY)), 10);
                }
                // The null a user-defined `==` was given is plain `null`, and
                // a pointer is compared with `null`, not with a zero.
                let zero = |side: &Expr| match side {
                    Expr::Int(0) | Expr::Long(0) => true,
                    Expr::Cast(TypeSig::IntPtr | TypeSig::UIntPtr | TypeSig::Pointer(_), inner) => {
                        matches!(inner.as_ref(), Expr::Int(0) | Expr::Long(0))
                    }
                    _ => false,
                };
                let operand = |side: &Expr, other: &Expr, need: u8| match side {
                    Expr::Cast(_, inner) if **inner == Expr::Null => "null".to_string(),
                    _ if zero(side)
                        && matches!(op, Cmp::Eq | Cmp::Ne)
                        && matches!(self.type_of(other), Some(TypeSig::Pointer(_))) =>
                    {
                        "null".to_string()
                    }
                    _ => self.operand(side, other, need),
                };
                let plain = |op: Cmp| {
                    format!(
                        "{} {} {}",
                        operand(left, right, op.precedence()),
                        op.text(),
                        operand(right, left, op.precedence() + 1)
                    )
                };
                if *float && *unordered && !matches!(op, Cmp::Ne) {
                    return (format!("!({})", plain(op.negated())), UNARY);
                }
                if !*float && *unordered && !matches!(op, Cmp::Eq | Cmp::Ne) {
                    // An unsigned comparison of signed operands.
                    let cast = |side: &Expr| -> String {
                        // A member of an enum compared with `(uint)e` is
                        // its number.
                        if let Expr::EnumMember(ty, name) = side
                            && let Some(value) = self
                                .ctx
                                .resolver
                                .enum_of(ty)
                                .and_then(|members| {
                                    members.into_iter().find(|(member, _)| member == name)
                                })
                                .map(|(_, value)| value)
                                .filter(|value| *value >= 0)
                        {
                            return value.to_string();
                        }
                        if side.is_constant() {
                            return self.expr(side, op.precedence() + 1);
                        }
                        let wide =
                            matches!(self.type_of(side), Some(TypeSig::Int64 | TypeSig::UInt64));
                        let already = matches!(
                            self.type_of(side),
                            Some(
                                TypeSig::UInt32
                                    | TypeSig::UInt64
                                    | TypeSig::UIntPtr
                                    | TypeSig::Byte
                                    | TypeSig::UInt16
                                    | TypeSig::Pointer(_)
                            )
                        );
                        if already {
                            return self.expr(side, op.precedence() + 1);
                        }
                        format!(
                            "({}){}",
                            if wide { "ulong" } else { "uint" },
                            self.expr(side, UNARY)
                        )
                    };
                    return (
                        format!("{} {} {}", cast(left), op.text(), cast(right)),
                        precedence,
                    );
                }
                (plain(*op), precedence)
            }
            Expr::Assign(target, value) => {
                // `long x = (long)i;` converts by itself.
                let value = match value.as_ref() {
                    Expr::Cast(to, inner)
                        if matches!(
                            target.as_ref(),
                            Expr::Local(_) | Expr::Arg(_) | Expr::Field { .. }
                        ) && self.type_of(target).as_ref() == Some(to)
                            && self.type_of(inner).is_some_and(|from| {
                                crate::simplify::implicit_numeric(&from, to)
                            }) =>
                    {
                        inner.as_ref()
                    }
                    other => other,
                };
                (
                    format!("{} = {}", self.expr(target, 2), self.expr(value, 1)),
                    1,
                )
            }
            Expr::Compound(op, target, value) => (
                format!(
                    "{} {}= {}",
                    self.expr(target, 2),
                    op.text(),
                    self.expr(value, 1)
                ),
                1,
            ),
            Expr::Increment {
                target,
                delta,
                postfix,
            } => {
                let sign = if *delta > 0 { "++" } else { "--" };
                if *postfix {
                    (format!("{}{sign}", self.expr(target, PRIMARY)), PRIMARY)
                } else {
                    (format!("{sign}{}", self.expr(target, UNARY)), UNARY)
                }
            }
            Expr::Call {
                method,
                receiver,
                args,
            } => {
                // A delegate's `Invoke` is the call syntax itself.
                if method.name == "Invoke"
                    && let Some(receiver) = receiver
                    && self.ctx.resolver.is_delegate(&method.declaring)
                {
                    let callee = self.expr(receiver, PRIMARY);
                    let arguments =
                        self.arguments(args, &method.sig.parameters, &method.out_params);
                    // `handler?(x)` is not C#: behind `?` the call keeps its name.
                    let text = if callee.ends_with('?') {
                        format!("{callee}.Invoke({arguments})")
                    } else {
                        format!("{callee}({arguments})")
                    };
                    return (text, PRIMARY);
                }
                // An extension method is called on its first argument.
                let extension = receiver.is_none() && !args.is_empty() && method.is_extension;
                let mut text = if extension {
                    let first = match &args[0] {
                        Expr::Unary(UnOp::AddressOf, inner) => inner.as_ref(),
                        other => other,
                    };
                    format!("{}.{}", self.receiver(first), method.name)
                } else {
                    self.member(receiver.as_deref(), &method.declaring, &method.name)
                };
                // Type arguments that the arguments pin down are left to
                // inference, the way the source would have.
                let call_args: &[Expr] = args;
                let inferable = method.type_args.iter().enumerate().all(|(at, _)| {
                    let at = at as u32;
                    // An `out var` says nothing of its type.
                    let givers: Vec<(&TypeSig, Option<TypeSig>)> = method
                        .sig
                        .parameters
                        .iter()
                        .zip(call_args)
                        .enumerate()
                        .filter(|(index, _)| method.out_params.get(*index) != Some(&true))
                        .map(|(_, pair)| pair)
                        // Nor does `null`.
                        .filter(|(_, arg)| !matches!(arg, Expr::Null))
                        .filter(|(param, _)| mentions_method_var(param, at))
                        .map(|(param, arg)| (param, self.type_of(arg)))
                        .collect();
                    // A lambda gives its type arguments only through what its
                    // body returns, which may be nothing: `null`.
                    let only_lambdas = method
                        .sig
                        .parameters
                        .iter()
                        .zip(call_args)
                        .filter(|(param, _)| mentions_method_var(param, at))
                        .all(|(_, arg)| match arg {
                            Expr::Lambda { body, .. } => !self.returns_typed(body),
                            _ => false,
                        });
                    if only_lambdas {
                        return false;
                    }
                    // `T` given twice, as values of different types: C#
                    // takes neither.
                    let direct: Vec<&Option<TypeSig>> = givers
                        .iter()
                        .filter(|(param, _)| **param == TypeSig::MVar(at))
                        .map(|(_, ty)| ty)
                        .collect();
                    if direct.len() > 1 && direct.iter().any(|ty| *ty != direct[0]) {
                        return false;
                    }
                    // A value of a narrower type than the argument IL gives
                    // would be inferred as that type.
                    if let Some(given) = method.type_args.get(at as usize)
                        && direct
                            .iter()
                            .any(|ty| ty.as_ref().is_some_and(|ty| ty != given))
                    {
                        return false;
                    }
                    // `Span<T>` given something that only converts to one:
                    // inference does not see through the conversion.
                    let converted = |param: &TypeSig, ty: &Option<TypeSig>| match (param, ty) {
                        (
                            TypeSig::Generic { definition, .. },
                            Some(TypeSig::Generic {
                                definition: given, ..
                            }),
                        ) => definition != given && self.ctx.resolver.is_value_type(param),
                        (TypeSig::Generic { .. }, Some(_)) => {
                            self.ctx.resolver.is_value_type(param)
                        }
                        _ => false,
                    };
                    !givers.is_empty() && !givers.iter().all(|(param, ty)| converted(param, ty))
                });
                // An anonymous type argument can only be inferred.
                let unnameable = method
                    .type_args
                    .iter()
                    .any(|ty| self.ctx.resolver.mentions_anonymous(ty));
                if !method.type_args.is_empty() && (!inferable || args.is_empty()) && !unnameable {
                    let names: Vec<String> = method
                        .type_args
                        .iter()
                        .map(|ty| self.type_name(ty))
                        .collect();
                    let _ = write!(text, "<{}>", names.join(", "));
                }
                text.push('(');
                let (params, outs, names): (&[TypeSig], &[bool], &[String]) = if extension {
                    (
                        &method.sig.parameters[1..],
                        method.out_params.get(1..).unwrap_or(&[]),
                        method.param_names.get(1..).unwrap_or(&[]),
                    )
                } else {
                    (
                        &method.sig.parameters,
                        &method.out_params,
                        &method.param_names,
                    )
                };
                let shown_args = if extension { &args[1..] } else { &args[..] };
                text.push_str(&self.arguments_named(
                    shown_args,
                    params,
                    outs,
                    names,
                    Some((method, usize::from(extension))),
                ));
                text.push(')');
                (text, PRIMARY)
            }
            // `new { a = x, b }`: an anonymous type, by its properties.
            Expr::New { ctor, args, .. }
                if self
                    .ctx
                    .resolver
                    .anonymous_type_row(&ctor.declaring)
                    .is_some_and(|row| {
                        self.ctx.resolver.anonymous_members(row).len() == args.len()
                    }) =>
            {
                let row = self
                    .ctx
                    .resolver
                    .anonymous_type_row(&ctor.declaring)
                    .unwrap_or(0);
                let members = self.ctx.resolver.anonymous_members(row);
                if members.is_empty() {
                    return ("new { }".to_string(), PRIMARY);
                }
                let parts: Vec<String> = members
                    .iter()
                    .zip(args)
                    .map(|(member, arg)| {
                        let value = self.expr(arg, 1);
                        // `x` given as `x` is the projection initializer.
                        let named = |text: &str| {
                            text == member
                                || text
                                    .rsplit_once('.')
                                    .is_some_and(|(_, last)| last == member)
                        };
                        if named(&value) {
                            value
                        } else {
                            format!("{member} = {value}")
                        }
                    })
                    .collect();
                (format!("new {{ {} }}", parts.join(", ")), PRIMARY)
            }
            Expr::New {
                ctor,
                args,
                initializer,
            } => {
                let mut text = format!("new {}", self.type_name(&ctor.declaring));
                if !args.is_empty() || initializer.is_empty() {
                    text.push('(');
                    text.push_str(&self.arguments_named(
                        args,
                        &ctor.sig.parameters,
                        &ctor.out_params,
                        &ctor.param_names,
                        Some((ctor, 0)),
                    ));
                    text.push(')');
                }
                if !initializer.is_empty() {
                    let _ = write!(text, " {}", self.initializer(initializer));
                }
                (text, PRIMARY)
            }
            Expr::NewOf(ty) => (format!("new {}()", self.type_name(ty)), PRIMARY),
            Expr::With {
                source,
                initializer,
            } => (
                format!(
                    "{} with {}",
                    self.expr(source, 11),
                    self.initializer(initializer)
                ),
                10,
            ),
            Expr::NewArray {
                element,
                size,
                items,
            } => match items {
                // `new T[2, 3] { { a, b, c }, { d, e, f } }`.
                Some(items)
                    if array_lengths(size).is_some_and(|lengths| {
                        lengths.iter().product::<usize>() == items.len()
                    }) =>
                {
                    let lengths = array_lengths(size).unwrap_or_default();
                    let dimensions = lengths
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ");
                    (
                        format!(
                            "{} {}",
                            self.array_creation(element, &dimensions),
                            self.nested_items(items, &lengths)
                        ),
                        PRIMARY,
                    )
                }
                // An array of an anonymous type is only ever implicitly typed.
                Some(items)
                    if !items.is_empty() && self.ctx.resolver.mentions_anonymous(element) =>
                {
                    let texts: Vec<String> = items.iter().map(|item| self.expr(item, 1)).collect();
                    (format!("new[] {{ {} }}", texts.join(", ")), PRIMARY)
                }
                Some(items) => {
                    let texts: Vec<String> = items.iter().map(|item| self.expr(item, 1)).collect();
                    (
                        format!(
                            "{} {{ {} }}",
                            self.array_creation(element, &items.len().to_string()),
                            texts.join(", ")
                        ),
                        PRIMARY,
                    )
                }
                None => {
                    // A multi-dimensional array has one size per rank.
                    let dimensions = match size.as_ref() {
                        Expr::Tuple(sizes) => sizes
                            .iter()
                            .map(|size| self.expr(size, 0))
                            .collect::<Vec<_>>()
                            .join(", "),
                        other => self.expr(other, 0),
                    };
                    (self.array_creation(element, &dimensions), PRIMARY)
                }
            },
            Expr::Field { receiver, field } => (
                self.member(
                    receiver.as_deref(),
                    &field.declaring,
                    primary_parameter_name(&field.name),
                ),
                PRIMARY,
            ),
            Expr::Property {
                receiver,
                declaring,
                name,
                ..
            } => (self.member(receiver.as_deref(), declaring, name), PRIMARY),
            Expr::Index { array, indices } => {
                // `a[a.Length - 1]` is `a[^1]`.
                let from_end = |index: &Expr| -> Option<String> {
                    if let Expr::Binary(BinOp::Sub, left, right) = index
                        && let Expr::Length(measured) = left.as_ref()
                        && measured == array
                        && array.is_place()
                        && let Expr::Int(n) = right.as_ref()
                        && *n > 0
                    {
                        return Some(format!("^{n}"));
                    }
                    None
                };
                let texts: Vec<String> = indices
                    .iter()
                    .map(|index| from_end(index).unwrap_or_else(|| self.expr(index, 0)))
                    .collect();
                (
                    format!("{}[{}]", self.expr(array, PRIMARY), texts.join(", ")),
                    PRIMARY,
                )
            }
            Expr::Indexer { receiver, args } => {
                let texts: Vec<String> = args.iter().map(|arg| self.expr(arg, 0)).collect();
                (
                    format!("{}[{}]", self.receiver(receiver), texts.join(", ")),
                    PRIMARY,
                )
            }
            Expr::Length(array) => (format!("{}.Length", self.expr(array, PRIMARY)), PRIMARY),
            // `(int)(-x)`: what a cast applies to is bracketed unless it is
            // primary, or itself a cast.
            // Constant arithmetic out of the type's range: a compile-time
            // error unless said to wrap.
            Expr::Cast(ty, inner)
                if matches!(inner.as_ref(), Expr::Binary(..) | Expr::Unary(..))
                    && constant_value(inner)
                        .zip(integral_range(ty))
                        .is_some_and(|(value, (low, high))| value < low || value > high) =>
            {
                (
                    format!(
                        "unchecked(({}){})",
                        self.type_name(ty),
                        self.expr(inner, PRIMARY)
                    ),
                    PRIMARY,
                )
            }
            // A negative constant made unsigned: C# wants it said.
            Expr::Cast(
                ty @ (TypeSig::Byte
                | TypeSig::UInt16
                | TypeSig::UInt32
                | TypeSig::UInt64
                | TypeSig::UIntPtr),
                inner,
            ) if matches!(negative_constant(inner), Some(Expr::Int(n) | Expr::Long(n)) if *n < 0) =>
            {
                let name = self.type_name(ty);
                // `(nuint)(nint)(-16)`: the widening says nothing more.
                let inner = negative_constant(inner).unwrap_or(inner);
                if matches!(inner, Expr::Int(-1) | Expr::Long(-1)) {
                    return (format!("{name}.MaxValue"), PRIMARY);
                }
                (
                    format!("unchecked(({name}){})", self.expr(inner, PRIMARY)),
                    PRIMARY,
                )
            }
            // A negative constant made an enum over an unsigned type is the
            // unsigned value of the same bits.
            Expr::Cast(ty, inner)
                if matches!(inner.as_ref(), Expr::Int(n) | Expr::Long(n) if *n < 0)
                    && matches!(
                        self.ctx.resolver.enum_underlying(ty),
                        Some(TypeSig::UInt64 | TypeSig::UInt32)
                    ) =>
            {
                let (Expr::Int(n) | Expr::Long(n)) = inner.as_ref() else {
                    unreachable!()
                };
                let value = if self.ctx.resolver.enum_underlying(ty) == Some(TypeSig::UInt32) {
                    u64::from(*n as u32)
                } else {
                    *n as u64
                };
                (format!("({}){value}", self.type_name(ty)), UNARY)
            }
            // A constant, or a constant cast, out of the range of the type it
            // is cast to: `(int)2147483648L` and `(sbyte)(byte)255` are
            // compile-time errors (CS0221) unless said to wrap.
            Expr::Cast(ty, inner)
                if (matches!(
                    inner.as_ref(),
                    Expr::Int(_) | Expr::Long(_) | Expr::Cast(..)
                ) && constant_value(inner)
                    .zip(integral_range(ty))
                    .is_some_and(|(value, (low, high))| value < low || value > high))
                    // A floating constant is truncated, and has to land in
                    // the range too: `(byte)300.7` does not.
                    || matches!((inner.as_ref(), integral_range(ty)), (Expr::Float(value, _), Some((low, high)))
                        if !value.trunc().is_finite()
                            || value.trunc() < low as f64
                            || value.trunc() > high as f64) =>
            {
                (
                    format!(
                        "unchecked(({}){})",
                        self.type_name(ty),
                        self.expr(inner, UNARY)
                    ),
                    PRIMARY,
                )
            }
            // `(T*)(nint)&x` is `&x` when `x` is a `T`, `(T*)(&x)` if not.
            Expr::Cast(TypeSig::Pointer(pointee), inner)
                if matches!(inner.as_ref(), Expr::Cast(TypeSig::IntPtr | TypeSig::UIntPtr, address)
                    if matches!(address.as_ref(), Expr::Unary(UnOp::AddressOf, _))) =>
            {
                let Expr::Cast(_, address) = inner.as_ref() else {
                    unreachable!()
                };
                let Expr::Unary(_, place) = address.as_ref() else {
                    unreachable!()
                };
                let text = format!("&{}", self.expr(place, UNARY));
                if self.type_of(place).as_ref() == Some(pointee.as_ref()) {
                    (text, UNARY)
                } else {
                    (format!("({}*)({text})", self.type_name(pointee)), UNARY)
                }
            }
            // `(nint)&x`: an address made a number is a pointer's.
            Expr::Cast(ty @ (TypeSig::IntPtr | TypeSig::UIntPtr | TypeSig::Pointer(_)), inner)
                if matches!(inner.as_ref(), Expr::Unary(UnOp::AddressOf, _)) =>
            {
                let Expr::Unary(_, place) = inner.as_ref() else {
                    unreachable!()
                };
                (
                    format!("({})(&{})", self.type_name(ty), self.expr(place, UNARY)),
                    UNARY,
                )
            }
            // A non-negative constant made unsigned is a literal of it.
            Expr::Cast(TypeSig::UInt64, inner) if matches!(inner.as_ref(), Expr::Int(n) | Expr::Long(n) if *n >= 0) =>
            {
                let (Expr::Int(n) | Expr::Long(n)) = inner.as_ref() else {
                    unreachable!()
                };
                (format!("{n}UL"), PRIMARY)
            }
            // `(T)null` is no C# for an unconstrained `T`: through `object`,
            // as IL unboxes it.
            Expr::Cast(ty @ (TypeSig::Var(_) | TypeSig::MVar(_)), inner)
                if matches!(inner.as_ref(), Expr::Null) =>
            {
                (format!("({})(object)null", self.type_name(ty)), UNARY)
            }
            Expr::Cast(ty, inner) => {
                let need = if matches!(inner.as_ref(), Expr::Cast(..)) {
                    UNARY
                } else {
                    PRIMARY
                };
                // A type parameter converts to and from other types only
                // through `object` (or an interface): `(T)(object)b`.
                let generic = |t: &TypeSig| match t {
                    TypeSig::Var(_) | TypeSig::MVar(_) => true,
                    TypeSig::Vector(element) => {
                        matches!(element.as_ref(), TypeSig::Var(_) | TypeSig::MVar(_))
                    }
                    _ => false,
                };
                // `C<T>` to `C<int>` too.
                // `C<T>` to `C<int>`, and a class to one made of type
                // parameters, `(Frozen<TKey>)new IntFrozen()`.
                let reinstantiated = |from: &TypeSig, to: &TypeSig| {
                    let same = matches!((from, to), (
                        TypeSig::Generic { definition: x, .. },
                        TypeSig::Generic { definition: y, .. },
                    ) if x == y);
                    (same && (mentions_type_parameter(from) || mentions_type_parameter(to)))
                        || (matches!(to, TypeSig::Generic { .. })
                            && mentions_type_parameter(to)
                            && !mentions_type_parameter(from)
                            && matches!(from, TypeSig::Generic { .. } | TypeSig::Class(_))
                            && !self.ctx.resolver.is_interface(from)
                            && !self.ctx.resolver.is_interface(to)
                            && !self.ctx.resolver.is_value_type(from))
                };
                let concrete = |t: &TypeSig| {
                    !generic(t)
                        && !matches!(t, TypeSig::Object)
                        && !self.ctx.resolver.is_interface(t)
                };
                let is_enum = |t: &TypeSig| self.ctx.resolver.enum_underlying(t).is_some();
                let through_object = self.type_of(inner).is_some_and(|from| {
                    from != *ty
                        && !is_enum(&from)
                        && !is_enum(ty)
                        && ((generic(ty) && concrete(&from))
                            // `T[]` to `Span<T>` is the span's own conversion.
                            || (generic(&from)
                                && concrete(ty)
                                && !(matches!(from, TypeSig::Vector(_))
                                    && self.ctx.resolver.is_value_type(ty)))
                            || (generic(ty) && generic(&from))
                            || reinstantiated(&from, ty))
                });
                if through_object {
                    return (
                        format!(
                            "({})(object){}",
                            self.type_name(ty),
                            self.expr(inner, PRIMARY)
                        ),
                        UNARY,
                    );
                }
                (
                    format!("({}){}", self.type_name(ty), self.expr(inner, need)),
                    UNARY,
                )
            }
            Expr::OperatorCast(ty, inner) => (
                format!("({}){}", self.type_name(ty), self.expr(inner, PRIMARY)),
                UNARY,
            ),
            Expr::CheckedCast(ty, inner) => (
                format!(
                    "checked(({}){})",
                    self.type_name(ty),
                    self.expr(inner, PRIMARY)
                ),
                PRIMARY,
            ),
            // Few know where `is` and `as` bind: their operand is bracketed
            // unless primary.
            // `as` on a value type only exists as `as T?`.
            Expr::As(ty, inner) => (
                format!(
                    "{} as {}{}",
                    self.expr(inner, PRIMARY),
                    self.type_name(ty),
                    if self.ctx.resolver.is_value_type(ty) && !self.ctx.resolver.is_nullable(ty) {
                        "?"
                    } else {
                        ""
                    }
                ),
                10,
            ),
            Expr::Is(ty, inner) => (
                format!("{} is {}", self.expr(inner, PRIMARY), self.type_name(ty)),
                10,
            ),
            Expr::IsPattern(ty, inner, target) => (
                format!(
                    "{} is {} {}",
                    self.expr(inner, 10),
                    self.type_name(ty),
                    self.expr(target, PRIMARY)
                ),
                10,
            ),
            Expr::Box(_, inner) => self.expr_inner(inner),
            // The precedence of `?:` confuses; each part that is not primary
            // is bracketed, the way readers expect.
            Expr::Conditional(condition, a, b) => {
                // `c ? ref a : ref b`, a conditional of references.
                // `c ? new Index(…) : null` is an `Index?` taken apart: the
                // `null` says so, `(Index?)null`, or it would be a
                // `default(Index)` or no C# at all.
                let lifted_null = |other: &Expr| {
                    self.type_of(other)
                        .filter(|ty| {
                            matches!(ty, TypeSig::ValueType(_) | TypeSig::Generic { .. })
                                && !self.ctx.resolver.is_nullable(ty)
                                && self.ctx.resolver.is_value_type(ty)
                        })
                        .map(|ty| format!("({}?)null", self.type_name(&ty)))
                };
                let branch = |value: &Expr, other: &Expr| match value {
                    Expr::Unary(UnOp::AddressOf, inner) => {
                        format!("ref {}", self.expr(inner, PRIMARY))
                    }
                    Expr::Null => lifted_null(other).unwrap_or_else(|| self.expr(value, PRIMARY)),
                    other => self.expr(other, PRIMARY),
                };
                (
                    format!(
                        "{} ? {} : {}",
                        self.expr(condition, PRIMARY),
                        branch(a, b),
                        branch(b, a)
                    ),
                    2,
                )
            }
            Expr::Delegate { target, method, .. } => {
                // A generic method group names its type arguments: nothing
                // is there to infer them from.
                let mut text = self.member(target.as_deref(), &method.declaring, &method.name);
                if !method.type_args.is_empty() {
                    let names: Vec<String> = method
                        .type_args
                        .iter()
                        .map(|ty| self.type_name(ty))
                        .collect();
                    let _ = write!(text, "<{}>", names.join(", "));
                }
                (text, PRIMARY)
            }
            Expr::FunctionPointer(method) => (format!("&{}", method.name), UNARY),
            Expr::Await(inner) => (format!("await {}", self.expr(inner, UNARY)), UNARY),
            Expr::Tuple(items) => {
                let texts: Vec<String> = items.iter().map(|item| self.expr(item, 0)).collect();
                (format!("({})", texts.join(", ")), PRIMARY)
            }
            Expr::Interpolated(parts) => {
                let mut text = String::from("$\"");
                for part in parts {
                    match part {
                        Interpolation::Text(literal) => {
                            text.push_str(&escape(literal).replace('{', "{{").replace('}', "}}"));
                        }
                        Interpolation::Hole(hole, spec) => {
                            text.push('{');
                            let hole_text = self.expr(hole, 3);
                            if hole_text.contains(':') && !hole_text.starts_with('(') {
                                text.push('(');
                                text.push_str(&hole_text);
                                text.push(')');
                            } else {
                                text.push_str(&hole_text);
                            }
                            if let Some(spec) = spec {
                                if !spec.starts_with(':') && !spec.starts_with(',') {
                                    text.push(',');
                                }
                                text.push_str(spec);
                            }
                            text.push('}');
                        }
                    }
                }
                text.push('"');
                (text, PRIMARY)
            }
            Expr::Lambda {
                id,
                params,
                outs,
                body,
            } => {
                // A parameter of an anonymous type cannot be written: all
                // are left to inference.
                let implicit = params.iter().any(|param| {
                    self.var_types
                        .get(&Var::Local(*param))
                        .is_some_and(|ty| self.ctx.resolver.mentions_anonymous(ty))
                }) && !outs.iter().any(|out| *out);
                let names: Vec<String> = params
                    .iter()
                    .enumerate()
                    .map(|(at, param)| {
                        let var = Var::Local(*param);
                        if implicit {
                            return self.var_name(var);
                        }
                        if outs.get(at) == Some(&true)
                            && let Some(TypeSig::ByRef(inner)) = self.var_types.get(&var)
                        {
                            return format!("out {} {}", self.type_name(inner), self.var_name(var));
                        }
                        format!("{} {}", self.var_type(var), self.var_name(var))
                    })
                    .collect();
                // An `await` of its own, outside the lambdas nested in it,
                // makes it `async`.
                let mut own = (**body).clone();
                let mut awaits = false;
                let mut strip = |e: &mut Expr| {
                    if matches!(e, Expr::Lambda { .. }) {
                        *e = Expr::Null;
                    }
                };
                let mut seen = |e: &Expr| awaits |= matches!(e, Expr::Await(_));
                match &mut own {
                    Body::Expr(expr) => {
                        expr.map(&mut strip);
                        expr.walk(&mut seen);
                    }
                    Body::Block(stmts) => {
                        for stmt in stmts.iter_mut() {
                            stmt.map_exprs(&mut strip);
                        }
                        for stmt in stmts.iter() {
                            stmt.walk_exprs(&mut seen);
                        }
                    }
                }
                let prefix = if awaits { "async " } else { "" };
                let header = format!("{prefix}({})", names.join(", "));
                match body.as_ref() {
                    Body::Expr(expr) => (format!("{header} => {}", self.expr(expr, 1)), 1),
                    Body::Block(stmts) => {
                        // The block is printed by a copy of this printer at
                        // the next indentation, under the lambda's own path.
                        let mut nested = self.clone();
                        nested.out = String::new();
                        nested.indent = self.indent;
                        let mut path = self.current_path.clone();
                        path.push(LAMBDA_PATH_BASE + *id as usize);
                        nested.line("{");
                        nested.indent += 1;
                        nested.block_contents(stmts, &mut path);
                        nested.indent -= 1;
                        for _ in 0..nested.indent {
                            nested.out.push('\t');
                        }
                        nested.out.push('}');
                        (format!("{header} =>\n{}", nested.out), 1)
                    }
                }
            }
            Expr::Checked(inner) => (format!("checked({})", self.expr(inner, 0)), PRIMARY),
            Expr::MaybeNull(inner) => (format!("{}?", self.expr(inner, PRIMARY)), PRIMARY),
            Expr::StackAlloc(ty, size) => {
                // The count is an `int`: the unsigned conversion the
                // allocation's size went through is IL's.
                let count = match size.as_ref() {
                    Expr::Cast(TypeSig::UInt32 | TypeSig::UIntPtr, inner) => inner.as_ref(),
                    other => other,
                };
                (
                    format!("stackalloc {}[{}]", self.type_name(ty), self.expr(count, 0)),
                    UNARY,
                )
            }
            Expr::Raw(text) => (text.clone(), PRIMARY),
        }
    }

    /// `receiver.Name`, with `this.` and the type's own name left out where
    /// C# would leave them out.
    fn member(&self, receiver: Option<&Expr>, declaring: &TypeSig, name: &str) -> String {
        let name = &*crate::names::identifier(name);
        let shadowed = self.param_names.iter().any(|p| p == name)
            || self.var_names.values().any(|v| v == name);
        match receiver {
            Some(Expr::This) if !shadowed => name.to_string(),
            Some(Expr::Base) => format!("base.{name}"),
            // A member reached through a pointer.
            Some(receiver)
                if !matches!(receiver, Expr::Unary(UnOp::AddressOf, _))
                    && matches!(self.type_of(receiver), Some(TypeSig::Pointer(_))) =>
            {
                format!("{}->{name}", self.expr(receiver, 15))
            }
            Some(receiver) => format!("{}.{name}", self.receiver(receiver)),
            // A function of a display class reached by no receiver is a
            // local function, in scope by its name.
            None if !shadowed
                && crate::closures::display_row(self.ctx.resolver, declaring).is_some() =>
            {
                name.to_string()
            }
            None if (self.is_own_type(declaring)
                || (self.is_enclosing_type(declaring)
                    && !self.ctx.resolver.has_member_named(self.own_type(), name)))
                && !shadowed =>
            {
                name.to_string()
            }
            None => {
                let shown = self.type_name(declaring);
                // `Buffer.BlockCopy` in a class with a `Buffer` property
                // would be the property's.
                let head = shown.split(['<', '.']).next().unwrap_or(&shown);
                if !head.is_empty()
                    && !self.is_own_type(declaring)
                    && !self.is_enclosing_type(declaring)
                    && self.ctx.resolver.has_member_named(self.own_type(), head)
                {
                    let full = self
                        .ctx
                        .resolver
                        .qualified()
                        .type_name(declaring, &self.generics());
                    return format!("{full}.{name}");
                }
                format!("{shown}.{name}")
            }
        }
    }

    /// The items of a multi-dimensional array, braced by rank.
    fn nested_items(&self, items: &[Expr], lengths: &[usize]) -> String {
        let texts: Vec<String> = match lengths {
            [] | [_] => items.iter().map(|item| self.expr(item, 1)).collect(),
            [_, inner @ ..] => {
                let row = inner.iter().product::<usize>().max(1);
                items
                    .chunks(row)
                    .map(|chunk| self.nested_items(chunk, inner))
                    .collect()
            }
        };
        format!("{{ {} }}", texts.join(", "))
    }

    /// Whether every value a lambda's body returns has a type to infer
    /// from, `null` having none.
    fn returns_typed(&self, body: &Body) -> bool {
        fn returns<'e>(stmts: &'e [Stmt], out: &mut Vec<Option<&'e Expr>>) {
            for stmt in stmts {
                match stmt {
                    Stmt::Return(value) => out.push(value.as_ref()),
                    Stmt::LocalFunction { .. } => {}
                    other => {
                        for block in other.blocks() {
                            returns(block, out);
                        }
                    }
                }
            }
        }
        match body {
            Body::Expr(value) => {
                !matches!(value.as_ref(), Expr::Null) && self.type_of(value).is_some()
            }
            Body::Block(stmts) => {
                let mut values = Vec::new();
                returns(stmts, &mut values);
                values.iter().all(|value| match value {
                    Some(Expr::Null) => false,
                    Some(value) => self.type_of(value).is_some(),
                    None => true,
                })
            }
        }
    }

    /// A receiver: a value type reached by address is spelled as itself.
    fn receiver(&self, receiver: &Expr) -> String {
        match receiver {
            // A method group is no value to call a member on: the delegate
            // made of it is.
            Expr::Delegate { ty, .. } => {
                format!("new {}({})", self.type_name(ty), self.expr(receiver, 0))
            }
            Expr::Unary(UnOp::AddressOf, inner) => self.expr(inner, 15),
            Expr::MaybeNull(inner) => match inner.as_ref() {
                // A struct reached by address, `x?.Y` of a `Nullable`.
                Expr::Unary(UnOp::AddressOf, place) => format!("{}?", self.expr(place, 15)),
                other => format!("{}?", self.expr(other, 15)),
            },
            other => self.expr(other, 15),
        }
    }

    /// Whether the printed name of a type is that of the type being printed
    /// or one enclosing it.
    #[allow(dead_code)]
    fn names_own_type(&self, name: &str) -> bool {
        self.own_type_names.iter().any(|own| own == name)
    }

    /// One side of a binary operator: a `long` literal beside a `long`
    /// operand drops its `L`, the way it was written.
    fn operand(&self, side: &Expr, other: &Expr, need: u8) -> String {
        // Only beside a 64-bit value: `1L << n` is no `1 << n`, nor is
        // `x + 1L` with `x` an `int`.
        if let Expr::Long(n) = side
            && !other.is_constant()
            && i32::try_from(*n).is_ok()
            && matches!(
                self.type_of(other).map(|ty| match ty {
                    TypeSig::ByRef(inner) => *inner,
                    other => other,
                }),
                Some(TypeSig::Int64 | TypeSig::UInt64)
            )
        {
            return n.to_string();
        }
        self.expr(side, need)
    }

    /// A value assigned to a variable, with the literal suffix its type
    /// asks for: `0u` for a `uint`.
    /// The value stored into a variable, or the reference a `ref` variable
    /// is bound to where it is declared (or given another one).
    fn bound(&self, var: Var, value: &Expr, declaring: bool) -> String {
        // A reference is a variable, a call or an element; `r & x` is the
        // value stored through `r`.
        let a_reference = matches!(
            value,
            Expr::Local(_)
                | Expr::Arg(_)
                | Expr::Call { .. }
                | Expr::Index { .. }
                | Expr::Field { .. }
        ) && matches!(self.type_of(value), Some(TypeSig::ByRef(_)));
        if matches!(self.var_types.get(&var), Some(TypeSig::ByRef(_)))
            && !matches!(value, Expr::Unary(UnOp::AddressOf, _))
            && (declaring || a_reference)
        {
            return format!("ref {}", self.expr(value, 14));
        }
        self.assigned(var, value, 3)
    }

    fn assigned(&self, var: Var, value: &Expr, need: u8) -> String {
        if let Expr::Int(n) = value
            && *n >= 0
        {
            match self.var_types.get(&var) {
                Some(TypeSig::UInt32) => return format!("{n}u"),
                Some(TypeSig::UInt64) => return format!("{n}uL"),
                _ => {}
            }
        }
        // `long x = (long)i;` converts by itself.
        let value = match value {
            Expr::Cast(to, inner)
                if self.var_types.get(&var) == Some(to)
                    && self
                        .type_of(inner)
                        .is_some_and(|from| crate::simplify::implicit_numeric(&from, to)) =>
            {
                inner.as_ref()
            }
            other => other,
        };
        // A lambda binds loosest of all, and is never bracketed here.
        let need = if matches!(value, Expr::Lambda { .. }) {
            0
        } else {
            need
        };
        self.expr(value, need)
    }

    fn arguments(&self, args: &[Expr], params: &[TypeSig], outs: &[bool]) -> String {
        self.arguments_named(args, params, outs, &[], None)
    }

    /// Arguments, with a bare `true`/`false` labelled by its parameter's
    /// name where the name is known: `GetCount(onlyIfCheap: true)`, and a
    /// `null` cast to its parameter's type where another overload could
    /// take it: `Max((IComparer<int>?)null)`. `method` is the callee and
    /// how many leading parameters the shown arguments skip.
    fn arguments_named(
        &self,
        args: &[Expr],
        params: &[TypeSig],
        outs: &[bool],
        names: &[String],
        method: Option<(&MethodRef, usize)>,
    ) -> String {
        let texts: Vec<String> = args
            .iter()
            .enumerate()
            .map(|(index, arg)| match arg {
                Expr::Bool(_) if names.get(index).is_some_and(|name| !name.is_empty()) => {
                    let name = &names[index];
                    let name = if is_keyword(name) {
                        format!("@{name}")
                    } else {
                        name.clone()
                    };
                    format!("{name}: {}", self.expr(arg, 1))
                }
                Expr::Null => {
                    let cast = method.and_then(|(method, skipped)| {
                        self.ctx
                            .resolver
                            .null_cast_for(method, index + skipped)
                            .map(|(ty, nullable)| (method, ty, nullable))
                    });
                    match cast {
                        Some((method, ty, nullable)) => {
                            let ty =
                                crate::stack::substitute(&ty, &method.declaring, &method.type_args);
                            let mark = if nullable { "?" } else { "" };
                            format!("({}{mark})null", self.type_name(&ty))
                        }
                        None => "null".to_string(),
                    }
                }
                Expr::Unary(UnOp::AddressOf, inner) => {
                    let by_ref = matches!(params.get(index), Some(TypeSig::ByRef(_)));
                    if !by_ref {
                        return self.expr(inner, 0);
                    }
                    let is_out = outs.get(index).copied().unwrap_or(false);
                    if is_out
                        && let Some(var) = var_of(inner)
                        && self.discards.contains(&var)
                    {
                        return format!("out {} _", self.var_type(var));
                    }
                    if is_out
                        && let Some(var) = var_of(inner)
                        && self
                            .inline_declarations
                            .contains(&(self.current_path.clone(), var))
                        && self
                            .declared_inline
                            .borrow_mut()
                            .insert((self.current_path.clone(), var))
                    {
                        // Where another overload could take the argument,
                        // its type says which.
                        if method.is_some_and(|(method, _)| self.ctx.resolver.is_overloaded(method))
                        {
                            return format!("out {} {}", self.var_type(var), self.expr(inner, 0));
                        }
                        return format!("out var {}", self.expr(inner, 0));
                    }
                    // An `in` parameter takes the variable as it is.
                    let is_in = method.is_some_and(|(method, skipped)| {
                        method
                            .sig
                            .parameters_required
                            .get(index + skipped)
                            .is_some_and(|required| {
                                required.iter().any(|token| {
                                    self.ctx.resolver.raw_name(*token).as_deref()
                                        == Some("System.Runtime.InteropServices.InAttribute")
                                })
                            })
                            || self.ctx.resolver.param_is_in(method, index + skipped)
                    });
                    if is_in {
                        // Unless another overload takes it by value: then
                        // `M(x)` is that one, and `in` is what says this.
                        if method.is_some_and(|(method, _)| self.ctx.resolver.has_overloads(method))
                        {
                            return format!("in {}", self.expr(inner, 0));
                        }
                        return self.expr(inner, 0);
                    }
                    let keyword = if is_out { "out" } else { "ref" };
                    // A pointer given for a reference is what it points at.
                    if let Some(TypeSig::ByRef(wanted)) = params.get(index)
                        && !matches!(wanted.as_ref(), TypeSig::Pointer(_))
                        && matches!(self.type_of(inner), Some(TypeSig::Pointer(_)))
                    {
                        return format!("{keyword} *{}", self.expr(inner, 14));
                    }
                    format!("{keyword} {}", self.expr(inner, 0))
                }
                other => self.expr(other, 1),
            })
            .collect();
        texts.join(", ")
    }
}

/// Whether a signature type mentions a method type parameter by position.
fn mentions_method_var(ty: &TypeSig, at: u32) -> bool {
    match ty {
        TypeSig::MVar(found) => *found == at,
        TypeSig::Vector(inner) | TypeSig::Pointer(inner) | TypeSig::ByRef(inner) => {
            mentions_method_var(inner, at)
        }
        TypeSig::Array { element, .. } => mentions_method_var(element, at),
        TypeSig::Generic { arguments, .. } => arguments
            .iter()
            .any(|argument| mentions_method_var(argument, at)),
        _ => false,
    }
}

/// Where the last `.` at the top level of a type name is: the split between
/// an enclosing type and the one nested in it.
fn split_enclosing(name: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut last = None;
    for (at, ch) in name.char_indices() {
        match ch {
            '<' | '[' | '(' => depth += 1,
            '>' | ']' | ')' => depth = depth.saturating_sub(1),
            '.' if depth == 0 => last = Some(at),
            _ => {}
        }
    }
    last
}

/// Whether C# takes an expression as a statement of its own.
fn is_statement_expression(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Call { .. }
            | Expr::Assign(..)
            | Expr::Compound(..)
            | Expr::Increment { .. }
            | Expr::New { .. }
            | Expr::NewOf(_)
            | Expr::Await(_)
            | Expr::Raw(_)
    )
}

/// The statement at a path of statement and block indices.
fn stmt_at<'s>(stmts: &'s [Stmt], path: &[usize]) -> Option<&'s Stmt> {
    let (&first, rest) = path.split_first()?;
    let stmt = stmts.get(first)?;
    match rest.split_first() {
        None => Some(stmt),
        Some((&block, deeper)) => {
            let blocks = stmt.blocks();
            stmt_at(blocks.get(block)?, deeper)
        }
    }
}

fn full_path(path: &[usize], sub: &[usize], block_index: usize) -> Vec<usize> {
    let mut full = path.to_vec();
    full.extend_from_slice(sub);
    full.push(block_index);
    full
}

/// One occurrence of a variable in a body.
#[derive(Clone, Debug)]
struct Reference {
    /// The path of the block the statement is in.
    block: Vec<usize>,
    /// The statement's index in that block.
    stmt: usize,
    /// Whether the statement is an assignment to the variable at this level.
    declaring: bool,
    /// Whether a construct (`foreach`, `using`, a pattern) declares it.
    binding: bool,
    /// Whether the reference is a `for` initialiser, which can declare it.
    header: bool,
    /// A name suggested by what is assigned.
    hint: Option<String>,
    /// A name suggested by where the value goes: the parameter it is
    /// passed as, `result` when it is returned.
    load_hint: Option<String>,
    /// Whether the reference is an `out` argument, which can declare the
    /// variable as `out var`.
    out_arg: bool,
    /// Whether the reference is the target of `++` or `+=`: neither a read
    /// that names the variable nor a store that does.
    compound: bool,
    /// Whether the reference is the receiver of a member access, which on
    /// a struct is by address, not a read of the value.
    receiver: bool,
}

fn var_of(expr: &Expr) -> Option<Var> {
    match expr {
        Expr::Local(at) => Some(Var::Local(*at)),
        Expr::Slot(id) => Some(Var::Slot(*id)),
        _ => None,
    }
}

fn collect_block(stmts: &[Stmt], path: &mut Vec<usize>, refs: &mut HashMap<Var, Vec<Reference>>) {
    for (index, stmt) in stmts.iter().enumerate() {
        collect_stmt(stmt, path, index, refs);
    }
}

fn collect_stmt(
    stmt: &Stmt,
    path: &mut Vec<usize>,
    index: usize,
    refs: &mut HashMap<Var, Vec<Reference>>,
) {
    fn note(
        refs: &mut HashMap<Var, Vec<Reference>>,
        index: usize,
        var: Var,
        declaring: bool,
        binding: bool,
        hint: Option<String>,
        path: &[usize],
    ) {
        refs.entry(var).or_default().push(Reference {
            block: path.to_vec(),
            stmt: index,
            declaring,
            binding,
            header: false,
            hint,
            load_hint: None,
            out_arg: false,
            compound: false,
            receiver: false,
        });
    }
    match stmt {
        Stmt::Return(Some(value)) if var_of(value).is_some() => {
            let var = var_of(value).unwrap_or(Var::Slot(u32::MAX));
            refs.entry(var).or_default().push(Reference {
                block: path.to_vec(),
                stmt: index,
                declaring: false,
                binding: false,
                header: false,
                hint: None,
                load_hint: Some("result".to_string()),
                out_arg: false,
                compound: false,
                receiver: false,
            });
            collect_expr(value, path, index, false, refs);
        }
        Stmt::Expr(Expr::Assign(target, value)) => {
            if let Some(var) = var_of(target) {
                note(refs, index, var, true, false, hint_of(value), path);
                collect_expr(value, path, index, false, refs);
            } else {
                collect_expr(target, path, index, false, refs);
                collect_expr(value, path, index, false, refs);
            }
        }
        Stmt::ForEach {
            local,
            source,
            body,
        } => {
            note(
                refs,
                index,
                Var::Local(*local),
                true,
                true,
                hint_of_source(source),
                path,
            );
            collect_expr(source, path, index, false, refs);
            path.push(index);
            path.push(0);
            collect_block(body, path, refs);
            path.pop();
            path.pop();
        }
        Stmt::Fixed { local, init, body } => {
            note(
                refs,
                index,
                Var::Local(*local),
                true,
                true,
                Some("ptr".to_string()),
                path,
            );
            collect_expr(init, path, index, false, refs);
            path.push(index);
            path.push(0);
            collect_block(body, path, refs);
            path.pop();
            path.pop();
        }
        Stmt::Using {
            local,
            resource,
            body,
        } => {
            if let Some(local) = local {
                note(
                    refs,
                    index,
                    Var::Local(*local),
                    true,
                    true,
                    hint_of(resource),
                    path,
                );
            }
            collect_expr(resource, path, index, false, refs);
            path.push(index);
            path.push(0);
            collect_block(body, path, refs);
            path.pop();
            path.pop();
        }
        Stmt::For {
            initializer,
            condition,
            step,
            body,
        } => {
            if let Some(Stmt::Expr(Expr::Assign(target, value))) = initializer.as_deref()
                && let Some(var) = var_of(target)
            {
                // A counter stepping up by one is an `i`.
                let counts = matches!(step.as_ref(), Some(Expr::Increment { target: stepped, delta: 1, .. }) if **stepped == **target);
                refs.entry(var).or_default().push(Reference {
                    block: path.to_vec(),
                    stmt: index,
                    declaring: true,
                    binding: false,
                    header: true,
                    hint: counts.then(|| "i".to_string()),
                    load_hint: None,
                    out_arg: false,
                    compound: false,
                    receiver: false,
                });
                collect_expr(value, path, index, false, refs);
            } else if let Some(initializer) = initializer {
                collect_stmt(initializer, path, index, refs);
            }
            collect_expr(condition, path, index, false, refs);
            if let Some(step) = step {
                collect_expr(step, path, index, false, refs);
            }
            path.push(index);
            path.push(0);
            collect_block(body, path, refs);
            path.pop();
            path.pop();
        }
        Stmt::LocalFunction { params, body, .. } => {
            path.push(index);
            path.push(0);
            for param in params {
                refs.entry(Var::Local(*param)).or_default().push(Reference {
                    block: path.clone(),
                    stmt: 0,
                    declaring: true,
                    binding: true,
                    header: false,
                    hint: None,
                    load_hint: None,
                    out_arg: false,
                    compound: false,
                    receiver: false,
                });
            }
            collect_block(body, path, refs);
            path.pop();
            path.pop();
        }
        Stmt::Try {
            body,
            catches,
            finally,
        } => {
            path.push(index);
            path.push(0);
            collect_block(body, path, refs);
            path.pop();
            for (at, catch) in catches.iter().enumerate() {
                if let Some(variable) = catch.variable {
                    path.pop();
                    note(
                        refs,
                        index,
                        Var::Local(variable),
                        true,
                        true,
                        Some("ex".into()),
                        path,
                    );
                    path.push(index);
                }
                if let Some(filter) = &catch.filter {
                    path.pop();
                    collect_expr(filter, path, index, false, refs);
                    path.push(index);
                }
                path.push(at + 1);
                collect_block(&catch.body, path, refs);
                path.pop();
            }
            if let Some(finally) = finally {
                path.push(catches.len() + 1);
                collect_block(finally, path, refs);
                path.pop();
            }
            path.pop();
        }
        other => {
            for expr in head_exprs(other) {
                collect_expr(expr, path, index, false, refs);
            }
            path.push(index);
            for (at, block) in other.blocks().iter().enumerate() {
                path.push(at);
                collect_block(block, path, refs);
                path.pop();
            }
            path.pop();
        }
    }
}

/// The paths of the `switch` statements, as `collect_block` numbers them.
fn switch_paths(
    stmts: &[Stmt],
    path: &mut Vec<usize>,
    out: &mut HashSet<Vec<usize>>,
    flat: &mut HashSet<Vec<usize>>,
) {
    for (index, stmt) in stmts.iter().enumerate() {
        path.push(index);
        if matches!(stmt, Stmt::Switch { .. }) {
            out.insert(path.clone());
        }
        // Written as `using var x = ...;`, as `block_contents` does.
        if index + 1 == stmts.len()
            && matches!(stmt, Stmt::Using { local: Some(_), body, .. } if !body.is_empty())
        {
            let mut body = path.clone();
            body.push(0);
            flat.insert(body);
        }
        for (at, block) in stmt.blocks().iter().enumerate() {
            path.push(at);
            switch_paths(block, path, out, flat);
            path.pop();
        }
        path.pop();
    }
}

fn head_exprs(stmt: &Stmt) -> Vec<&Expr> {
    match stmt {
        Stmt::Expr(expr) | Stmt::YieldReturn(expr) => vec![expr],
        Stmt::Declare {
            value: Some(value), ..
        }
        | Stmt::Return(Some(value))
        | Stmt::Throw(Some(value)) => vec![value],
        Stmt::If { condition, .. }
        | Stmt::While { condition, .. }
        | Stmt::DoWhile { condition, .. } => vec![condition],
        Stmt::Switch { value, .. } => vec![value],
        Stmt::Lock { target, .. } | Stmt::Fixed { init: target, .. } => vec![target],
        _ => Vec::new(),
    }
}

fn collect_expr(
    expr: &Expr,
    path: &mut Vec<usize>,
    index: usize,
    _declaring: bool,
    refs: &mut HashMap<Var, Vec<Reference>>,
) {
    // A lambda's body is a block of its own; its parameters are bound by it.
    if let Expr::Lambda {
        id, params, body, ..
    } = expr
        && *id != u32::MAX
    {
        path.push(index);
        path.push(LAMBDA_PATH_BASE + *id as usize);
        for param in params {
            refs.entry(Var::Local(*param)).or_default().push(Reference {
                block: path.clone(),
                stmt: 0,
                declaring: true,
                binding: true,
                header: false,
                hint: None,
                load_hint: None,
                out_arg: false,
                compound: false,
                receiver: false,
            });
        }
        match body.as_ref() {
            Body::Block(stmts) => collect_block(stmts, path, refs),
            Body::Expr(inner) => collect_expr(inner, path, 0, false, refs),
        }
        path.pop();
        path.pop();
        return;
    }
    let mut lambdas: Vec<Expr> = Vec::new();
    // The locals inside `out` arguments, which are written there, not read;
    // the targets of `++`/`+=`; the receivers of member accesses.
    let mut out_inners: Vec<*const Expr> = Vec::new();
    let mut compound_inners: Vec<*const Expr> = Vec::new();
    let mut receiver_inners: Vec<*const Expr> = Vec::new();
    expr.walk_shallow(&mut |e| {
        if let Expr::Lambda { id, .. } = e
            && *id != u32::MAX
            && !std::ptr::eq(e, expr)
        {
            lambdas.push(e.clone());
            return;
        }
        // A local passed as an `out` argument takes the parameter's name,
        // and may be declared right there; one passed by value is named
        // after the parameter when nothing else names it.
        let call = match e {
            Expr::Call { method, args, .. } => Some((method, args)),
            Expr::New { ctor, args, .. } => Some((ctor, args)),
            _ => None,
        };
        if let Some((method, args)) = call {
            // The one argument of a setter is named after the property.
            let setter = (args.len() == 1)
                .then(|| {
                    method
                        .name
                        .strip_prefix("set_")
                        .or_else(|| {
                            method
                                .name
                                .strip_prefix("Set")
                                .filter(|rest| rest.chars().next().is_some_and(char::is_uppercase))
                        })
                        .map(camel)
                })
                .flatten();
            for (at, arg) in args.iter().enumerate() {
                let name = setter.clone().or_else(|| {
                    method
                        .param_names
                        .get(at)
                        .filter(|name| !name.is_empty())
                        .map(|name| camel(name))
                });
                match arg {
                    Expr::Unary(UnOp::AddressOf, inner)
                        if method.out_params.get(at) == Some(&true) =>
                    {
                        if let Expr::Local(local) = inner.as_ref() {
                            out_inners.push(std::ptr::from_ref::<Expr>(inner));
                            refs.entry(Var::Local(*local)).or_default().push(Reference {
                                block: path.clone(),
                                stmt: index,
                                declaring: true,
                                binding: false,
                                header: false,
                                hint: name,
                                load_hint: None,
                                out_arg: true,
                                compound: false,
                                receiver: false,
                            });
                        }
                    }
                    Expr::Local(_) | Expr::Slot(_) if name.is_some() => {
                        let var = var_of(arg).unwrap_or(Var::Slot(u32::MAX));
                        refs.entry(var).or_default().push(Reference {
                            block: path.clone(),
                            stmt: index,
                            declaring: false,
                            binding: false,
                            header: false,
                            hint: None,
                            load_hint: name,
                            out_arg: false,
                            compound: false,
                            receiver: false,
                        });
                    }
                    _ => {}
                }
            }
            return;
        }
        if out_inners.iter().any(|inner| std::ptr::eq(*inner, e)) {
            // Noted with the call already, as a write.
            return;
        }
        // `x++`, `x += e`: the target is neither read nor stored for naming.
        if let Expr::Increment { target, .. } | Expr::Compound(_, target, _) = e
            && let Some(var) = var_of(target)
        {
            compound_inners.push(std::ptr::from_ref::<Expr>(target));
            refs.entry(var).or_default().push(Reference {
                block: path.clone(),
                stmt: index,
                declaring: false,
                binding: false,
                header: false,
                hint: None,
                load_hint: None,
                out_arg: false,
                compound: true,
                receiver: false,
            });
        }
        // What a value is stored into names it: a field, a property.
        if let Expr::Assign(target, value) = e
            && let Some(var) = var_of(value)
        {
            let name = match target.as_ref() {
                Expr::Field { field, .. } => Some(camel(
                    field.name.trim_start_matches("m_").trim_start_matches('_'),
                )),
                Expr::Property { name, .. } if name != "Item" => Some(camel(name)),
                _ => None,
            };
            if let Some(name) = name {
                refs.entry(var).or_default().push(Reference {
                    block: path.clone(),
                    stmt: index,
                    declaring: false,
                    binding: false,
                    header: false,
                    hint: None,
                    load_hint: Some(name),
                    out_arg: false,
                    compound: false,
                    receiver: false,
                });
            }
        }
        // The receiver of a member access: by address on a struct.
        match e {
            Expr::Property {
                receiver: Some(inner),
                ..
            }
            | Expr::Field {
                receiver: Some(inner),
                ..
            }
            | Expr::Call {
                receiver: Some(inner),
                ..
            } if var_of(inner).is_some() => {
                receiver_inners.push(std::ptr::from_ref::<Expr>(inner));
            }
            _ => {}
        }
        if compound_inners.iter().any(|inner| std::ptr::eq(*inner, e)) {
            return;
        }
        let is_receiver = receiver_inners.iter().any(|inner| std::ptr::eq(*inner, e));
        let (var, binding, hint) = match e {
            Expr::Local(at) => (Var::Local(*at), false, None),
            Expr::Slot(id) => (Var::Slot(*id), false, None),
            Expr::IsPattern(_, _, target) => match target.as_ref() {
                Expr::Local(at) => (Var::Local(*at), true, None),
                _ => return,
            },
            _ => return,
        };
        let entries = refs.entry(var).or_default();
        // The pattern's binding is noted once; the local inside it again as a
        // plain use is harmless but doubles the entry.
        if binding {
            entries.push(Reference {
                block: path.clone(),
                stmt: index,
                declaring: true,
                binding: true,
                header: false,
                hint,
                load_hint: None,
                out_arg: false,
                compound: false,
                receiver: false,
            });
            return;
        }
        if entries
            .last()
            .is_some_and(|r| r.binding && r.block == *path && r.stmt == index)
        {
            return;
        }
        entries.push(Reference {
            block: path.clone(),
            stmt: index,
            declaring: false,
            binding: false,
            header: false,
            hint,
            load_hint: None,
            out_arg: false,
            compound: false,
            receiver: is_receiver,
        });
    });
    // Nested lambdas are noted under their own blocks.
    for lambda in &lambdas {
        collect_expr(lambda, path, index, false, refs);
    }
}

/// A name suggested by an assigned value: the property or field it came
/// from, or the type that was constructed.
fn hint_of(value: &Expr) -> Option<String> {
    match value {
        Expr::Property { name, .. } if name != "Item" => Some(camel(name)),
        Expr::Field { field, .. } => Some(camel(
            field.name.trim_start_matches("m_").trim_start_matches('_'),
        )),
        Expr::Call { method, .. } => {
            let name = method.name.as_str();
            if let Some(rest) = name.strip_prefix("Get")
                && rest.chars().next().is_some_and(char::is_uppercase)
            {
                return Some(camel(rest));
            }
            None
        }
        _ => None,
    }
}

/// The name a `foreach` variable takes from its collection: `name` for
/// `names`, `item` otherwise. A parameter or local as the collection is
/// noted for [`Printer::name_all`] to look up once it knows their names.
fn hint_of_source(source: &Expr) -> Option<String> {
    let name = match source {
        Expr::Field { field, .. } => field.name.clone(),
        Expr::Property { name, .. } => name.clone(),
        Expr::Arg(at) => return Some(format!("{FOREACH_ARG}{at}")),
        Expr::Local(at) => return Some(format!("{FOREACH_LOCAL}{at}")),
        _ => return Some("item".to_string()),
    };
    Some(singular(&name).unwrap_or_else(|| "item".to_string()))
}

/// `<name>P`, the field a captured primary-constructor parameter becomes,
/// reads as the parameter.
#[must_use]
pub fn primary_parameter_name(name: &str) -> &str {
    // An auto-property's field, `<Name>k__BackingField`, is written as the
    // property: `Name = name;` in a constructor is how a get-only one is set.
    name.strip_prefix('<')
        .and_then(|rest| {
            rest.strip_suffix(">P")
                .or_else(|| rest.strip_suffix(">k__BackingField"))
        })
        .filter(|inner| !inner.is_empty() && !inner.contains('>'))
        .unwrap_or(name)
}

/// Marks a `foreach` hint that names the parameter the loop runs over.
const FOREACH_ARG: char = '\u{1}';
/// The same for a local.
const FOREACH_LOCAL: char = '\u{2}';

/// `name` for `names`, `entry` for `entries`; nothing for a name that is
/// not a plural.
fn singular(name: &str) -> Option<String> {
    let lower = camel(name.trim_start_matches('_'));
    if let Some(stem) = lower.strip_suffix("ies") {
        return Some(format!("{stem}y"));
    }
    if let Some(stem) = lower.strip_suffix('s')
        && stem.len() > 1
        && !stem.ends_with('s')
    {
        return Some(stem.to_string());
    }
    None
}

fn camel(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) => first.to_lowercase().chain(chars).collect(),
        None => String::new(),
    }
}

/// `stringBuilder` for `StringBuilder`, `list` for `List<int>`.
fn camel_of_type(name: &str) -> String {
    let simple = name
        .split(['<', '[', '?'])
        .next()
        .unwrap_or(name)
        .rsplit('.')
        .next()
        .unwrap_or(name);
    let simple = simple.trim_start_matches('I').to_string();
    let simple = if simple.is_empty() {
        "value".to_string()
    } else {
        simple
    };
    // `IEnumerable` loses its `I` only when the rest starts upper-case.
    let stem = if name.starts_with('I') && name.chars().nth(1).is_some_and(char::is_uppercase) {
        simple
    } else {
        name.split(['<', '[', '?'])
            .next()
            .unwrap_or(name)
            .rsplit('.')
            .next()
            .unwrap_or(name)
            .to_string()
    };
    camel(&stem)
}

fn sanitize(hint: &str) -> String {
    let cleaned: String = hint
        .chars()
        .filter(|c| c.is_alphanumeric() || *c == '_')
        .collect();
    if cleaned.is_empty() || cleaned.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        "value".to_string()
    } else {
        cleaned
    }
}

fn common_prefix<'p>(paths: impl Iterator<Item = &'p [usize]>) -> Vec<usize> {
    let mut prefix: Option<Vec<usize>> = None;
    for path in paths {
        prefix = Some(match prefix {
            None => path.to_vec(),
            Some(current) => current
                .iter()
                .zip(path)
                .take_while(|(a, b)| a == b)
                .map(|(a, _)| *a)
                .collect(),
        });
    }
    prefix.unwrap_or_default()
}

/// The name a floating constant is known by, when it is one the framework
/// defines and a compiler would have inlined.
fn well_known_float(value: f64, single: bool) -> Option<&'static str> {
    if single {
        let value = value as f32;
        return Some(match value {
            f32::MAX => "float.MaxValue",
            f32::MIN => "float.MinValue",
            f32::EPSILON => "float.Epsilon",
            _ if value == std::f32::consts::PI => "MathF.PI",
            _ if value == std::f32::consts::E => "MathF.E",
            _ => return None,
        });
    }
    Some(match value {
        f64::MAX => "double.MaxValue",
        f64::MIN => "double.MinValue",
        f64::EPSILON => "double.Epsilon",
        _ if value == std::f64::consts::PI => "Math.PI",
        _ if value == std::f64::consts::E => "Math.E",
        _ if value == std::f64::consts::TAU => "Math.Tau",
        _ => return None,
    })
}

/// A floating literal that reads back as the same value.
pub(crate) fn float_text(value: f64, single: bool) -> String {
    if value.is_nan() {
        return if single {
            "float.NaN".into()
        } else {
            "double.NaN".into()
        };
    }
    if value.is_infinite() {
        let name = if value > 0.0 {
            "PositiveInfinity"
        } else {
            "NegativeInfinity"
        };
        return if single {
            format!("float.{name}")
        } else {
            format!("double.{name}")
        };
    }
    let mut text = if single {
        format!("{}", value as f32)
    } else {
        format!("{value}")
    };
    if !text.contains('.') && !text.contains('e') && !text.contains("inf") {
        text.push_str(".0");
    }
    if single {
        text.push('f');
    }
    text
}

pub(crate) fn char_literal(c: u16) -> String {
    match char::from_u32(u32::from(c)) {
        Some('\'') => "'\\''".into(),
        Some('\\') => "'\\\\'".into(),
        Some('\n') => "'\\n'".into(),
        Some('\r') => "'\\r'".into(),
        Some('\t') => "'\\t'".into(),
        Some('\0') => "'\\0'".into(),
        Some(ch) if !ch.is_control() && !is_line_break(ch) && (ch as u32) < 0xD800 => {
            format!("'{ch}'")
        }
        _ => format!("'\\u{c:04x}'"),
    }
}

fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            // C# ends a line at these too, so a literal holding one raw
            // would end there.
            ch if ch.is_control() || is_line_break(ch) => {
                let _ = write!(out, "\\u{:04x}", ch as u32);
            }
            ch => out.push(ch),
        }
    }
    out
}

/// The line and paragraph separators, which C# counts as new lines.
const fn is_line_break(ch: char) -> bool {
    matches!(ch, '\u{2028}' | '\u{2029}')
}

pub(crate) fn string_literal(text: &str) -> String {
    format!("\"{}\"", escape(text))
}

/// An expression as text with placeholder names, for remarks.
#[must_use]
pub fn expr_text(ctx: &MethodContext<'_>, expr: &Expr) -> String {
    let mut printer = Printer::new(ctx, Vec::new(), &HashMap::new());
    printer.raw = true;
    printer.expression(expr)
}

/// A statement as text with placeholder names, for remarks.
#[must_use]
pub fn stmt_text(ctx: &MethodContext<'_>, stmt: &Stmt) -> String {
    let mut printer = Printer::new(ctx, Vec::new(), &HashMap::new());
    printer.raw = true;
    printer.body(std::slice::from_ref(stmt), 0)
}

/// An expression with no method around it: constants only.
#[must_use]
pub fn expr_text_free(expr: &Expr) -> String {
    match expr {
        Expr::Char(c) => char_literal(*c),
        Expr::Str(s) => string_literal(s),
        Expr::Float(f, single) => float_text(*f, *single),
        Expr::Int(n) => n.to_string(),
        Expr::Long(n) => format!("{n}L"),
        Expr::Bool(b) => b.to_string(),
        Expr::Null => "null".into(),
        _ => "?".into(),
    }
}

/// Whether a name needs `@` to be an identifier.
#[must_use]
pub fn is_keyword(name: &str) -> bool {
    KEYWORDS.contains(&name)
}

/// The constant lengths of a multi-dimensional array.
fn array_lengths(size: &Expr) -> Option<Vec<usize>> {
    let Expr::Tuple(sizes) = size else {
        return None;
    };
    sizes
        .iter()
        .map(|size| match size {
            Expr::Int(n) => usize::try_from(*n).ok(),
            _ => None,
        })
        .collect()
}

/// A constant, through the casts to signed types that keep its value.
/// The value of integer arithmetic on constants alone.
fn constant_value(expr: &Expr) -> Option<i128> {
    match expr {
        Expr::Int(n) | Expr::Long(n) => Some(i128::from(*n)),
        Expr::Unary(UnOp::Neg, inner) => constant_value(inner).map(|v| -v),
        // A conversion wraps into the type's range.
        Expr::Cast(ty, inner) => {
            let value = constant_value(inner)?;
            let (low, high) = integral_range(ty)?;
            let span = high - low + 1;
            Some((value - low).rem_euclid(span) + low)
        }
        Expr::Binary(op, left, right) => {
            let (left, right) = (constant_value(left)?, constant_value(right)?);
            match op {
                BinOp::Add => left.checked_add(right),
                BinOp::Sub => left.checked_sub(right),
                BinOp::Mul => left.checked_mul(right),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The values an integral type holds.
fn integral_range(ty: &TypeSig) -> Option<(i128, i128)> {
    Some(match ty {
        TypeSig::SByte => (i128::from(i8::MIN), i128::from(i8::MAX)),
        TypeSig::Byte => (0, i128::from(u8::MAX)),
        TypeSig::Int16 => (i128::from(i16::MIN), i128::from(i16::MAX)),
        TypeSig::UInt16 | TypeSig::Char => (0, i128::from(u16::MAX)),
        TypeSig::Int32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
        TypeSig::UInt32 => (0, i128::from(u32::MAX)),
        TypeSig::Int64 => (i128::from(i64::MIN), i128::from(i64::MAX)),
        TypeSig::UInt64 => (0, i128::from(u64::MAX)),
        _ => return None,
    })
}

fn negative_constant(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Int(_) | Expr::Long(_) => Some(expr),
        Expr::Cast(TypeSig::IntPtr | TypeSig::Int64 | TypeSig::Int32, inner) => {
            negative_constant(inner)
        }
        _ => None,
    }
}

/// Whether a type is, or is made of, a type parameter.
fn mentions_type_parameter(ty: &TypeSig) -> bool {
    match ty {
        TypeSig::Var(_) | TypeSig::MVar(_) => true,
        TypeSig::Vector(element) | TypeSig::Array { element, .. } => {
            mentions_type_parameter(element)
        }
        TypeSig::Generic { arguments, .. } => arguments.iter().any(mentions_type_parameter),
        _ => false,
    }
}

/// Whether a `goto` to a label sits in a `switch` inside these statements.
fn jumps_from_nested_switch(stmts: &[Stmt], label: u32, nested: bool) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Goto(target) => nested && *target == label,
        Stmt::LocalFunction { .. } => false,
        Stmt::Switch { cases, .. } => cases
            .iter()
            .any(|case| jumps_from_nested_switch(&case.body, label, true)),
        other => other
            .blocks()
            .iter()
            .any(|block| jumps_from_nested_switch(block, label, nested)),
    })
}
