//! Writing types and their members: the declarations around the bodies.
//!
//! Flags become modifiers, signatures become parameter lists, `Property`
//! and `Event` rows gather their accessors back, and the constructor's
//! opening assignments go back to the fields they initialise.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write;

use rustlyn_metadata::signature::{Blob, MethodSig, TypeSig};
use rustlyn_metadata::{Assembly, Row, Token, table};

use crate::ir::{Expr, Stmt};
use crate::names::{Annotations, AttributeValue, Constant, Generics, Index, Resolver};
use crate::{Decompiled, Options, decompile_body};

/// Writes the whole assembly, or the types a filter selects.
#[derive(Debug)]
pub struct Writer<'a> {
    pub resolver: Resolver<'a>,
    pub options: Options,
    out: String,
    indent: usize,
    /// The printed names of the types being written, innermost last, whose
    /// nested types go by their own names.
    scope: Vec<String>,
    /// For each type in `scope`, the names of the types nested in it and in
    /// those enclosing it.
    nested_names: Vec<HashSet<String>>,
    /// Every type and member written so far, and where its name is.
    pub declared: Vec<Declared>,
    /// The declaration the next line written is the header of.
    pending: Option<Pending>,
}

/// A type or member as written: what it is and where its name is in the
/// text, so an editor can go to it without reading the text back.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Declared {
    /// A type by its metadata name — `Ns.Outer/Inner`, ``List`1`` — and a
    /// member by its own, a constructor by its type's.
    pub name: String,
    /// The metadata token of the type or member.
    pub token: u32,
    pub is_type: bool,
    /// The name in the text, in bytes.
    pub start: u32,
    pub length: u32,
}

/// What `Writer::declare` noted for the header line that follows.
#[derive(Debug)]
struct Pending {
    /// The name as the header spells it.
    written: String,
    declared: String,
    token: Token,
    is_type: bool,
}

/// What kind of type a `TypeDef` is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Class,
    Struct,
    Interface,
    Enum,
    Delegate,
}

impl<'a> Writer<'a> {
    #[must_use]
    pub fn new(assembly: &'a Assembly<'a>, index: &'a Index, options: Options) -> Self {
        Self {
            resolver: Resolver::new(assembly, index),
            options,
            out: String::new(),
            indent: 0,
            scope: Vec::new(),
            nested_names: Vec::new(),
            declared: Vec::new(),
            pending: None,
        }
    }

    /// Notes that the next line written is the header of a declaration:
    /// `written` is its name as the header spells it, `declared` the name it
    /// is known by.
    fn declare(&mut self, written: &str, declared: String, token: Token, is_type: bool) {
        self.pending = Some(Pending {
            written: written.trim_start_matches('@').to_owned(),
            declared,
            token,
            is_type,
        });
    }

    /// A type's name as metadata spells it: `Ns.Outer/Inner`, with arity.
    fn metadata_type_name(&self, row: u32) -> String {
        let heaps = self.resolver.assembly.heaps();
        let Some(type_row) = self.resolver.assembly.table(table::TYPE_DEF).row(row) else {
            return String::new();
        };
        let name = heaps.string(type_row.number(1));
        match self.resolver.enclosing_type(row) {
            Some(outer) => format!("{}/{name}", self.metadata_type_name(outer)),
            None => crate::names::qualified(heaps.string(type_row.number(2)), name),
        }
    }

    /// A type name as it reads inside the type being written: a type nested
    /// in it, or in one enclosing it, goes by its own name.
    fn tn(&self, sig: &TypeSig, generics: &Generics) -> String {
        let name = self.resolver.type_name(sig, generics);
        if self.hidden_by_nested(&name) {
            return self.resolver.qualified().type_name(sig, generics);
        }
        self.scoped(name)
    }

    /// Whether a type's name is also that of a type nested where it is
    /// written, which would be the one meant.
    fn hidden_by_nested(&self, name: &str) -> bool {
        let head = name.split(['<', '.', '[']).next().unwrap_or(name);
        !self
            .scope
            .iter()
            .any(|own| name.starts_with(&format!("{own}.")))
            && self
                .nested_names
                .last()
                .is_some_and(|names| names.contains(head))
    }

    /// The same, with the annotations a row carries: tuple element names
    /// and nullable reference types.
    fn tn_annotated(
        &self,
        sig: &TypeSig,
        generics: &Generics,
        annotations: &mut Annotations,
    ) -> String {
        if self.hidden_by_nested(&self.resolver.type_name(sig, generics)) {
            return self
                .resolver
                .qualified()
                .type_name_with(sig, generics, annotations);
        }
        self.scoped(self.resolver.type_name_with(sig, generics, annotations))
    }

    fn scoped(&self, name: String) -> String {
        // The simple name each enclosing type has, innermost last.
        let simple = |full: &str| -> String {
            let last = full.rsplit('.').next().unwrap_or(full);
            last.split('<').next().unwrap_or(last).to_string()
        };
        for (depth, own) in self.scope.iter().enumerate().rev() {
            if name.starts_with(own.as_str()) && name[own.len()..].starts_with('.') {
                let rest = &name[own.len() + 1..];
                let first = rest.split(['.', '<']).next().unwrap_or(rest);
                // A type nearer in of the same name would be the one meant.
                let shadowed = self.scope[depth + 1..]
                    .iter()
                    .any(|inner| simple(inner) == first && !name.starts_with(inner.as_str()));
                if shadowed {
                    continue;
                }
                return rest.to_string();
            }
        }
        name
    }

    /// The annotations for one row of a signature: its own `Nullable`
    /// bytes, or the context of its method and type.
    fn annotations_of(&self, row: Token, method_row: Option<u32>, type_row: u32) -> Annotations {
        let mut annotations = Annotations::default();
        if let Some(names) = self.resolver.tuple_names(row) {
            annotations.tuple_names = names.into_iter().collect();
        }
        if let Some(flags) = self.resolver.nullable_flags(row) {
            annotations.nullable = flags.into_iter().collect();
        } else {
            let mut context = method_row.and_then(|method| {
                self.resolver
                    .nullable_context(Token::new(table::METHOD_DEF, method))
            });
            let mut at = Some(type_row);
            while context.is_none()
                && let Some(current) = at
            {
                context = self
                    .resolver
                    .nullable_context(Token::new(table::TYPE_DEF, current));
                at = self.resolver.enclosing_type(current);
            }
            annotations.context = context.unwrap_or(0);
        }
        annotations
    }

    fn line(&mut self, text: &str) {
        if text.is_empty() {
            self.out.push('\n');
            return;
        }
        for _ in 0..self.indent {
            self.out.push('\t');
        }
        if let Some(pending) = self.pending.take()
            && let Some(at) = name_in_header(text, &pending.written, pending.is_type)
        {
            self.declared.push(Declared {
                name: pending.declared,
                token: pending.token.0,
                is_type: pending.is_type,
                start: (self.out.len() + at) as u32,
                length: pending.written.len() as u32,
            });
        }
        self.out.push_str(text);
        self.out.push('\n');
    }

    /// Every top-level type, grouped by namespace, with `using` directives
    /// for every namespace the assembly refers to.
    #[must_use]
    pub fn assembly(self, filter: Option<&str>) -> String {
        self.assembly_declared(filter).0
    }

    /// The same, and where each type and member is in it.
    #[must_use]
    pub fn assembly_declared(mut self, filter: Option<&str>) -> (String, Vec<Declared>) {
        self.write_assembly(filter);
        (self.out, self.declared)
    }

    fn write_assembly(&mut self, filter: Option<&str>) {
        let heaps = self.resolver.assembly.heaps();
        let mut namespaces: BTreeSet<String> = BTreeSet::new();
        for row in self.resolver.assembly.table(table::TYPE_REF).iter() {
            let namespace = heaps.string(row.number(2));
            if !namespace.is_empty() {
                namespaces.insert(namespace.to_string());
            }
        }
        let mut by_namespace: BTreeMap<String, Vec<u32>> = BTreeMap::new();
        let types = self.resolver.assembly.table(table::TYPE_DEF);
        for (index, row) in types.iter().enumerate() {
            let number = index as u32 + 1;
            let name = heaps.string(row.number(1));
            // An anonymous type is written where it is made: `new { a, b }`,
            // and a lambda's natural delegate type nowhere: `var f = …`.
            if name == "<Module>"
                || name == "<PrivateImplementationDetails>"
                || name.starts_with("<>f__AnonymousType")
                || name.starts_with("<>f__AnonymousDelegate")
                || name.starts_with("<>A{")
                || name.starts_with("<>F{")
                || name.starts_with("<>A`")
                || name.starts_with("<>F`")
                || self.resolver.enclosing_type(number).is_some()
            {
                continue;
            }
            let namespace = heaps.string(row.number(2)).to_string();
            let full = crate::names::qualified(&namespace, name);
            if let Some(filter) = filter
                && !self.type_matches(number, filter)
            {
                continue;
            }
            if !self.options.compiler_generated && is_compiler_generated_name(name) {
                continue;
            }
            let _ = full;
            by_namespace.entry(namespace).or_default().push(number);
        }
        // The assembly's own namespaces are named by each other.
        if by_namespace.len() > 1 {
            namespaces.extend(by_namespace.keys().filter(|n| !n.is_empty()).cloned());
        }
        let wanted: Vec<String> = namespaces
            .iter()
            .filter(|namespace| !by_namespace.contains_key(*namespace) || by_namespace.len() > 1)
            .cloned()
            .collect();
        // The types go first, into the text the `using`s are then chosen
        // for: a namespace nothing written names is not listed.
        let before = std::mem::take(&mut self.out);
        let declared_before = self.declared.len();
        for (namespace, rows) in by_namespace {
            if namespace.is_empty() {
                for row in rows {
                    self.type_def(row, filter);
                    self.line("");
                }
                continue;
            }
            self.line(&format!("namespace {namespace}"));
            self.line("{");
            self.indent += 1;
            let count = rows.len();
            for (at, row) in rows.into_iter().enumerate() {
                self.type_def(row, filter);
                if at + 1 < count {
                    self.line("");
                }
            }
            self.indent -= 1;
            self.line("}");
            self.line("");
        }
        let body = std::mem::take(&mut self.out);
        let words: HashSet<&str> = body
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .filter(|word| !word.is_empty())
            .collect();
        let used = self.used_namespaces(&words);
        let mut prefix = before;
        // A call to a `[Conditional("X")]` method is in the IL because `X`
        // was defined; written back without it, the call would vanish.
        let defines = self.conditional_symbols();
        for symbol in &defines {
            let _ = writeln!(prefix, "#define {symbol}");
        }
        if !defines.is_empty() {
            prefix.push('\n');
        }
        let mut listed = false;
        for namespace in wanted {
            if used.contains(&namespace) {
                let _ = writeln!(prefix, "using {namespace};");
                listed = true;
            }
        }
        if listed {
            prefix.push('\n');
        }
        let shift = prefix.len() as u32;
        for declared in &mut self.declared[declared_before..] {
            declared.start += shift;
        }
        prefix.push_str(&body);
        self.out = prefix;
    }

    /// The symbols of the `[Conditional]` methods this assembly calls.
    fn conditional_symbols(&self) -> BTreeSet<String> {
        let mut symbols = BTreeSet::new();
        let methods = self.resolver.assembly.table(table::METHOD_DEF).len();
        for row in 1..=methods {
            let Some(instructions) = crate::instructions_of(self.resolver, row) else {
                continue;
            };
            for instruction in instructions {
                // `call` and `callvirt`.
                if !matches!(instruction.opcode, 0x28 | 0x6F) {
                    continue;
                }
                let rustlyn_metadata::body::Value::Token(token) = instruction.value else {
                    continue;
                };
                let Some(method) = self.resolver.method_ref(token) else {
                    continue;
                };
                let Some((there, target)) = self.resolver.definition_of_method(&method) else {
                    continue;
                };
                for (name, _, blob) in
                    there.attribute_rows(rustlyn_metadata::Token::new(table::METHOD_DEF, target))
                {
                    if name.ends_with("System.Diagnostics.ConditionalAttribute")
                        && let Some(symbol) = attribute_string(blob)
                    {
                        symbols.insert(symbol);
                    }
                }
            }
        }
        symbols
    }

    /// The namespaces whose types, or whose members (extension methods
    /// read as instance calls), the text names.
    fn used_namespaces(&self, words: &HashSet<&str>) -> HashSet<String> {
        let heaps = self.resolver.assembly.heaps();
        let named = |name: &str| {
            let bare = crate::names::strip_arity(name);
            words.contains(bare)
                || bare
                    .strip_suffix("Attribute")
                    .is_some_and(|short| words.contains(short))
        };
        let mut used = HashSet::new();
        let mut by_ref: HashMap<u32, String> = HashMap::new();
        for (index, row) in self
            .resolver
            .assembly
            .table(table::TYPE_REF)
            .iter()
            .enumerate()
        {
            let namespace = heaps.string(row.number(2));
            if namespace.is_empty() {
                continue;
            }
            by_ref.insert(index as u32 + 1, namespace.to_string());
            if named(heaps.string(row.number(1))) {
                used.insert(namespace.to_string());
            }
        }
        for row in self.resolver.assembly.table(table::TYPE_DEF).iter() {
            let namespace = heaps.string(row.number(2));
            if !namespace.is_empty() && named(heaps.string(row.number(1))) {
                used.insert(namespace.to_string());
            }
        }
        for row in self.resolver.assembly.table(table::MEMBER_REF).iter() {
            let parent = row.token(0);
            if parent.table() == table::TYPE_REF
                && let Some(namespace) = by_ref.get(&parent.row())
                && words.contains(heaps.string(row.number(1)))
            {
                used.insert(namespace.clone());
            }
        }
        used
    }

    /// Whether a type, or any type nested in it, or any of its methods, is
    /// what a `Type` or `Type::Method` filter asks for.
    fn type_matches(&self, row: u32, filter: &str) -> bool {
        let (type_part, _) = filter.split_once("::").unwrap_or((filter, ""));
        let full = self.resolver.qualified().type_def_name(row);
        let simple = self.resolver.type_def_simple_name(row);
        if full == type_part || simple == type_part || full.ends_with(&format!(".{type_part}")) {
            return true;
        }
        self.nested_of(row)
            .into_iter()
            .any(|nested| self.type_matches(nested, filter))
    }

    fn method_matches(&self, method_row: u32, filter: Option<&str>) -> bool {
        let Some(filter) = filter else {
            return true;
        };
        let Some((_, method_part)) = filter.split_once("::") else {
            return true;
        };
        let name = self
            .resolver
            .assembly
            .table(table::METHOD_DEF)
            .row(method_row)
            .map(|row| {
                self.resolver
                    .assembly
                    .heaps()
                    .string(row.number(3))
                    .to_string()
            })
            .unwrap_or_default();
        name == method_part
            || name
                .trim_start_matches(['g', 's'])
                .trim_start_matches("et_")
                == method_part
    }

    /// A method's body; one compiled into a state machine is shown as it
    /// was written, `yield` and `await` included: a property's getter too.
    fn unfolded_body(&self, method_row: u32) -> Option<Decompiled<'a>> {
        let body = decompile_body(self.resolver, method_row, &self.options);
        if let Some(found) = &body
            && let Some(machine) = crate::machines::machine_of(self.resolver, found)
            && let Some(unfolded) =
                crate::machines::machine_body(self.resolver, machine, method_row, &self.options)
        {
            return Some(unfolded);
        }
        body
    }

    fn nested_of(&self, row: u32) -> Vec<u32> {
        self.resolver.nested_of(row)
    }

    /// Whether every method of a folded-away type was folded, its
    /// constructor aside, so that nothing of it is left to show.
    fn fully_consumed(&self, type_row: u32) -> bool {
        let consumed = self.options.consumed.borrow();
        let heaps = self.resolver.assembly.heaps();
        self.resolver
            .methods_of(type_row)
            .iter()
            .all(|(row, method)| {
                let name = heaps.string(method.number(3));
                name == ".ctor" || name == ".cctor" || consumed.methods.contains(row)
            })
            && self.nested_of(type_row).iter().all(|nested| {
                // A state machine folded back into its method is gone too.
                crate::machines::is_folded_machine(&self.options, *nested)
                    || self.fully_consumed(*nested)
            })
    }

    fn kind_of(&self, row: Row<'_>) -> Kind {
        let flags = row.number(0);
        if flags & 0x20 != 0 {
            return Kind::Interface;
        }
        match self.resolver.raw_name(row.token(3)).as_deref() {
            Some("System.Enum") => Kind::Enum,
            Some("System.ValueType") => Kind::Struct,
            Some("System.MulticastDelegate" | "System.Delegate") => Kind::Delegate,
            _ => Kind::Class,
        }
    }

    #[allow(clippy::too_many_lines)]
    fn type_def(&mut self, row_number: u32, filter: Option<&str>) {
        let Some(row) = self
            .resolver
            .assembly
            .table(table::TYPE_DEF)
            .row(row_number)
        else {
            return;
        };
        let heaps = self.resolver.assembly.heaps();
        let flags = row.number(0);
        let kind = self.kind_of(row);
        let name = crate::names::strip_arity(heaps.string(row.number(1))).to_string();
        let type_token = Token::new(table::TYPE_DEF, row_number);
        let generics = Generics {
            type_params: self.resolver.type_generics(row_number),
            method_params: Vec::new(),
        };

        self.attributes(type_token, &generics);
        let record = self.record_shape(row_number, kind, &generics);
        let declared = self.metadata_type_name(row_number);
        self.declare(&name, declared, type_token, true);
        let mut header = String::new();
        header.push_str(type_visibility(flags));
        header.push(' ');
        if kind == Kind::Class {
            if flags & 0x80 != 0 && flags & 0x100 != 0 {
                header.push_str("static ");
            } else {
                if flags & 0x80 != 0 {
                    header.push_str("abstract ");
                }
                if flags & 0x100 != 0 {
                    header.push_str("sealed ");
                }
            }
        }
        if kind == Kind::Struct
            && self.resolver.has_attribute(
                type_token,
                "System.Runtime.CompilerServices.IsReadOnlyAttribute",
            )
        {
            header.push_str("readonly ");
        }
        if kind == Kind::Struct
            && self.resolver.has_attribute(
                type_token,
                "System.Runtime.CompilerServices.IsByRefLikeAttribute",
            )
        {
            header.push_str("ref ");
        }
        if kind == Kind::Delegate {
            // `public delegate R Name(params);` from `Invoke`.
            let invoke = self
                .resolver
                .methods_of(row_number)
                .into_iter()
                .find(|(_, method)| heaps.string(method.number(3)) == "Invoke");
            if let Some((invoke_row, invoke)) = invoke
                && let Some(sig) = self.resolver.method_sig_at(invoke.number(4))
            {
                let params = self.parameters(invoke_row, &sig, &generics);
                let _ = write!(
                    header,
                    "delegate {} {name}{}({params});",
                    self.tn(&sig.returns, &generics),
                    self.type_params(self.own_type_params(row_number, &generics))
                );
                self.line(&header);
                return;
            }
        }
        header.push_str(match (kind, &record) {
            (Kind::Class, Some(shape)) if shape.record => "record ",
            (Kind::Struct, Some(shape)) if shape.record => "record struct ",
            (Kind::Class | Kind::Delegate, _) => "class ",
            (Kind::Struct, _) => "struct ",
            (Kind::Interface, _) => "interface ",
            (Kind::Enum, _) => "enum ",
        });
        header.push_str(&name);
        header.push_str(&self.type_params(self.own_type_params(row_number, &generics)));
        if let Some(RecordShape {
            positional: Some(positional),
            ..
        }) = &record
        {
            let _ = write!(header, "({})", positional.params);
        }

        let mut bases: Vec<String> = Vec::new();
        if kind == Kind::Class {
            let base = row.token(3);
            if !base.is_nil() && self.resolver.raw_name(base).as_deref() != Some("System.Object") {
                let mut text = self
                    .resolver
                    .type_name(&self.resolver.token_sig(base), &generics);
                if let Some(RecordShape {
                    positional: Some(positional),
                    ..
                }) = &record
                    && let Some(arguments) = &positional.base_arguments
                {
                    let _ = write!(text, "({arguments})");
                }
                bases.push(text);
            }
        }
        if kind == Kind::Enum {
            let underlying = self
                .resolver
                .fields_of(row_number)
                .into_iter()
                .find(|(_, field)| field.number(0) & 0x0040 == 0)
                .and_then(|(_, field)| heaps.blob(field.number(2)).ok())
                .and_then(|bytes| Blob::new(bytes).field_sig().ok());
            if let Some(underlying) = underlying
                && underlying != TypeSig::Int32
            {
                bases.push(self.tn(&underlying, &generics));
            }
        }
        for interface in self.resolver.interfaces_of(row_number) {
            // A record's `IEquatable<Self>` is the compiler's.
            if record.as_ref().is_some_and(|shape| shape.record)
                && let TypeSig::Generic {
                    definition,
                    arguments,
                } = self.resolver.token_sig(interface)
                && matches!(definition.as_ref(), TypeSig::Class(token) | TypeSig::ValueType(token)
                    if self.resolver.raw_name(*token).as_deref() == Some("System.IEquatable`1"))
                && arguments.len() == 1
                && arguments[0] == self.resolver.declared_type_sig(row_number)
            {
                continue;
            }
            bases.push(
                self.resolver
                    .type_name(&self.resolver.token_sig(interface), &generics),
            );
        }
        if !bases.is_empty() {
            let _ = write!(header, " : {}", bases.join(", "));
        }
        header.push_str(&self.constraints(false, row_number, &generics));
        self.line(&header);
        self.line("{");
        self.indent += 1;
        self.scope.push(
            self.resolver
                .type_name(&self.resolver.declared_type_sig(row_number), &generics),
        );
        self.nested_names
            .push(self.resolver.nested_names_in_scope(row_number));

        if kind == Kind::Enum {
            let unsigned_long = self
                .resolver
                .enum_underlying(&self.resolver.declared_type_sig(row_number))
                == Some(TypeSig::UInt64);
            let fields = self.resolver.fields_of(row_number);
            let count = fields
                .iter()
                .filter(|(_, f)| f.number(0) & 0x0040 != 0)
                .count();
            let mut written = 0;
            let mut expected: i64 = 0;
            for (field_row, field) in fields {
                if field.number(0) & 0x0040 == 0 {
                    continue;
                }
                let constant = self
                    .resolver
                    .constant_of(Token::new(table::FIELD, field_row));
                let value = match &constant {
                    Some(Constant::Int(value)) if *value == expected => String::new(),
                    // A `ulong` past `long.MaxValue` is stored as the
                    // negative number of the same bits.
                    Some(Constant::Int(value)) if *value < 0 && unsigned_long => {
                        format!(" = {}", *value as u64)
                    }
                    Some(constant) => format!(" = {}", constant_text(constant)),
                    None => String::new(),
                };
                if let Some(Constant::Int(value)) = constant {
                    expected = value.wrapping_add(1);
                }
                written += 1;
                let comma = if written < count { "," } else { "" };
                let member = heaps.string(field.number(1)).to_string();
                self.declare(
                    &member,
                    member.clone(),
                    Token::new(table::FIELD, field_row),
                    false,
                );
                self.line(&format!("{member}{value}{comma}"));
            }
            self.scope.pop();
            self.nested_names.pop();
            self.indent -= 1;
            self.line("}");
            return;
        }

        let methods = self.resolver.methods_of(row_number);
        let mut accessor_rows: HashSet<u32> = HashSet::new();
        for (method_row, _) in &methods {
            if self.resolver.accessor_role(*method_row).is_some() {
                accessor_rows.insert(*method_row);
            }
        }

        // Constructors, decompiled first so field initialisers can be lifted
        // out of them.
        let mut initializers: BTreeMap<String, String> = BTreeMap::new();
        let mut decompiled: Vec<(u32, Row<'a>, Option<Decompiled>)> = Vec::new();
        for (method_row, method) in &methods {
            if accessor_rows.contains(method_row) {
                decompiled.push((*method_row, *method, None));
                continue;
            }
            let mut body = self.unfolded_body(*method_row);
            // A destructor's body is its `try`: the `finally` calling the
            // base's `Finalize` is what `~T()` means.
            if heaps.string(method.number(3)) == "Finalize"
                && let Some(found) = &mut body
                && let [
                    Stmt::Try {
                        body: inner,
                        catches,
                        finally: Some(finally),
                    },
                ] = found.stmts.as_mut_slice()
                && catches.is_empty()
                && matches!(finally.as_slice(), [Stmt::Expr(Expr::Call { method, receiver: Some(receiver), .. })]
                    if method.name == "Finalize" && matches!(receiver.as_ref(), Expr::Base | Expr::This))
            {
                let inner = std::mem::take(inner);
                found.stmts = inner;
            }
            decompiled.push((*method_row, *method, body));
        }
        let mut skip_methods: HashSet<u32> = HashSet::new();
        for (method_row, method, body) in &mut decompiled {
            let method_name = heaps.string(method.number(3));
            if method_name != ".ctor" && method_name != ".cctor" {
                continue;
            }
            let Some(body) = body else {
                continue;
            };
            let is_static = method_name == ".cctor";
            let lifted = lift_field_initializers(body, is_static, row_number);
            for (field, text) in lifted {
                initializers.entry(field).or_insert(text);
            }
            let real: Vec<&Stmt> = body
                .stmts
                .iter()
                .filter(|s| !matches!(s, Stmt::Label(_)))
                .collect();
            if is_static && real.is_empty() {
                skip_methods.insert(*method_row);
            }
            if !is_static
                && real.len() == 1
                && body.base_call_is_trivial
                && is_default_ctor(&methods, *method_row, self.resolver)
            {
                skip_methods.insert(*method_row);
            }
        }

        if let Some(record) = &record {
            skip_methods.extend(record.hidden_methods.iter().copied());
            for (field, text) in &record.initializers {
                initializers.insert(field.clone(), text.clone());
            }
        }
        let mut wrote_any = false;
        // Fields.
        let mut properties = self.properties_of(row_number);
        let mut backing_fields: HashSet<String> = properties
            .iter()
            .filter_map(|property| property.auto_backing.clone())
            .collect();
        if let Some(record) = &record {
            properties.retain(|property| !record.hidden_properties.contains(&property.name));
        }
        let events = self.events_of(row_number);
        backing_fields.extend(events.iter().map(|event| event.name.clone()));
        for (field_row, field) in self.resolver.fields_of(row_number) {
            let field_name = heaps.string(field.number(1)).to_string();
            if backing_fields.contains(&field_name) {
                continue;
            }
            if record
                .as_ref()
                .is_some_and(|shape| shape.hidden_fields.contains(&field_name))
            {
                continue;
            }
            if !self.options.compiler_generated
                && field_name.starts_with('<')
                && kind != Kind::Struct
            {
                // Display-class and state-machine fields are shown with their
                // types; only the auto-property backing fields are folded.
                if field_name.ends_with("k__BackingField") {
                    continue;
                }
            }
            let field_token = Token::new(table::FIELD, field_row);
            let Ok(bytes) = heaps.blob(field.number(2)) else {
                continue;
            };
            let Ok(ty) = Blob::new(bytes).field_sig() else {
                continue;
            };
            self.attributes(field_token, &generics);
            let shown = crate::print::primary_parameter_name(&field_name).to_owned();
            self.declare(&shown, shown.clone(), field_token, false);
            let field_flags = field.number(0);
            let mut text = String::new();
            if kind != Kind::Interface {
                text.push_str(member_visibility(field_flags & 0x7));
                text.push(' ');
            }
            if is_unsafe_type(&ty) || self.fixed_buffer(&ty, &generics).is_some() {
                text.push_str("unsafe ");
            }
            if self.resolver.has_attribute(
                field_token,
                "System.Runtime.CompilerServices.RequiredMemberAttribute",
            ) {
                text.push_str("required ");
            }
            // `const decimal` is a static field with its value in an
            // attribute.
            let decimal_constant = self.decimal_constant(field_token);
            if field_flags & 0x0040 != 0 || decimal_constant.is_some() {
                text.push_str("const ");
            } else {
                if field_flags & 0x0010 != 0 {
                    text.push_str("static ");
                }
                if field_flags & 0x0020 != 0 {
                    text.push_str("readonly ");
                }
            }
            if let Some((element, length)) = self.fixed_buffer(&ty, &generics) {
                // `fixed float planes[24]`: what C# wrote before it became a
                // struct named `<planes>e__FixedBuffer` of the same size.
                let _ = write!(
                    text,
                    "fixed {element} {}[{length}];",
                    escape_name(&field_name)
                );
                self.line(&text);
                wrote_any = true;
                continue;
            }
            let _ = write!(
                text,
                "{} {}",
                self.tn(&ty, &generics),
                escape_name(crate::print::primary_parameter_name(&field_name))
            );
            if let Some(literal) = decimal_constant {
                let _ = write!(text, " = {literal}");
            } else if let Some(constant) = self.resolver.constant_of(field_token) {
                let value = match (&constant, self.resolver.enum_of(&ty)) {
                    (Constant::Int(value), Some(members)) => {
                        members.iter().find(|(_, v)| v == value).map_or_else(
                            || format!("({}){value}", self.tn(&ty, &generics)),
                            |(name, _)| format!("{}.{name}", self.tn(&ty, &generics)),
                        )
                    }
                    _ => constant_text(&constant),
                };
                let _ = write!(text, " = {value}");
            } else if let Some(initializer) = initializers.get(&field_name) {
                let _ = write!(text, " = {initializer}");
            }
            text.push(';');
            self.line(&text);
            wrote_any = true;
        }

        // Properties and events.
        for property in &properties {
            if wrote_any {
                self.line("");
            }
            self.property(property, &generics, kind, &initializers, filter);
            wrote_any = true;
        }
        for event in &events {
            if wrote_any {
                self.line("");
            }
            self.event(event, &generics, kind, filter);
            wrote_any = true;
        }

        // Methods.
        for (method_row, method, body) in decompiled {
            if accessor_rows.contains(&method_row) || skip_methods.contains(&method_row) {
                continue;
            }
            if self.options.consumed.borrow().methods.contains(&method_row) {
                continue;
            }
            if !self.method_matches(method_row, filter) {
                continue;
            }
            let method_name = heaps.string(method.number(3));
            if !self.options.compiler_generated
                && is_compiler_generated_name(method_name)
                && !method_name.starts_with('<')
            {
                continue;
            }
            if wrote_any {
                self.line("");
            }
            self.method(
                row_number,
                &name,
                kind,
                method_row,
                method,
                body.as_ref(),
                &generics,
            );
            wrote_any = true;
        }

        // `==` without `!=`, the other trimmed away: C# wants both, and
        // the one is the other negated.
        let operators: Vec<(u32, String)> = self
            .resolver
            .methods_of(row_number)
            .into_iter()
            .map(|(row, method)| (row, heaps.string(method.number(3)).to_string()))
            .filter(|(_, name)| name == "op_Equality" || name == "op_Inequality")
            .collect();
        if let [(row, present)] = operators.as_slice()
            && self.method_matches(*row, filter)
            && let Some(method) = self.resolver.assembly.table(table::METHOD_DEF).row(*row)
            && let Some(sig) = self.resolver.method_sig_at(method.number(4))
            && let [left, right] = sig.parameters.as_slice()
        {
            let (symbol, other) = if present == "op_Equality" {
                ("!=", "==")
            } else {
                ("==", "!=")
            };
            if wrote_any {
                self.line("");
            }
            self.line(&format!(
                "public static bool operator {symbol}({} left, {} right) => !(left {other} right);",
                self.tn(left, &generics),
                self.tn(right, &generics)
            ));
            wrote_any = true;
        }

        // Nested types.
        for nested in self.nested_of(row_number) {
            let nested_name = self
                .resolver
                .assembly
                .table(table::TYPE_DEF)
                .row(nested)
                .map(|row| heaps.string(row.number(1)).to_string())
                .unwrap_or_default();
            if !self.options.compiler_generated && is_compiler_generated_name(&nested_name) {
                continue;
            }
            if self.options.consumed.borrow().types.contains(&nested) && self.fully_consumed(nested)
            {
                continue;
            }
            // A display class with no lambdas of its own holds the
            // variables of an outer scope for the closures nested in it:
            // it goes with them.
            if nested_name.starts_with("<>c__DisplayClass") && self.fully_consumed(nested) {
                continue;
            }
            if crate::machines::is_folded_machine(&self.options, nested) {
                continue;
            }
            // The struct a `fixed` buffer is stored as.
            if nested_name.starts_with('<') && nested_name.ends_with(">e__FixedBuffer") {
                continue;
            }
            if wrote_any {
                self.line("");
            }
            self.type_def(nested, filter);
            wrote_any = true;
        }

        self.scope.pop();
        self.nested_names.pop();
        self.indent -= 1;
        self.line("}");
    }

    /// What a record declaration says in its header and the compiler
    /// wrote out as members: a class with `<Clone>$`, a struct with a
    /// generated `PrintMembers`.
    fn record_shape(&self, type_row: u32, kind: Kind, generics: &Generics) -> Option<RecordShape> {
        let heaps = self.resolver.assembly.heaps();
        let methods = self.resolver.methods_of(type_row);
        let generated = |row: u32| {
            self.resolver.has_attribute(
                Token::new(table::METHOD_DEF, row),
                "System.Runtime.CompilerServices.CompilerGeneratedAttribute",
            )
        };
        let name_of = |method: &Row<'_>| heaps.string(method.number(3)).to_string();
        let is_record = match kind {
            Kind::Class => methods
                .iter()
                .any(|(_, method)| name_of(method) == "<Clone>$"),
            Kind::Struct => methods
                .iter()
                .any(|(row, method)| name_of(method) == "PrintMembers" && generated(*row)),
            _ => false,
        };
        if !is_record {
            return self.primary_constructor_shape(type_row, kind, generics);
        }
        let self_sig = self.resolver.declared_type_sig(type_row);
        let mut shape = RecordShape {
            record: true,
            ..RecordShape::default()
        };
        shape
            .hidden_properties
            .insert("EqualityContract".to_string());
        for (row, method) in &methods {
            let name = name_of(method);
            let Some(sig) = self.resolver.method_sig_at(method.number(4)) else {
                continue;
            };
            let synthesized = match name.as_str() {
                "<Clone>$" => true,
                "get_EqualityContract"
                | "ToString"
                | "PrintMembers"
                | "op_Equality"
                | "op_Inequality"
                | "GetHashCode"
                | "Equals" => generated(*row),
                // The copy constructor `with` goes through.
                ".ctor" => {
                    kind == Kind::Class
                        && sig.parameters.len() == 1
                        && sig.parameters[0] == self_sig
                        && crate::param_names(self.resolver, *row, 1)[0] == "original"
                }
                _ => false,
            };
            if synthesized {
                shape.hidden_methods.insert(*row);
            }
        }
        // The primary constructor: every parameter stored into the backing
        // field of a generated property of its name, with a `Deconstruct`
        // to match.
        let properties = self.properties_of(type_row);
        let deconstruct = methods
            .iter()
            .find(|(row, method)| name_of(method) == "Deconstruct" && generated(*row));
        let positional = deconstruct.and_then(|(deconstruct_row, deconstruct)| {
            let deconstruct_sig = self.resolver.method_sig_at(deconstruct.number(4))?;
            let names = crate::param_names(
                self.resolver,
                *deconstruct_row,
                deconstruct_sig.parameters.len(),
            );
            let (ctor_row, _) = methods.iter().find(|(row, method)| {
                name_of(method) == ".ctor"
                    && self
                        .resolver
                        .method_sig_at(method.number(4))
                        .is_some_and(|sig| {
                            sig.parameters.len() == names.len()
                                && crate::param_names(self.resolver, *row, names.len()) == names
                        })
            })?;
            let body = decompile_body(self.resolver, *ctor_row, &self.options)?;
            let mut base_arguments = None;
            for stmt in &body.stmts {
                match stmt {
                    Stmt::Label(_) | Stmt::Return(None) => {}
                    Stmt::Expr(Expr::Assign(target, value)) => {
                        let (Expr::Field {
                            receiver: Some(receiver),
                            ..
                        }
                        | Expr::Property {
                            receiver: Some(receiver),
                            ..
                        }) = target.as_ref()
                        else {
                            return None;
                        };
                        if **receiver != Expr::This {
                            return None;
                        }
                        let stored = match target.as_ref() {
                            Expr::Field { field, .. } => {
                                crate::print::primary_parameter_name(&field.name).to_string()
                            }
                            Expr::Property { name, .. } => name.clone(),
                            _ => return None,
                        };
                        match value.as_ref() {
                            Expr::Arg(at) if names.get(*at as usize) == Some(&stored) => {}
                            // A field initialiser, lifted on its own.
                            other
                                if other.count(&|e| {
                                    matches!(e, Expr::Arg(_) | Expr::Local(_) | Expr::Slot(_))
                                }) == 0 => {}
                            _ => return None,
                        }
                    }
                    Stmt::Expr(Expr::Call {
                        method,
                        receiver: Some(receiver),
                        args,
                    }) if method.is_constructor()
                        && matches!(receiver.as_ref(), Expr::This | Expr::Base) =>
                    {
                        if !args.is_empty() {
                            base_arguments = Some(
                                args.iter()
                                    .map(|arg| body.printer().expression(arg))
                                    .collect::<Vec<_>>()
                                    .join(", "),
                            );
                        }
                    }
                    _ => return None,
                }
            }
            let ctor_method = methods.iter().find(|(row, _)| row == ctor_row)?.1;
            let ctor_sig = self.resolver.method_sig_at(ctor_method.number(4))?;
            Some((
                *ctor_row,
                *deconstruct_row,
                RecordPositional {
                    params: self.parameters(*ctor_row, &ctor_sig, generics),
                    base_arguments,
                },
                names,
            ))
        });
        if let Some((ctor_row, deconstruct_row, positional, names)) = positional {
            shape.hidden_methods.insert(ctor_row);
            shape.hidden_methods.insert(deconstruct_row);
            for property in &properties {
                if names.contains(&property.name)
                    && property.auto_backing.is_some()
                    && property.getter.is_some_and(generated)
                {
                    shape.hidden_properties.insert(property.name.clone());
                }
            }
            shape.positional = Some(positional);
        }
        Some(shape)
    }

    /// A class or struct whose constructor's parameters are captured in
    /// fields named `<name>P`: C# 12's primary constructor.
    fn primary_constructor_shape(
        &self,
        type_row: u32,
        kind: Kind,
        generics: &Generics,
    ) -> Option<RecordShape> {
        if !matches!(kind, Kind::Class | Kind::Struct) {
            return None;
        }
        let heaps = self.resolver.assembly.heaps();
        let captured: HashSet<String> = self
            .resolver
            .fields_of(type_row)
            .iter()
            .map(|(_, field)| heaps.string(field.number(1)).to_string())
            .filter(|name| name.starts_with('<') && name.ends_with(">P"))
            .collect();
        if captured.is_empty() {
            return None;
        }
        let methods = self.resolver.methods_of(type_row);
        for (ctor_row, method) in &methods {
            if heaps.string(method.number(3)) != ".ctor" {
                continue;
            }
            let Some(sig) = self.resolver.method_sig_at(method.number(4)) else {
                continue;
            };
            let names = crate::param_names(self.resolver, *ctor_row, sig.parameters.len());
            let Some(body) = decompile_body(self.resolver, *ctor_row, &self.options) else {
                continue;
            };
            // The captured fields read as the parameters they hold.
            let as_parameter = |expr: &Expr| -> Expr {
                let mut expr = expr.clone();
                expr.map(&mut |e| {
                    if let Expr::Field {
                        receiver: Some(receiver),
                        field,
                    } = e
                        && **receiver == Expr::This
                        && captured.contains(&field.name)
                        && let Some(at) = names
                            .iter()
                            .position(|name| format!("<{name}>P") == field.name)
                    {
                        *e = Expr::Arg(at as u16);
                    }
                });
                expr
            };
            let mut assigned: HashSet<String> = HashSet::new();
            let mut initializers = Vec::new();
            let mut base_arguments = None;
            let mut fits = true;
            for stmt in &body.stmts {
                match stmt {
                    Stmt::Label(_) | Stmt::Return(None) => {}
                    Stmt::Expr(Expr::Assign(target, value)) => {
                        let member = match target.as_ref() {
                            Expr::Field {
                                receiver: Some(receiver),
                                field,
                            } if **receiver == Expr::This => field.name.clone(),
                            _ => {
                                fits = false;
                                break;
                            }
                        };
                        if captured.contains(&member) {
                            if matches!(value.as_ref(), Expr::Arg(at)
                                if format!("<{}>P", names[*at as usize]) == member)
                            {
                                assigned.insert(member);
                                continue;
                            }
                            fits = false;
                            break;
                        }
                        let value = as_parameter(value);
                        initializers.push((member, body.printer().expression(&value)));
                    }
                    Stmt::Expr(Expr::Call {
                        method,
                        receiver: Some(receiver),
                        args,
                    }) if method.is_constructor()
                        && matches!(receiver.as_ref(), Expr::This | Expr::Base) =>
                    {
                        if !args.is_empty() {
                            base_arguments = Some(
                                args.iter()
                                    .map(|arg| body.printer().expression(&as_parameter(arg)))
                                    .collect::<Vec<_>>()
                                    .join(", "),
                            );
                        }
                    }
                    _ => {
                        fits = false;
                        break;
                    }
                }
            }
            if !fits || assigned != captured {
                continue;
            }
            let mut shape = RecordShape {
                positional: Some(RecordPositional {
                    params: self.parameters(*ctor_row, &sig, generics),
                    base_arguments,
                }),
                hidden_fields: captured,
                initializers,
                ..RecordShape::default()
            };
            shape.hidden_methods.insert(*ctor_row);
            return Some(shape);
        }
        None
    }

    fn type_params(&self, params: &[String]) -> String {
        if params.is_empty() {
            String::new()
        } else {
            format!("<{}>", params.join(", "))
        }
    }

    /// The `where` clauses of a type or method.
    /// A nested type's own type parameters: metadata repeats the enclosing
    /// type's in front of them, which C# does not declare again.
    fn own_type_params<'g>(&self, row: u32, generics: &'g Generics) -> &'g [String] {
        let inherited = self.resolver.enclosing_type(row).map_or(0, |outer| {
            self.resolver.generic_param_names(false, outer).len()
        });
        generics.type_params.get(inherited..).unwrap_or(&[])
    }

    fn constraints(&self, is_method: bool, row: u32, generics: &Generics) -> String {
        let inherited = if is_method {
            0
        } else {
            self.resolver.enclosing_type(row).map_or(0, |outer| {
                self.resolver.generic_param_names(false, outer).len()
            })
        };
        constraint_clauses(self.resolver, is_method, row, generics, inherited)
    }
}

/// The `where` clauses of a type's or method's type parameters, past the
/// first `inherited` of them.
pub(crate) fn constraint_clauses(
    resolver: Resolver<'_>,
    is_method: bool,
    row: u32,
    generics: &Generics,
    inherited: usize,
) -> String {
    let mut out = String::new();
    {
        for (name, flags, param_row) in resolver
            .generic_param_rows(is_method, row)
            .into_iter()
            .skip(inherited)
        {
            let mut clauses: Vec<String> = Vec::new();
            if flags & 0x04 != 0 {
                clauses.push("class".into());
            }
            if flags & 0x08 != 0 {
                clauses.push("struct".into());
            }
            for token in resolver.constraints_of(param_row) {
                if resolver.raw_name(token).as_deref() == Some("System.ValueType") {
                    continue;
                }
                // `unmanaged` is `struct` and a `ValueType` modified to say
                // so, which only a `TypeSpec` can carry.
                if token.table() == table::TYPE_SPEC
                    && let Some(TypeSig::ValueType(inner) | TypeSig::Class(inner)) =
                        resolver.type_spec(token.row())
                    && resolver.raw_name(inner).as_deref() == Some("System.ValueType")
                {
                    if let Some(at) = clauses.iter().position(|clause| clause == "struct") {
                        clauses[at] = "unmanaged".into();
                    } else {
                        clauses.insert(0, "unmanaged".into());
                    }
                    continue;
                }
                clauses.push(resolver.type_name(&resolver.token_sig(token), generics));
            }
            if flags & 0x10 != 0 && flags & 0x08 == 0 {
                clauses.push("new()".into());
            }
            if !clauses.is_empty() {
                let _ = write!(out, " where {name} : {}", clauses.join(", "));
            }
        }
    }
    out
}

impl<'a> Writer<'a> {
    /// `[StructLayout(…)]` for a type whose layout is not the one C# gives
    /// it by itself: sequential for a struct, automatic for a class, with
    /// no packing or size. A struct of no fields is one byte, which needs
    /// no saying either.
    fn struct_layout(&self, row: u32, flags: u32) -> Option<String> {
        let value_type = self
            .resolver
            .is_value_type_token(rustlyn_metadata::Token::new(table::TYPE_DEF, row));
        let kind = match flags & 0x18 {
            0x10 => "Explicit",
            0x08 => "Sequential",
            _ => "Auto",
        };
        let (pack, size) = self
            .resolver
            .assembly
            .table(table::CLASS_LAYOUT)
            .iter()
            .find(|layout| layout.number(2) == row)
            .map_or((0, 0), |layout| (layout.number(0), layout.number(1)));
        let default_kind = if value_type { "Sequential" } else { "Auto" };
        let default_size = value_type && kind == "Sequential" && pack == 0 && size == 1;
        if kind == default_kind && pack == 0 && (size == 0 || default_size) {
            return None;
        }
        let mut text = format!(
            "[System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.{kind}"
        );
        if pack != 0 {
            let _ = write!(text, ", Pack = {pack}");
        }
        if size != 0 && !default_size {
            let _ = write!(text, ", Size = {size}");
        }
        text.push_str(")]");
        Some(text)
    }

    /// Custom attributes on a row, by name only.
    fn attributes(&mut self, parent: Token, generics: &Generics) {
        // What the metadata keeps as flags rather than as attributes.
        if let Some(row) = self.resolver.assembly.row(parent) {
            let flags = row.number(0);
            if parent.table() == table::TYPE_DEF && flags & 0x2000 != 0 {
                self.line("[Serializable]");
            }
            if parent.table() == table::FIELD && flags & 0x0080 != 0 {
                self.line("[NonSerialized]");
            }
            // The layout is flags and a ClassLayout row; it changes what the
            // runtime does (a union through `Explicit`), so it is said.
            if parent.table() == table::TYPE_DEF
                && let Some(text) = self.struct_layout(parent.row(), flags)
            {
                self.line(&text);
            }
            if parent.table() == table::FIELD
                && let Some(offset) = self
                    .resolver
                    .assembly
                    .table(table::FIELD_LAYOUT)
                    .iter()
                    .find(|layout| layout.number(1) == parent.row())
                    .map(|layout| layout.number(0))
            {
                self.line(&format!(
                    "[System.Runtime.InteropServices.FieldOffset({offset})]"
                ));
            }
        }
        for (name, ctor, blob) in self.resolver.attribute_rows(parent) {
            let simple = name.rsplit(['.', '/']).next().unwrap_or(&name);
            if matches!(
                simple,
                "CompilerGeneratedAttribute"
                    | "NullableAttribute"
                    | "NullableContextAttribute"
                    | "ParamArrayAttribute"
                    | "IsReadOnlyAttribute"
                    | "IsByRefLikeAttribute"
                    | "ExtensionAttribute"
                    | "DebuggerStepThroughAttribute"
                    | "DebuggerBrowsableAttribute"
                    | "DebuggerHiddenAttribute"
                    | "AsyncStateMachineAttribute"
                    | "IteratorStateMachineAttribute"
                    | "DefaultMemberAttribute"
                    | "TupleElementNamesAttribute"
                    | "RefSafetyRulesAttribute"
                    | "ScopedRefAttribute"
                    | "InAttribute"
                    | "OutAttribute"
                    | "IsUnmanagedAttribute"
                    | "DynamicAttribute"
                    | "NativeIntegerAttribute"
                    | "InlineArrayAttribute"
                    | "EmbeddedAttribute"
                    | "FixedBufferAttribute"
                    | "UnsafeValueTypeAttribute"
                    | "AsyncIteratorStateMachineAttribute"
                    | "CompilerFeatureRequiredAttribute"
                    | "RequiresLocationAttribute"
                    | "PreserveBaseOverridesAttribute"
                    | "DecimalConstantAttribute"
            ) {
                continue;
            }
            // `required` says it on the member; the constructors are
            // marked obsolete for compilers that do not know it.
            if simple == "RequiredMemberAttribute" {
                continue;
            }
            let arguments = self.resolver.attribute_arguments(ctor, blob);
            if simple == "ObsoleteAttribute"
                && parent.table() == table::METHOD_DEF
                && matches!(&arguments, Some((fixed, _))
                    if matches!(fixed.first(), Some(AttributeValue::Str(Some(text)))
                        if text.starts_with("Constructors of types with required members")))
            {
                continue;
            }
            // A `ref struct` is marked obsolete for compilers that do not
            // know what it is.
            if simple == "ObsoleteAttribute"
                && parent.table() == table::TYPE_DEF
                && matches!(&arguments, Some((fixed, _))
                    if matches!(fixed.first(), Some(AttributeValue::Str(Some(text)))
                        if text.starts_with("Types with embedded references are not supported")))
            {
                continue;
            }
            let shown = simple.strip_suffix("Attribute").unwrap_or(simple);
            let text = match arguments {
                Some((fixed, named)) if !fixed.is_empty() || !named.is_empty() => {
                    let mut parts: Vec<String> = fixed
                        .iter()
                        .map(|value| self.attribute_value(value, generics))
                        .collect();
                    parts.extend(named.iter().map(|(name, value)| {
                        format!("{name} = {}", self.attribute_value(value, generics))
                    }));
                    format!("[{shown}({})]", parts.join(", "))
                }
                _ => format!("[{shown}]"),
            };
            self.line(&text);
        }
    }

    /// The value of a `const decimal`, from its `DecimalConstant` attribute.
    fn decimal_constant(&self, parent: Token) -> Option<String> {
        let (_, ctor, blob) =
            self.resolver
                .attribute_rows(parent)
                .into_iter()
                .find(|(name, _, _)| {
                    name == "System.Runtime.CompilerServices.DecimalConstantAttribute"
                })?;
        let (fixed, _) = self.resolver.attribute_arguments(ctor, blob)?;
        let number = |value: &AttributeValue| match value {
            AttributeValue::Int(n) => Some(*n),
            AttributeValue::UInt(n) => Some(*n as i64),
            _ => None,
        };
        let [scale, sign, hi, mid, lo] = fixed.as_slice() else {
            return None;
        };
        Some(crate::stack::decimal_text(
            number(lo)? as u32,
            number(mid)? as u32,
            number(hi)? as u32,
            number(sign)? != 0,
            number(scale)? as u32,
        ))
    }

    /// An attribute argument as C#.
    fn attribute_value(&self, value: &AttributeValue, generics: &Generics) -> String {
        match value {
            AttributeValue::Bool(value) => value.to_string(),
            AttributeValue::Char(c) => crate::print::char_literal(*c),
            AttributeValue::Int(value) => value.to_string(),
            AttributeValue::UInt(value) => format!("{value}uL"),
            AttributeValue::Float(value, single) => crate::print::float_text(*value, *single),
            AttributeValue::Str(Some(text)) => crate::print::string_literal(text),
            AttributeValue::Str(None)
            | AttributeValue::Type(None)
            | AttributeValue::Array(None) => "null".into(),
            AttributeValue::Type(Some(name)) => {
                let shown = self
                    .resolver
                    .type_by_serialized_name(name)
                    .map(|found| {
                        self.resolver.token_sig(match found {
                            TypeSig::ValueType(token) | TypeSig::Class(token) => token,
                            _ => Token(0),
                        })
                    })
                    .map(|sig| self.tn(&sig, generics))
                    .unwrap_or_else(|| serialized_type_name(name));
                // An open generic type: `typeof(List<>)`, its arity in the
                // name.
                let bare = name.split(',').next().unwrap_or(name).trim();
                // A type nested in an open generic one, arities anywhere
                // in the name: `typeof(List<>.Enumerator)`.
                if !bare.contains('[')
                    && bare.contains('`')
                    && bare.contains('+')
                    && let Some(TypeSig::ValueType(token) | TypeSig::Class(token)) =
                        self.resolver.type_by_serialized_name(name)
                    && let Some(open) = self.resolver.open_generic_name(token)
                {
                    return format!("typeof({open})");
                }
                let open = if bare.contains('[') {
                    String::new()
                } else {
                    bare.rsplit('`')
                        .next()
                        .filter(|_| bare.contains('`'))
                        .and_then(|digits| digits.parse::<usize>().ok())
                        .map(|arity| format!("<{}>", ",".repeat(arity.saturating_sub(1))))
                        .unwrap_or_default()
                };
                format!("typeof({shown}{open})")
            }
            AttributeValue::Enum(ty, name, value) => {
                let ty = ty.clone().or_else(|| {
                    name.as_ref()
                        .and_then(|name| self.resolver.type_by_serialized_name(name))
                });
                let shown = match &ty {
                    Some(ty) => self.tn(ty, generics),
                    None => name
                        .as_deref()
                        .map_or_else(|| "int".into(), serialized_type_name),
                };
                match ty.as_ref().and_then(|ty| self.resolver.enum_of(ty)) {
                    Some(members) => match members.iter().find(|(_, v)| v == value) {
                        Some((member, _)) => format!("{shown}.{member}"),
                        None => {
                            // Flags: the members that make up the value.
                            let mut rest = *value;
                            let mut parts = Vec::new();
                            for (member, v) in members.iter().rev() {
                                if *v != 0 && rest & v == *v {
                                    parts.push(format!("{shown}.{member}"));
                                    rest &= !v;
                                }
                            }
                            if rest == 0 && !parts.is_empty() {
                                parts.reverse();
                                parts.join(" | ")
                            } else {
                                format!("({shown}){value}")
                            }
                        }
                    },
                    None => format!("({shown}){value}"),
                }
            }
            AttributeValue::Array(Some(items)) => {
                let texts: Vec<String> = items
                    .iter()
                    .map(|item| self.attribute_value(item, generics))
                    .collect();
                format!("new[] {{ {} }}", texts.join(", "))
            }
        }
    }

    /// The `Param` row of a method's return value, when there is one.
    fn return_param(&self, method_row: u32) -> Option<Token> {
        let params_table = self.resolver.assembly.table(table::PARAM);
        let methods = self.resolver.assembly.table(table::METHOD_DEF);
        let start = methods.row(method_row)?.number(5);
        let end = methods
            .row(method_row + 1)
            .map_or(params_table.len() + 1, |next| next.number(5));
        (start..end)
            .filter_map(|n| params_table.row(n).map(|r| (n, r)))
            .find(|(_, r)| r.number(1) == 0)
            .map(|(n, _)| Token::new(table::PARAM, n))
    }

    /// A method's parameter list, names and modifiers included.
    fn parameters(&self, method_row: u32, sig: &MethodSig, generics: &Generics) -> String {
        let names = crate::param_names(self.resolver, method_row, sig.parameters.len());
        let params = self.resolver.params_of(method_row);
        let param_row_of = |sequence: usize| -> Option<Token> {
            let params_table = self.resolver.assembly.table(table::PARAM);
            let methods = self.resolver.assembly.table(table::METHOD_DEF);
            let start = methods.row(method_row)?.number(5);
            let end = methods
                .row(method_row + 1)
                .map_or(params_table.len() + 1, |next| next.number(5));
            (start..end)
                .filter_map(|n| params_table.row(n).map(|r| (n, r)))
                .find(|(_, r)| r.number(1) as usize == sequence)
                .map(|(n, _)| Token::new(table::PARAM, n))
        };
        let mut texts = Vec::with_capacity(sig.parameters.len());
        for (index, ty) in sig.parameters.iter().enumerate() {
            let flags = params
                .iter()
                .find(|(sequence, _, _)| *sequence as usize == index + 1)
                .map_or(0, |(_, flags, _)| *flags);
            let mut text = String::new();
            let is_extension_this = index == 0
                && self.resolver.has_attribute(
                    Token::new(table::METHOD_DEF, method_row),
                    "System.Runtime.CompilerServices.ExtensionAttribute",
                );
            if is_extension_this {
                text.push_str("this ");
            }
            let param_token = param_row_of(index + 1);
            // `scoped`: the reference, or the span, may not escape the call.
            if param_token.is_some_and(|token| {
                self.resolver
                    .has_attribute(token, "System.Runtime.CompilerServices.ScopedRefAttribute")
            }) {
                text.push_str("scoped ");
            }
            let owner = self.resolver.method_owner(method_row).unwrap_or(0);
            let mut annotations = param_token
                .map(|token| self.annotations_of(token, Some(method_row), owner))
                .unwrap_or_else(|| self.annotations_of(Token(0), Some(method_row), owner));
            if let TypeSig::ByRef(inner) = ty {
                let required = sig.parameters_required.get(index);
                let is_in = required.is_some_and(|mods| {
                    mods.iter().any(|token| {
                        self.resolver.raw_name(*token).as_deref()
                            == Some("System.Runtime.InteropServices.InAttribute")
                    })
                }) || (flags & 0x0001 != 0 && flags & 0x0002 == 0);
                if flags & 0x0002 != 0 && flags & 0x0001 == 0 {
                    text.push_str("out ");
                } else if is_in {
                    text.push_str("in ");
                } else {
                    text.push_str("ref ");
                }
                text.push_str(&self.tn_annotated(inner, generics, &mut annotations));
            } else {
                if let Some(token) = param_token
                    && self
                        .resolver
                        .has_attribute(token, "System.ParamArrayAttribute")
                {
                    text.push_str("params ");
                }
                text.push_str(&self.tn_annotated(ty, generics, &mut annotations));
            }
            let _ = write!(text, " {}", escape_name(&names[index]));
            if flags & 0x1000 != 0
                && let Some(token) = param_token
            {
                match self.resolver.constant_of(token) {
                    Some(constant) => {
                        let value = match (&constant, self.resolver.enum_of(ty)) {
                            (Constant::Int(value), Some(members)) => {
                                members.iter().find(|(_, v)| v == value).map_or_else(
                                    || format!("({}){value}", self.tn(ty, generics)),
                                    |(name, _)| format!("{}.{name}", self.tn(ty, generics)),
                                )
                            }
                            // `in S s = default` is by reference.
                            (Constant::Null, _)
                                if self.resolver.is_value_type(match ty {
                                    TypeSig::ByRef(inner) => inner,
                                    other => other,
                                }) =>
                            {
                                "default".to_string()
                            }
                            _ => constant_text(&constant),
                        };
                        let _ = write!(text, " = {value}");
                    }
                    None => text.push_str(" = default"),
                }
            }
            texts.push(text);
        }
        texts.join(", ")
    }

    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn method(
        &mut self,
        type_row: u32,
        type_name: &str,
        kind: Kind,
        method_row: u32,
        method: Row<'_>,
        body: Option<&Decompiled>,
        type_generics: &Generics,
    ) {
        let heaps = self.resolver.assembly.heaps();
        let name = heaps.string(method.number(3)).to_string();
        let flags = method.number(2);
        let impl_flags = method.number(1);
        let Some(sig) = self.resolver.method_sig_at(method.number(4)) else {
            return;
        };
        let generics = Generics {
            type_params: type_generics.type_params.clone(),
            method_params: self.resolver.generic_param_names(true, method_row),
        };
        let method_token = Token::new(table::METHOD_DEF, method_row);
        self.attributes(method_token, &generics);
        let written = if name == ".ctor" || name == ".cctor" {
            type_name.to_owned()
        } else {
            name.clone()
        };
        self.declare(&written, written.clone(), method_token, false);

        let mut header = String::new();
        let is_static = flags & 0x0010 != 0;
        let explicit = self.explicit_implementation(type_row, method_row, &generics);
        if explicit.is_none() && (kind != Kind::Interface || flags & 0x7 != 6) {
            header.push_str(member_visibility(flags & 0x7));
            header.push(' ');
        }
        if is_static {
            header.push_str("static ");
        }
        if explicit.is_none() {
            header.push_str(&virtual_modifiers(flags, kind, name == "Finalize"));
        }
        if method.number(0) == 0 && flags & 0x2000 != 0 {
            header.push_str("extern ");
        }
        if impl_flags & 0x0020 != 0 && name != ".ctor" && name != ".cctor" {
            header.push_str("/* synchronized */ ");
        }
        if is_unsafe_type(&sig.returns)
            || sig.parameters.iter().any(is_unsafe_type)
            || body.is_some_and(body_is_unsafe)
        {
            header.push_str("unsafe ");
        }
        if body.is_some_and(|body| body.is_async) {
            header.push_str("async ");
        }
        if self.resolver.has_attribute(
            method_token,
            "System.Runtime.CompilerServices.IsReadOnlyAttribute",
        ) && kind == Kind::Struct
        {
            header.push_str("readonly ");
        }

        let params = self.parameters(method_row, &sig, &generics);
        let return_row = self.return_param(method_row);
        let mut return_annotations = return_row
            .map(|token| self.annotations_of(token, Some(method_row), type_row))
            .unwrap_or_else(|| self.annotations_of(Token(0), Some(method_row), type_row));
        let returns = if sig.returns_required.iter().any(|token| {
            self.resolver.raw_name(*token).as_deref()
                == Some("System.Runtime.InteropServices.InAttribute")
        }) {
            match &sig.returns {
                TypeSig::ByRef(inner) => format!(
                    "ref readonly {}",
                    self.tn_annotated(inner, &generics, &mut return_annotations)
                ),
                other => self.tn_annotated(other, &generics, &mut return_annotations),
            }
        } else {
            self.tn_annotated(&sig.returns, &generics, &mut return_annotations)
        };
        if name == ".ctor" {
            let _ = write!(header, "{type_name}({params})");
        } else if name == ".cctor" {
            let unsafe_ = if header.contains("unsafe ") {
                "unsafe "
            } else {
                ""
            };
            header = format!("static {unsafe_}{type_name}()");
        } else if name == "Finalize" && sig.parameters.is_empty() && flags & 0x0040 != 0 {
            header = format!("~{type_name}()");
        } else if let Some(operator) = name.strip_prefix("op_")
            && is_static
            && let Some(symbol) = operator_symbol(operator)
        {
            match operator {
                "Implicit" | "Explicit" => {
                    let _ = write!(header, "{symbol} operator {returns}({params})");
                }
                _ => {
                    let _ = write!(header, "{returns} operator {symbol}({params})");
                }
            }
        } else {
            let shown = match &explicit {
                Some((interface, member)) => format!("{interface}.{member}"),
                None => escape_name(&name),
            };
            let _ = write!(
                header,
                "{returns} {shown}{}({params})",
                self.type_params(&generics.method_params)
            );
        }
        // An override or an explicit implementation takes its constraints
        // from the method it implements, and may not say them again.
        if !(header.contains("override ") || explicit.is_some()) {
            header.push_str(&self.constraints(true, method_row, &generics));
        }

        // `: base(...)` / `: this(...)` on a constructor.
        let mut stmts: Vec<Stmt> = body.map(|body| body.stmts.clone()).unwrap_or_default();
        if name == ".ctor"
            && let Some(body) = body
            && let Some(position) = stmts
                .iter()
                .position(|stmt| matches!(stmt, Stmt::Expr(Expr::Call { method, receiver: Some(receiver), .. }) if method.is_constructor() && **receiver == Expr::This))
        {
            let Stmt::Expr(Expr::Call {
                method: ctor,
                mut args,
                ..
            }) = stmts.remove(position)
            else {
                unreachable!()
            };
            // What the arguments were worked out in, before the call, goes
            // into them: nothing can come before `: this(...)`.
            let mut at = position;
            while at > 0 {
                at -= 1;
                let (variable, value) = match &stmts[at] {
                    Stmt::Expr(Expr::Assign(target, value))
                        if matches!(target.as_ref(), Expr::Local(_) | Expr::Slot(_)) =>
                    {
                        ((**target).clone(), value.as_ref())
                    }
                    Stmt::Declare {
                        local,
                        value: Some(value),
                    } => (Expr::Local(*local), value),
                    _ => break,
                };
                let is_local = |e: &Expr| *e == variable;
                let in_args: usize = args.iter().map(|arg| arg.count(&is_local)).sum();
                let elsewhere: usize = stmts
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| *index != at)
                    .map(|(_, stmt)| crate::simplify::count_in_stmt_deep(stmt, &is_local))
                    .sum();
                if in_args != 1 || elsewhere != 0 {
                    break;
                }
                let value = value.clone();
                for arg in &mut args {
                    arg.map(&mut |e| {
                        if *e == variable {
                            *e = value.clone();
                        }
                    });
                }
                stmts.remove(at);
            }
            let is_this = ctor.declaring == self.resolver.declared_type_sig(type_row)
                || matches!((&ctor.declaring, self.resolver.declared_type_sig(type_row)), (TypeSig::Generic { definition: a, .. }, TypeSig::Generic { definition: b, .. }) if a == &Box::new((*b).clone()));
            let base_is_object = matches!(&ctor.declaring, TypeSig::Class(token) if self.resolver.raw_name(*token).as_deref() == Some("System.Object"));
            let implied = args.is_empty() && (base_is_object || !is_this);
            if !implied {
                let printer = body.printer();
                let call = printer.expression(&Expr::Call {
                    method: ctor.clone(),
                    receiver: None,
                    args,
                });
                // The callee's name has no parentheses and the arguments
                // may: `(TextureFormat)format` is an argument too.
                let arguments = call.split_once('(').map_or(String::new(), |(_, rest)| {
                    rest.strip_suffix(')').unwrap_or(rest).to_string()
                });
                let keyword = if is_this { "this" } else { "base" };
                let _ = write!(header, " : {keyword}({arguments})");
            }
        }

        match body {
            None => {
                header.push(';');
                self.line(&header);
            }
            Some(body) => {
                self.line(&header);
                self.line("{");
                let text = body.printer().body(&stmts, self.indent + 1);
                self.out.push_str(&text);
                self.line("}");
            }
        }
    }

    /// `IFoo.Bar` when the method implements an interface member explicitly.
    fn explicit_implementation(
        &self,
        type_row: u32,
        method_row: u32,
        generics: &Generics,
    ) -> Option<(String, String)> {
        let heaps = self.resolver.assembly.heaps();
        for (body, declaration) in self.resolver.method_impls_of(type_row) {
            if body.table() != table::METHOD_DEF || body.row() != method_row {
                continue;
            }
            let (interface, member) = match declaration.table() {
                table::METHOD_DEF => {
                    let owner = self.resolver.method_owner(declaration.row())?;
                    let found = self.resolver.assembly.row(declaration)?;
                    (
                        self.resolver
                            .type_name(&self.resolver.declared_type_sig(owner), generics),
                        heaps.string(found.number(3)).to_string(),
                    )
                }
                table::MEMBER_REF => {
                    let found = self.resolver.assembly.row(declaration)?;
                    (
                        self.resolver
                            .type_name(&self.resolver.token_sig(found.token(0)), generics),
                        heaps.string(found.number(1)).to_string(),
                    )
                }
                _ => continue,
            };
            // Only an explicit implementation has the mangled name.
            let name = heaps.string(
                self.resolver
                    .assembly
                    .table(table::METHOD_DEF)
                    .row(method_row)?
                    .number(3),
            );
            if name.contains('.') {
                return Some((interface, member));
            }
        }
        None
    }

    fn properties_of(&self, type_row: u32) -> Vec<PropertyInfo> {
        let heaps = self.resolver.assembly.heaps();
        let Some((start, end)) = self.resolver.property_range(type_row) else {
            return Vec::new();
        };
        let properties = self.resolver.assembly.table(table::PROPERTY);
        let mut out = Vec::new();
        for number in start..end {
            let Some(row) = properties.row(number) else {
                continue;
            };
            let token = Token::new(table::PROPERTY, number);
            let Ok(bytes) = heaps.blob(row.number(2)) else {
                continue;
            };
            let Ok(sig) = Blob::new(bytes).property_sig() else {
                continue;
            };
            let mut getter = None;
            let mut setter = None;
            for (semantics, method_row) in self.resolver.semantics_of(token) {
                if semantics & 0x02 != 0 {
                    getter = Some(method_row);
                }
                if semantics & 0x01 != 0 {
                    setter = Some(method_row);
                }
            }
            let name = heaps.string(row.number(1)).to_string();
            let auto_backing = match getter {
                Some(getter) => auto_getter_backing(self.resolver, getter).filter(|backing| {
                    setter.is_none_or(|row| {
                        auto_setter_backing(self.resolver, row).as_deref() == Some(backing.as_str())
                    })
                }),
                // A getter trimmed away: C# has no auto-property without one,
                // so it is written back.
                None => setter.and_then(|row| auto_setter_backing(self.resolver, row)),
            };
            out.push(PropertyInfo {
                token,
                name,
                sig,
                getter,
                setter,
                auto_backing,
            });
        }
        out
    }

    #[allow(clippy::too_many_lines)]
    fn property(
        &mut self,
        property: &PropertyInfo,
        type_generics: &Generics,
        kind: Kind,
        initializers: &BTreeMap<String, String>,
        filter: Option<&str>,
    ) {
        let heaps = self.resolver.assembly.heaps();
        let accessor = property.getter.or(property.setter);
        let Some(accessor_row) = accessor else {
            return;
        };
        if !self.method_matches(accessor_row, filter) {
            return;
        }
        let Some(method) = self
            .resolver
            .assembly
            .table(table::METHOD_DEF)
            .row(accessor_row)
        else {
            return;
        };
        let flags = method.number(2);
        self.attributes(property.token, type_generics);
        // An indexer goes by `Item` unless it says otherwise.
        if !property.sig.parameters.is_empty()
            && property.name != "Item"
            && !property.name.contains('.')
        {
            self.line(&format!(
                "[System.Runtime.CompilerServices.IndexerName(\"{}\")]",
                property.name
            ));
        }
        self.declare(&property.name, property.name.clone(), property.token, false);
        let mut header = String::new();
        let type_row = self.resolver.method_owner(accessor_row).unwrap_or(0);
        let explicit = self.explicit_implementation(type_row, accessor_row, type_generics);
        if kind != Kind::Interface && explicit.is_none() {
            header.push_str(member_visibility(flags & 0x7));
            header.push(' ');
        }
        if flags & 0x0010 != 0 {
            header.push_str("static ");
        }
        if explicit.is_none() {
            header.push_str(&virtual_modifiers(flags, kind, false));
        }
        if self.resolver.has_attribute(
            property.token,
            "System.Runtime.CompilerServices.RequiredMemberAttribute",
        ) {
            header.push_str("required ");
        }
        // The accessors' bodies, which say whether the property is unsafe.
        let mut bodies: Vec<(u32, Option<Decompiled>)> = [property.getter, property.setter]
            .into_iter()
            .flatten()
            .map(|row| (row, self.unfolded_body(row)))
            .collect();
        if is_unsafe_type(&property.sig.returns)
            || property.sig.parameters.iter().any(is_unsafe_type)
            || bodies
                .iter()
                .any(|(_, body)| body.as_ref().is_some_and(body_is_unsafe))
        {
            header.push_str("unsafe ");
        }
        let returns = self
            .resolver
            .type_name(&property.sig.returns, type_generics);
        let returns = if property.sig.returns_required.iter().any(|token| {
            self.resolver.raw_name(*token).as_deref()
                == Some("System.Runtime.InteropServices.InAttribute")
        }) {
            returns.replacen("ref ", "ref readonly ", 1)
        } else {
            returns
        };
        let is_indexer = !property.sig.parameters.is_empty();
        if is_indexer {
            let params = self.parameters(
                accessor_row,
                &MethodSig {
                    instance: true,
                    arity: 0,
                    returns: TypeSig::Void,
                    returns_required: Vec::new(),
                    parameters: property.sig.parameters.clone(),
                    parameters_required: property.sig.parameters_required.clone(),
                    sentinel: None,
                    returns_modifiers: Vec::new(),
                    parameters_modifiers: property.sig.parameters_modifiers.clone(),
                },
                type_generics,
            );
            let shown = match &explicit {
                Some((interface, _)) => format!("{interface}.this"),
                None => "this".to_string(),
            };
            let _ = write!(header, "{returns} {shown}[{params}]");
        } else {
            let shown = match &explicit {
                // The property's own name is the mangled one, with the
                // interface's in front.
                Some((interface, _)) => format!(
                    "{interface}.{}",
                    property.name.rsplit('.').next().unwrap_or(&property.name)
                ),
                None => escape_name(&property.name),
            };
            let _ = write!(header, "{returns} {shown}");
        }

        if let Some(backing) = &property.auto_backing {
            let mut accessors = String::from(" { get; ");
            if let Some(setter) = property.setter {
                let setter_row = self.resolver.assembly.table(table::METHOD_DEF).row(setter);
                let setter_flags = setter_row.map_or(flags, |row| row.number(2));
                if setter_flags & 0x7 != flags & 0x7 {
                    accessors.push_str(member_visibility(setter_flags & 0x7));
                    accessors.push(' ');
                }
                let is_init = self
                    .resolver
                    .method_sig_at(setter_row.map_or(0, |row| row.number(4)))
                    .is_some_and(|sig| {
                        sig.returns_required.iter().any(|token| {
                            self.resolver.raw_name(*token).as_deref()
                                == Some("System.Runtime.CompilerServices.IsExternalInit")
                        })
                    });
                accessors.push_str(if is_init { "init; " } else { "set; " });
            }
            accessors.push('}');
            header.push_str(&accessors);
            if let Some(initializer) = initializers.get(backing) {
                let _ = write!(header, " = {initializer};");
            }
            self.line(&header);
            return;
        }

        // Accessors with no body at all sit on the property's line.
        let bodiless = [property.getter, property.setter]
            .into_iter()
            .flatten()
            .all(|row| {
                self.resolver
                    .assembly
                    .table(table::METHOD_DEF)
                    .row(row)
                    .is_some_and(|method| method.number(0) == 0)
            });
        if bodiless {
            let mut accessors = String::from(" { ");
            for (label, row) in [("get", property.getter), ("set", property.setter)] {
                let Some(row) = row else {
                    continue;
                };
                let accessor_flags = self
                    .resolver
                    .assembly
                    .table(table::METHOD_DEF)
                    .row(row)
                    .map_or(flags, |method| method.number(2));
                if accessor_flags & 0x7 != flags & 0x7 && kind != Kind::Interface {
                    accessors.push_str(member_visibility(accessor_flags & 0x7));
                    accessors.push(' ');
                }
                accessors.push_str(label);
                accessors.push_str("; ");
            }
            accessors.push('}');
            header.push_str(&accessors);
            self.line(&header);
            return;
        }
        self.line(&header);
        self.line("{");
        self.indent += 1;
        for (label, row) in [("get", property.getter), ("set", property.setter)] {
            let Some(row) = row else {
                continue;
            };
            let Some(method) = self.resolver.assembly.table(table::METHOD_DEF).row(row) else {
                continue;
            };
            let accessor_flags = method.number(2);
            let mut line = String::new();
            if accessor_flags & 0x7 != flags & 0x7 && kind != Kind::Interface {
                line.push_str(member_visibility(accessor_flags & 0x7));
                line.push(' ');
            }
            let is_init = label == "set"
                && self
                    .resolver
                    .method_sig_at(method.number(4))
                    .is_some_and(|sig| {
                        sig.returns_required.iter().any(|token| {
                            self.resolver.raw_name(*token).as_deref()
                                == Some("System.Runtime.CompilerServices.IsExternalInit")
                        })
                    });
            line.push_str(if is_init { "init" } else { label });
            let body = bodies
                .iter()
                .position(|(at, _)| *at == row)
                .and_then(|at| bodies[at].1.take());
            match body {
                None => {
                    line.push(';');
                    self.line(&line);
                }
                Some(body) => {
                    self.line(&line);
                    self.line("{");
                    let text = body.printer().body(&body.stmts, self.indent + 1);
                    self.out.push_str(&text);
                    self.line("}");
                }
            }
        }
        self.indent -= 1;
        self.line("}");
        let _ = heaps;
    }

    /// Whether an `add` accessor is the one the compiler writes for a
    /// field-like event: a `Delegate.Combine` stored back into the field.
    fn is_field_like_add(&self, row: u32, event_name: &str) -> bool {
        let Some(body) = decompile_body(self.resolver, row, &self.options) else {
            return false;
        };
        let mut combines = false;
        let mut stores_field = false;
        for stmt in &body.stmts {
            stmt.walk_exprs(&mut |e| match e {
                Expr::Call { method, .. }
                    if method.name == "Combine" || method.name == "CompareExchange" =>
                {
                    combines = true;
                }
                Expr::Assign(target, _) => {
                    if let Expr::Field { field, .. } = target.as_ref()
                        && field.name == event_name
                    {
                        stores_field = true;
                    }
                }
                _ => {}
            });
        }
        combines && stores_field
    }

    fn events_of(&self, type_row: u32) -> Vec<EventInfo> {
        let heaps = self.resolver.assembly.heaps();
        let Some((start, end)) = self.resolver.event_range(type_row) else {
            return Vec::new();
        };
        let events = self.resolver.assembly.table(table::EVENT);
        let mut out = Vec::new();
        for number in start..end {
            let Some(row) = events.row(number) else {
                continue;
            };
            let token = Token::new(table::EVENT, number);
            let mut add = None;
            let mut remove = None;
            for (semantics, method_row) in self.resolver.semantics_of(token) {
                if semantics & 0x08 != 0 {
                    add = Some(method_row);
                }
                if semantics & 0x10 != 0 {
                    remove = Some(method_row);
                }
            }
            out.push(EventInfo {
                token,
                name: heaps.string(row.number(1)).to_string(),
                ty: self.resolver.token_sig(row.token(2)),
                add,
                remove,
            });
        }
        out
    }

    fn event(&mut self, event: &EventInfo, generics: &Generics, kind: Kind, filter: Option<&str>) {
        let Some(accessor_row) = event.add.or(event.remove) else {
            return;
        };
        if !self.method_matches(accessor_row, filter) {
            return;
        }
        let Some(method) = self
            .resolver
            .assembly
            .table(table::METHOD_DEF)
            .row(accessor_row)
        else {
            return;
        };
        let flags = method.number(2);
        self.attributes(event.token, generics);
        self.declare(&event.name, event.name.clone(), event.token, false);
        let mut header = String::new();
        let type_row = self.resolver.method_owner(accessor_row).unwrap_or(0);
        let explicit = self.explicit_implementation(type_row, accessor_row, generics);
        if kind != Kind::Interface && explicit.is_none() {
            header.push_str(member_visibility(flags & 0x7));
            header.push(' ');
        }
        if flags & 0x0010 != 0 {
            header.push_str("static ");
        }
        if explicit.is_none() {
            header.push_str(&virtual_modifiers(flags, kind, false));
        }
        // An explicit implementation is named by the interface, and has its
        // accessors written out.
        let shown = match &explicit {
            Some((interface, _)) => format!(
                "{interface}.{}",
                event.name.rsplit('.').next().unwrap_or(&event.name)
            ),
            None => escape_name(&event.name),
        };
        let _ = write!(header, "event {} {shown}", self.tn(&event.ty, generics));
        let generated = explicit.is_none()
            && (self.resolver.has_attribute(
                Token::new(table::METHOD_DEF, accessor_row),
                "System.Runtime.CompilerServices.CompilerGeneratedAttribute",
            ) || event
                .add
                .is_some_and(|row| self.is_field_like_add(row, &event.name)));
        if generated || kind == Kind::Interface {
            header.push(';');
            self.line(&header);
            return;
        }
        self.line(&header);
        self.line("{");
        self.indent += 1;
        for (label, row) in [("add", event.add), ("remove", event.remove)] {
            let Some(row) = row else {
                continue;
            };
            let body = decompile_body(self.resolver, row, &self.options);
            match body {
                None => self.line(&format!("{label};")),
                Some(body) => {
                    self.line(label);
                    self.line("{");
                    let text = body.printer().body(&body.stmts, self.indent + 1);
                    self.out.push_str(&text);
                    self.line("}");
                }
            }
        }
        self.indent -= 1;
        self.line("}");
    }
}

/// What of a record the compiler wrote and its header says instead.
#[derive(Debug, Default)]
struct RecordShape {
    /// Whether it is a record, rather than a class or struct with a
    /// primary constructor.
    record: bool,
    positional: Option<RecordPositional>,
    hidden_methods: HashSet<u32>,
    hidden_properties: HashSet<String>,
    /// The fields a primary constructor's captured parameters live in.
    hidden_fields: HashSet<String>,
    /// Initialisers that read the primary constructor's parameters, by the
    /// field (or backing field) they set.
    initializers: Vec<(String, String)>,
}

#[derive(Debug)]
struct RecordPositional {
    /// The primary constructor's parameters, as a parameter list.
    params: String,
    /// What the primary constructor passes its base, when anything.
    base_arguments: Option<String>,
}

struct PropertyInfo {
    token: Token,
    name: String,
    sig: MethodSig,
    getter: Option<u32>,
    setter: Option<u32>,
    /// The backing field, when both accessors are the trivial ones.
    auto_backing: Option<String>,
}

struct EventInfo {
    token: Token,
    name: String,
    ty: TypeSig,
    add: Option<u32>,
    remove: Option<u32>,
}

/// The backing field a trivial getter reads: `ldarg.0; ldfld F; ret`.
fn auto_getter_backing(resolver: Resolver<'_>, method_row: u32) -> Option<String> {
    let instructions = crate::instructions_of(resolver, method_row)?;
    let names: Vec<&str> = instructions.iter().map(|i| i.name).collect();
    let field_at = match names.as_slice() {
        ["ldarg.0", "ldfld", "ret"] => 1,
        ["ldsfld", "ret"] => 0,
        _ => return None,
    };
    let rustlyn_metadata::body::Value::Token(token) = instructions[field_at].value else {
        return None;
    };
    let field = resolver.field_ref(token)?;
    field
        .name
        .ends_with("k__BackingField")
        .then_some(field.name)
}

/// The backing field a trivial setter writes.
fn auto_setter_backing(resolver: Resolver<'_>, method_row: u32) -> Option<String> {
    let instructions = crate::instructions_of(resolver, method_row)?;
    let names: Vec<&str> = instructions.iter().map(|i| i.name).collect();
    let field_at = match names.as_slice() {
        ["ldarg.0", "ldarg.1", "stfld", "ret"] => 2,
        ["ldarg.0", "stsfld", "ret"] => 1,
        _ => return None,
    };
    let rustlyn_metadata::body::Value::Token(token) = instructions[field_at].value else {
        return None;
    };
    let field = resolver.field_ref(token)?;
    field
        .name
        .ends_with("k__BackingField")
        .then_some(field.name)
}

/// Takes the field initialisers out of a constructor: the assignments to
/// this type's fields before the base constructor call, and everything in
/// a static constructor that only sets static fields.
fn lift_field_initializers(
    body: &mut Decompiled,
    is_static: bool,
    type_row: u32,
) -> Vec<(String, String)> {
    let mut lifted = Vec::new();
    let base_call = body.stmts.iter().position(|stmt| {
        matches!(stmt, Stmt::Expr(Expr::Call { method, receiver: Some(receiver), .. }) if method.is_constructor() && **receiver == Expr::This)
    });
    let limit = if is_static {
        body.stmts.len()
    } else {
        match base_call {
            Some(at) => at,
            None => return lifted,
        }
    };
    let mut keep = Vec::new();
    let mut taken = 0;
    for (index, stmt) in body.stmts.iter().enumerate() {
        if index >= limit {
            keep.push(stmt.clone());
            continue;
        }
        let Stmt::Expr(Expr::Assign(target, value)) = stmt else {
            if is_static {
                // A static constructor doing anything else stays.
                return Vec::new();
            }
            keep.push(stmt.clone());
            continue;
        };
        let Expr::Field { receiver, field } = target.as_ref() else {
            if is_static {
                return Vec::new();
            }
            keep.push(stmt.clone());
            continue;
        };
        // A generic type's own fields are reached through a `MemberRef` on
        // its instantiation over its own parameters.
        let declared_here = match &field.declaring {
            TypeSig::Class(token) | TypeSig::ValueType(token) => Some(*token),
            TypeSig::Generic { definition, .. } => match definition.as_ref() {
                TypeSig::Class(token) | TypeSig::ValueType(token) => Some(*token),
                _ => None,
            },
            _ => None,
        } == Some(Token::new(table::TYPE_DEF, type_row));
        let own = if field.token.table() == table::FIELD {
            body.resolver_field_owner(field.token) == Some(type_row)
        } else {
            declared_here
        };
        let receiver_ok = if is_static {
            receiver.is_none()
        } else {
            matches!(receiver.as_deref(), Some(Expr::This))
        };
        let mentions_args =
            value.count(&|e| matches!(e, Expr::Arg(_) | Expr::Local(_) | Expr::Slot(_))) > 0
                || (!is_static && value.count(&|e| matches!(e, Expr::This)) > 0);
        if !(own && receiver_ok && !mentions_args) {
            if is_static {
                return Vec::new();
            }
            keep.push(stmt.clone());
            continue;
        }
        let text = body.printer().expression(value);
        lifted.push((field.name.clone(), text));
        taken += 1;
    }
    if taken > 0 {
        body.stmts = keep;
    }
    let _ = &mut body.base_call_is_trivial;
    lifted
}

/// Whether a constructor is the one the compiler would have written: no
/// parameters, only the base call left in it.
fn is_default_ctor(methods: &[(u32, Row<'_>)], method_row: u32, resolver: Resolver<'_>) -> bool {
    let Some((_, method)) = methods.iter().find(|(row, _)| *row == method_row) else {
        return false;
    };
    // C# writes one only where no constructor is declared.
    let heaps = resolver.assembly.heaps();
    let constructors = methods
        .iter()
        .filter(|(_, other)| heaps.string(other.number(3)) == ".ctor")
        .count();
    if constructors > 1 {
        return false;
    }
    let public = method.number(2) & 0x7 == 6;
    resolver
        .method_sig_at(method.number(4))
        .is_some_and(|sig| sig.parameters.is_empty())
        && public
}

/// `Name` out of `Ns.Outer+Name, Assembly, Version=...`.
fn serialized_type_name(name: &str) -> String {
    let bare = name.split(',').next().unwrap_or(name).trim();
    let bare = bare.split('[').next().unwrap_or(bare);
    let last = bare.rsplit(['.', '+']).next().unwrap_or(bare);
    crate::names::strip_arity(last).to_string()
}

/// Whether a body can only be written in an `unsafe` context: it has
/// pointers in its variables or its expressions.
fn body_is_unsafe(body: &Decompiled) -> bool {
    body.ctx.locals.iter().any(is_unsafe_type)
        || body.stmts.iter().any(|stmt| {
            let mut found = false;
            stmt.walk_exprs(&mut |e| {
                found |= match e {
                    // `stackalloc` into a span is safe, but the escape rules
                    // relax in an unsafe context, which an async method may
                    // not be: there only a pointer's variable says so.
                    Expr::StackAlloc(..) => !body.is_async,
                    Expr::Cast(TypeSig::Pointer(_), _)
                    | Expr::SizeOf(TypeSig::ValueType(_) | TypeSig::Var(_) | TypeSig::MVar(_)) => {
                        true
                    }
                    Expr::Cast(TypeSig::IntPtr | TypeSig::UIntPtr, inner) => {
                        matches!(inner.as_ref(), Expr::Unary(crate::ir::UnOp::AddressOf, _))
                    }
                    Expr::Field { field, .. } => {
                        is_unsafe_type(&field.ty)
                            // An element of a `fixed` buffer.
                            || body.ctx.resolver.fixed_buffer_element(&field.ty).is_some()
                    }
                    Expr::Call { method, .. } => {
                        is_unsafe_type(&method.sig.returns)
                            || method.sig.parameters.iter().any(is_unsafe_type)
                    }
                    Expr::Property { ty: Some(ty), .. } => is_unsafe_type(ty),
                    _ => false,
                };
            });
            found
        })
}

/// Whether a type can only be written in an `unsafe` context.
fn is_unsafe_type(ty: &TypeSig) -> bool {
    match ty {
        TypeSig::Pointer(_) | TypeSig::FunctionPointer(_) => true,
        TypeSig::Vector(inner) | TypeSig::ByRef(inner) => is_unsafe_type(inner),
        TypeSig::Array { element, .. } => is_unsafe_type(element),
        TypeSig::Generic { arguments, .. } => arguments.iter().any(is_unsafe_type),
        _ => false,
    }
}

fn type_visibility(flags: u32) -> &'static str {
    match flags & 0x7 {
        0 => "internal",
        1 | 2 => "public",
        3 => "private",
        4 => "protected",
        5 => "internal",
        6 => "private protected",
        _ => "protected internal",
    }
}

fn member_visibility(flags: u32) -> &'static str {
    match flags {
        1 => "private",
        2 => "private protected",
        3 => "internal",
        4 => "protected",
        5 => "protected internal",
        6 => "public",
        _ => "private",
    }
}

/// `virtual`, `override`, `abstract`, `sealed override`, `new`.
fn virtual_modifiers(flags: u32, kind: Kind, is_finalizer: bool) -> String {
    if kind == Kind::Interface {
        let is_static = flags & 0x0010 != 0;
        let is_abstract = flags & 0x0400 != 0;
        let is_virtual = flags & 0x0040 != 0;
        return match (is_static, is_abstract, is_virtual) {
            // `static abstract` and `static virtual`, C# 11's.
            (true, true, _) => "abstract ".into(),
            (true, false, true) => "virtual ".into(),
            // A body that nothing overrides.
            (false, false, false) if flags & 0x7 == 6 => "sealed ".into(),
            _ => String::new(),
        };
    }
    if is_finalizer {
        return String::new();
    }
    let is_virtual = flags & 0x0040 != 0;
    let is_abstract = flags & 0x0400 != 0;
    let new_slot = flags & 0x0100 != 0;
    let is_final = flags & 0x0020 != 0;
    let mut out = String::new();
    if is_abstract {
        if !new_slot {
            out.push_str("override ");
        }
        out.push_str("abstract ");
        return out;
    }
    if !is_virtual {
        return out;
    }
    if new_slot {
        if !is_final {
            out.push_str("virtual ");
        }
    } else {
        if is_final {
            out.push_str("sealed ");
        }
        out.push_str("override ");
    }
    out
}

fn operator_symbol(name: &str) -> Option<&'static str> {
    Some(match name {
        "Addition" => "+",
        "Subtraction" => "-",
        "Multiply" => "*",
        "Division" => "/",
        "Modulus" => "%",
        "BitwiseAnd" => "&",
        "BitwiseOr" => "|",
        "ExclusiveOr" => "^",
        "LeftShift" => "<<",
        "RightShift" => ">>",
        "UnsignedRightShift" => ">>>",
        "Equality" => "==",
        "Inequality" => "!=",
        "LessThan" => "<",
        "LessThanOrEqual" => "<=",
        "GreaterThan" => ">",
        "GreaterThanOrEqual" => ">=",
        "UnaryNegation" => "-",
        "UnaryPlus" => "+",
        "LogicalNot" => "!",
        "OnesComplement" => "~",
        "Increment" => "++",
        "Decrement" => "--",
        "True" => "true",
        "False" => "false",
        "Implicit" => "implicit",
        "Explicit" => "explicit",
        _ => return None,
    })
}

/// A constant as C# writes it.
pub(crate) fn constant_text(constant: &Constant) -> String {
    match constant {
        Constant::Bool(value) => value.to_string(),
        Constant::Char(c) => {
            let mut printer_text = String::new();
            let _ = write!(
                printer_text,
                "{}",
                crate::print::expr_text_free(&Expr::Char(*c))
            );
            printer_text
        }
        Constant::Int(value) => value.to_string(),
        Constant::Float(value, single) => {
            crate::print::expr_text_free(&Expr::Float(*value, *single))
        }
        Constant::Str(text) => crate::print::expr_text_free(&Expr::Str(text.clone())),
        Constant::Null => "null".to_string(),
    }
}

/// A name the compiler made up: display classes, state machines, lambdas.
pub(crate) fn is_compiler_generated_name(name: &str) -> bool {
    name.starts_with('<') && name != "<Main>$"
}

/// Where `name` is in a declaration's header line.
///
/// A type's name is its first whole-word occurrence: whatever follows it —
/// bases, constraints — may repeat it, but nothing before it does. A
/// member's is the last one before its parameters, accessors or
/// initializer, since its type comes first and may share the name
/// (`Color Color`).
fn name_in_header(text: &str, name: &str, is_type: bool) -> Option<usize> {
    if name.is_empty() {
        return None;
    }
    let is_word = |ch: char| ch.is_alphanumeric() || ch == '_';
    let occurrences = text.match_indices(name).map(|(at, _)| at).filter(|&at| {
        !text[..at].chars().next_back().is_some_and(is_word)
            && !text[at + name.len()..].chars().next().is_some_and(is_word)
    });
    if is_type {
        return occurrences.into_iter().next();
    }
    // The tail: a parameter list (a `(` right after a name or `>`), an
    // accessor block, an initializer or the end.
    let bytes = text.as_bytes();
    let tail = text
        .char_indices()
        .find(|&(at, ch)| {
            (ch == '(' && at > 0 && (is_word(bytes[at - 1] as char) || bytes[at - 1] == b'>'))
                || text[at..].starts_with(" {")
                || text[at..].starts_with(" =")
                || ch == ';'
        })
        .map_or(text.len(), |(at, _)| at);
    occurrences.filter(|&at| at < tail).last()
}

impl Writer<'_> {
    /// The element and length of a `fixed` buffer, when `ty` is the struct
    /// the compiler made for one: a single `FixedElementField` of the
    /// element's type, laid out as long as the whole buffer.
    fn fixed_buffer(&self, ty: &TypeSig, generics: &Generics) -> Option<(String, u32)> {
        let TypeSig::ValueType(token) = ty else {
            return None;
        };
        if token.table() != table::TYPE_DEF
            || !self.resolver.raw_name(*token)?.ends_with("e__FixedBuffer")
        {
            return None;
        }
        let heaps = self.resolver.assembly.heaps();
        let (_, element_field) = self.resolver.fields_of(token.row()).into_iter().next()?;
        let element = Blob::new(heaps.blob(element_field.number(2)).ok()?)
            .field_sig()
            .ok()?;
        let element_size = match element {
            TypeSig::Boolean | TypeSig::Byte | TypeSig::SByte => 1,
            TypeSig::Char | TypeSig::Int16 | TypeSig::UInt16 => 2,
            TypeSig::Int32 | TypeSig::UInt32 | TypeSig::Single => 4,
            TypeSig::Int64 | TypeSig::UInt64 | TypeSig::Double => 8,
            _ => return None,
        };
        let size = self
            .resolver
            .assembly
            .table(table::CLASS_LAYOUT)
            .iter()
            .find(|layout| layout.number(2) == token.row())?
            .number(1);
        Some((self.tn(&element, generics), size / element_size))
    }
}

/// The one string argument of an attribute blob: the prolog, a length and
/// the UTF-8 text.
fn attribute_string(blob: &[u8]) -> Option<String> {
    let rest = blob.strip_prefix(&[1, 0])?;
    let (length, skip) = match *rest.first()? {
        byte if byte & 0x80 == 0 => (usize::from(byte), 1),
        byte if byte & 0xC0 == 0x80 => (
            (usize::from(byte & 0x3F) << 8) | usize::from(*rest.get(1)?),
            2,
        ),
        _ => return None,
    };
    let text = rest.get(skip..skip + length)?;
    String::from_utf8(text.to_vec()).ok()
}

fn escape_name(name: &str) -> String {
    if crate::print::is_keyword(name) {
        format!("@{name}")
    } else {
        crate::names::identifier(name).into_owned()
    }
}
