//! Layer 5: code that has no source, on demand.
//!
//! A project depends on assemblies whose source is not in it — the engine's,
//! the framework's, a plugin's — and `⌘B` into one of them has to lead
//! somewhere.
//!
//! **The assembly as C#** is what an open `.dll` shows: every type and
//! member, with its method bodies turned back from IL into statements by
//! `rustlyn-decompile`, and a table of where each declaration is, so a jump
//! lands on its name. `UnityEngine.CoreModule` takes a third of a second,
//! `System.Private.CoreLib` a second and a half.
//!
//! **The surface** — the same declarations from the metadata tables alone,
//! with no bodies — is what is shown when the decompiler cannot write an
//! assembly out, and where the tokens of its methods come from.
//!
//! **A method's IL** is still there for the one method a reader asks about:
//! decoded and printed with its metadata tokens resolved, so a call reads
//! `call System.Console::WriteLine(string)` rather than `call 0x0A000012`.
//! The C# above it is what the IL does, not what somebody wrote; the IL is
//! what is actually there.
//!
//! All of it is cached against the assembly's fingerprint. An assembly is a
//! file that hardly ever changes and is expensive to read, which is the ideal
//! case for a cache that checks before it works.

use std::fmt::Write as _;

use rustlyn_metadata::body::{Handler, Value};
use rustlyn_metadata::signature::{Blob, TypeSig};
use rustlyn_metadata::{Assembly, Body, Token, table};

use crate::cache::Cacheable;
use crate::wire::{Reader, Writer};

/// Why an assembly could not be shown.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Failure {
    /// A PE file with no CLI header: a native library, with no .NET in it.
    NotManaged,
    /// Not a PE file, or one that ends where something was expected.
    Damaged(String),
}

impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotManaged => f.write_str("a native library: there are no .NET metadata in it"),
            Self::Damaged(why) => write!(f, "the assembly could not be read: {why}"),
        }
    }
}

impl std::error::Error for Failure {}

impl From<rustlyn_metadata::Error> for Failure {
    fn from(error: rustlyn_metadata::Error) -> Self {
        match error {
            rustlyn_metadata::Error::NotAnAssembly => Self::NotManaged,
            other => Self::Damaged(other.to_string()),
        }
    }
}

/// Where a declaration sits in the text that was rendered for it.
///
/// The text is a `.cs` file as far as the editor is concerned, so it wants
/// the same things it wants of a real one: an outline, and somewhere for a
/// jump to land.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rendered {
    /// The full name of the type, `Namespace.Outer/Inner` as metadata spells
    /// it, or the method's name inside its type.
    pub name: String,
    /// Where the name is in the rendered text, in bytes.
    pub name_start: u32,
    pub name_length: u32,
    pub line: u32,
    /// The metadata token, so a body can be asked for later without matching
    /// on the name again.
    pub token: u32,
    pub is_type: bool,
}

/// An assembly written out as C#, with no method bodies.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct AssemblySurface {
    /// The assembly's simple name, from its `Assembly` row.
    pub name: String,
    pub text: String,
    /// Every type and member, and where it is in `text`.
    pub declarations: Vec<Rendered>,
}

impl AssemblySurface {
    /// Reads an assembly and writes its surface out.
    ///
    /// # Errors
    ///
    /// Fails when the file is not a PE image, has no CLI header, or ends
    /// early.
    pub fn of(bytes: &[u8], file_name: &str) -> Result<Self, Failure> {
        let assembly = Assembly::read(bytes)?;
        Ok(Printer::new(&assembly, file_name).render())
    }

    /// The assembly as C#, with its method bodies: the IL turned back into
    /// statements by `rustlyn-decompile`.
    ///
    /// `references` are the assemblies it was built against, as far as they
    /// are known; they tell the decompiler what a call into them is — an
    /// extension method, an `out` parameter, a struct. The declarations are
    /// found by reading the C# back, so a jump lands on the same names the
    /// surface would have named, and a method keeps the token that asks for
    /// its IL.
    ///
    /// Falls back to the surface when the decompiler cannot write the
    /// assembly out: a body it does not understand should cost the bodies,
    /// not the declarations.
    ///
    /// # Errors
    ///
    /// The same as [`Self::of`].
    pub fn decompiled(
        bytes: &[u8],
        file_name: &str,
        references: &[Vec<u8>],
    ) -> Result<Self, Failure> {
        let surface = Self::of(bytes, file_name)?;
        let Some((csharp, declared)) = decompile_to_csharp(bytes, references) else {
            return Ok(surface);
        };
        if declared.is_empty() {
            return Ok(surface);
        }
        let header = format!(
            "// {file_name}\n// Decompiled from IL by Rustlyn. Method bodies are what the IL does,\n\
             // written back as C#: names of locals and some shapes differ from the source.\n\n"
        );
        let shift = header.len() as u32;
        let text = header + &csharp;

        // Lines in one pass: the declarations are in the order written.
        let mut declarations = Vec::with_capacity(declared.len());
        let (mut line, mut counted) = (0u32, 0usize);
        for declaration in declared {
            let start = (declaration.start + shift) as usize;
            if start < counted || start > text.len() {
                continue;
            }
            line += text.as_bytes()[counted..start]
                .iter()
                .filter(|&&byte| byte == b'\n')
                .count() as u32;
            counted = start;
            declarations.push(Rendered {
                name: declaration.name,
                name_start: start as u32,
                name_length: declaration.length,
                line,
                token: declaration.token,
                is_type: declaration.is_type,
            });
        }
        Ok(Self {
            name: surface.name,
            text,
            declarations,
        })
    }

    /// The token of the type whose name is `name`, for asking about its
    /// members.
    #[must_use]
    pub fn type_named(&self, name: &str) -> Option<u32> {
        self.declarations
            .iter()
            .find(|declaration| declaration.is_type && declaration.name == name)
            .map(|declaration| declaration.token)
    }
}

/// The decompiler's C# for a whole assembly and where each declaration
/// is in it, or `None` when it gave up.
///
/// It recurses as deep as the expressions it reads, and a long string
/// concatenation is a deep expression: it runs on a thread with a stack to
/// match. A panic there is the decompiler not understanding a body, and is
/// answered with the surface rather than passed on to the editor.
fn decompile_to_csharp(
    bytes: &[u8],
    references: &[Vec<u8>],
) -> Option<(String, Vec<rustlyn_decompile::members::Declared>)> {
    let images: Vec<&[u8]> = references.iter().map(Vec::as_slice).collect();
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("rustlyn-decompile".into())
            .stack_size(256 << 20)
            .spawn_scoped(scope, || {
                let options = rustlyn_decompile::Options {
                    compiler_generated: false,
                    ..rustlyn_decompile::Options::default()
                };
                rustlyn_decompile::decompile_declared(bytes, &images, &options).ok()
            })
            .ok()?
            .join()
            .ok()
            .flatten()
    })
}

/// One method's IL, printed.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct MethodBody {
    /// `Namespace.Type::Method`.
    pub name: String,
    pub text: String,
    /// How many instructions it decoded to, which is the honest measure of
    /// how much is here.
    pub instructions: u32,
    /// True when the method has no body at all: `abstract`, `extern`, or
    /// implemented by the runtime.
    pub is_empty: bool,
}

impl MethodBody {
    /// Decodes and prints the body of one method.
    ///
    /// # Errors
    ///
    /// Fails when the assembly cannot be read. A method with no body is not
    /// a failure — it is a body that says so.
    pub fn of(bytes: &[u8], method_token: u32) -> Result<Self, Failure> {
        let assembly = Assembly::read(bytes)?;
        let names = Names::new(&assembly);
        let token = Token(method_token);
        let Some(method) = assembly.row(token) else {
            return Err(Failure::Damaged(format!(
                "there is no method at {method_token:#010x}",
            )));
        };
        let name = names.method_name(token);
        let rva = method.number(0);
        if rva == 0 {
            let text = format!(
                "// {name} has no body: it is abstract, extern, or implemented by the runtime.\n",
            );
            return Ok(Self {
                name,
                text,
                instructions: 0,
                is_empty: true,
            });
        }

        let Ok(offset) = assembly.image().offset_of(rva) else {
            return Err(Failure::Damaged(format!(
                "the body address {rva:#x} is in no section"
            )));
        };
        let rest = &assembly.image().bytes()[offset as usize..];
        let body = Body::read(rest).map_err(Failure::from)?;
        let text = print_body(&body, &names, &name);
        Ok(Self {
            name,
            instructions: body.instructions.len() as u32,
            text,
            is_empty: false,
        })
    }
}

// MARK: - the surface

struct Printer<'a> {
    assembly: &'a Assembly<'a>,
    names: Names<'a>,
    file_name: String,
    out: String,
    declarations: Vec<Rendered>,
    line: u32,
}

impl<'a> Printer<'a> {
    fn new(assembly: &'a Assembly<'a>, file_name: &str) -> Self {
        Self {
            assembly,
            names: Names::new(assembly),
            file_name: file_name.to_owned(),
            out: String::new(),
            declarations: Vec::new(),
            line: 0,
        }
    }

    fn render(mut self) -> AssemblySurface {
        let name = self.names.assembly_name();
        self.header(&name);

        // Grouped by namespace rather than written out in table order: an
        // assembly's types arrive in whatever order they were compiled, and
        // one `namespace` block per type would be correct C# and unreadable.
        let types = self.assembly.table(table::TYPE_DEF);
        let mut groups: Vec<(String, Vec<Token>)> = Vec::new();
        for number in 1..=types.len() {
            let token = Token::new(table::TYPE_DEF, number);
            // Row one is `<Module>`, the holder for free functions, which is
            // not a type anybody wants to read.
            if number == 1 && self.names.simple_name(token).starts_with("<Module>") {
                continue;
            }
            // A nested type is printed inside the one it is nested in, so it
            // is skipped when the loop reaches it on its own.
            if self.names.enclosing(token).is_some() {
                continue;
            }
            let namespace = self.names.namespace(token);
            match groups.iter_mut().find(|(name, _)| *name == namespace) {
                Some((_, tokens)) => tokens.push(token),
                None => groups.push((namespace, vec![token])),
            }
        }
        groups.sort_by(|(a, _), (b, _)| a.cmp(b));

        for (namespace, tokens) in groups {
            if !namespace.is_empty() {
                self.write(&format!("namespace {namespace}\n{{\n"));
            }
            // Inside `namespace Game`, a `Game.IThing` is just `IThing`:
            // the source this stands in for would have said so.
            self.names.current_namespace = namespace.clone();
            for token in tokens {
                self.type_declaration(token, usize::from(!namespace.is_empty()));
            }
            self.names.current_namespace.clear();
            if namespace.is_empty() {
                self.write("\n");
            } else {
                self.write("}\n\n");
            }
        }

        AssemblySurface {
            name,
            text: self.out,
            declarations: self.declarations,
        }
    }

    fn header(&mut self, name: &str) {
        // The same line a language server writes at the top of a decompiled
        // file, so an editor that already recognises one recognises this.
        let version = self.names.assembly_version();
        self.write(&format!("#region Assembly {name}, Version={version}\n"));
        self.write(&format!("// {}\n", self.file_name));
        self.write("#endregion\n\n");
        self.write("// Read from the metadata tables. Method bodies are IL and\n");
        self.write("// are shown one at a time, when you ask for one.\n\n");
    }

    fn write(&mut self, text: &str) {
        self.line += text.bytes().filter(|&byte| byte == b'\n').count() as u32;
        self.out.push_str(text);
    }

    /// Writes `text`, and records that `name` inside it is a declaration.
    fn write_named(&mut self, before: &str, name: &str, after: &str, token: Token, is_type: bool) {
        let line = self.line;
        self.write(before);
        let name_start = self.out.len() as u32;
        self.write(name);
        self.declarations.push(Rendered {
            name: if is_type {
                self.names.type_name(token)
            } else {
                name.to_owned()
            },
            name_start,
            name_length: name.len() as u32,
            line,
            token: token.0,
            is_type,
        });
        self.write(after);
    }

    fn type_declaration(&mut self, token: Token, depth: usize) {
        let Some(row) = self.assembly.row(token) else {
            return;
        };
        let flags = row.number(0);
        let indent = "    ".repeat(depth);
        let name = self.names.simple_name(token);

        let keyword = type_keyword(flags, &self.names, token);
        // `Stash\u{60}1` in metadata is `Stash` in C#; the arity is spelled
        // by the parameters, and the suffix is not something anybody typed.
        let name = name
            .split_once('`')
            .map_or(name.clone(), |(head, _)| head.to_owned());
        let head = format!("{indent}{} {keyword} ", accessibility(flags, depth > 0));
        let bases = self.names.bases(token);
        let tail = if bases.is_empty() {
            format!("\n{indent}{{\n")
        } else {
            format!(" : {}\n{indent}{{\n", bases.join(", "))
        };
        self.write_named(&head, &name, &tail, token, true);

        let inner = format!("{indent}    ");
        if keyword == "enum" {
            self.enum_members(token, &inner);
            self.write(&format!("{indent}}}\n"));
            return;
        }
        for field in self.names.fields_of(token) {
            self.field(field, &inner);
        }
        for method in self.names.methods_of(token) {
            self.method(method, &inner, &name);
        }
        for nested in self.names.nested_in(token) {
            self.type_declaration(nested, depth + 1);
        }

        self.write(&format!("{indent}}}\n"));
    }

    /// An enum's members, with the values metadata gave them.
    ///
    /// Every enum carries a hidden instance field called `value__` holding
    /// its underlying type; the members are the static literal fields beside
    /// it, and their values live in the `Constant` table.
    fn enum_members(&mut self, token: Token, indent: &str) {
        for field in self.names.fields_of(token) {
            let Some(row) = self.assembly.row(field) else {
                continue;
            };
            // Static and literal: that is what tells a member from `value__`.
            if row.number(0) & 0x0050 != 0x0050 {
                continue;
            }
            let name = self.names.simple_name(field);
            let tail = match self.names.constant_of(field) {
                Some(value) => format!(" = {value},\n"),
                None => ",\n".to_owned(),
            };
            self.write_named(indent, &name, &tail, field, false);
        }
    }

    fn field(&mut self, token: Token, indent: &str) {
        let Some(row) = self.assembly.row(token) else {
            return;
        };
        let flags = row.number(0);
        // Private fields are an implementation detail of something whose
        // implementation is not here.
        if flags & 0x07 < 0x04 {
            return;
        }
        let name = self.names.simple_name(token);
        let type_text = self.names.field_type(token);
        let modifiers = if flags & 0x0010 != 0 { "static " } else { "" };
        self.write_named(
            &format!(
                "{indent}{} {modifiers}{type_text} ",
                accessibility_of_member(flags)
            ),
            &name,
            ";\n",
            token,
            false,
        );
    }

    fn method(&mut self, token: Token, indent: &str, owner: &str) {
        let Some(row) = self.assembly.row(token) else {
            return;
        };
        let flags = row.number(2);
        if flags & 0x07 < 0x04 {
            return;
        }
        let name = self.names.simple_name(token);
        let (return_type, parameters) = self.names.signature_of(token);
        let mut modifiers = String::new();
        if flags & 0x0010 != 0 {
            modifiers.push_str("static ");
        }
        if flags & 0x0400 != 0 {
            modifiers.push_str("abstract ");
        } else if flags & 0x0040 != 0 {
            modifiers.push_str("virtual ");
        }

        // Metadata calls a constructor `.ctor` and gives it a `void` return;
        // C# writes it as the type's own name with no return at all.
        let head = if name == ".ctor" || name == ".cctor" {
            format!("{indent}{} {modifiers}", accessibility_of_member(flags))
        } else {
            format!(
                "{indent}{} {modifiers}{return_type} ",
                accessibility_of_member(flags)
            )
        };
        let written = if name == ".ctor" || name == ".cctor" {
            owner.to_owned()
        } else {
            name.clone()
        };
        self.write_named(&head, &written, &format!("({parameters});\n"), token, false);
    }
}

/// Resolving tokens to the names a reader knows things by.
struct Names<'a> {
    assembly: &'a Assembly<'a>,
    /// The namespace being written out, whose own names need no prefix.
    current_namespace: String,
}

impl<'a> Names<'a> {
    fn new(assembly: &'a Assembly<'a>) -> Self {
        Self {
            assembly,
            current_namespace: String::new(),
        }
    }

    /// A type name as it would be written here: without the namespace the
    /// surrounding code is already in, and without one a `using` would cover.
    fn written(&self, full: &str) -> String {
        if !self.current_namespace.is_empty()
            && let Some(rest) = full.strip_prefix(&self.current_namespace)
            && let Some(rest) = rest.strip_prefix('.')
            && !rest.contains('.')
        {
            return rest.to_owned();
        }
        short(full)
    }

    fn assembly_name(&self) -> String {
        self.assembly.table(table::ASSEMBLY).row(1).map_or_else(
            || "?".to_owned(),
            |row| self.assembly.heaps().string(row.number(7)).to_owned(),
        )
    }

    fn assembly_version(&self) -> String {
        self.assembly.table(table::ASSEMBLY).row(1).map_or_else(
            || "0.0.0.0".to_owned(),
            |row| {
                format!(
                    "{}.{}.{}.{}",
                    row.number(1),
                    row.number(2),
                    row.number(3),
                    row.number(4)
                )
            },
        )
    }

    /// The name of a row, without its namespace.
    fn simple_name(&self, token: Token) -> String {
        // The column the name sits in, per §II.22: `TypeDef` and `TypeRef`
        // put it after the flags or the scope, `Field` after its flags,
        // `MethodDef` after its address and two sets of flags.
        let column = match token.table() {
            table::TYPE_DEF | table::TYPE_REF | table::FIELD | table::MEMBER_REF => 1,
            table::METHOD_DEF => 3,
            table::PARAM => 2,
            _ => return format!("{token:?}"),
        };
        self.assembly.row(token).map_or_else(String::new, |row| {
            self.assembly.heaps().string(row.number(column)).to_owned()
        })
    }

    fn namespace(&self, token: Token) -> String {
        let column = match token.table() {
            table::TYPE_DEF | table::TYPE_REF => 2,
            _ => return String::new(),
        };
        self.assembly.row(token).map_or_else(String::new, |row| {
            self.assembly.heaps().string(row.number(column)).to_owned()
        })
    }

    /// `Namespace.Outer/Inner`, the way metadata names a type.
    fn type_name(&self, token: Token) -> String {
        let name = self.simple_name(token);
        match self.enclosing(token) {
            Some(outer) => format!("{}/{name}", self.type_name(outer)),
            None => {
                let namespace = self.namespace(token);
                if namespace.is_empty() {
                    name
                } else {
                    format!("{namespace}.{name}")
                }
            }
        }
    }

    /// The type a type is nested in, if any.
    fn enclosing(&self, token: Token) -> Option<Token> {
        if token.table() != table::TYPE_DEF {
            return None;
        }
        self.assembly
            .table(table::NESTED_CLASS)
            .iter()
            .find(|row| row.token(0) == token)
            .map(|row| row.token(1))
    }

    fn nested_in(&self, token: Token) -> Vec<Token> {
        self.assembly
            .table(table::NESTED_CLASS)
            .iter()
            .filter(|row| row.token(1) == token)
            .map(|row| row.token(0))
            .collect()
    }

    /// The rows of a table that belong to one owner.
    ///
    /// Metadata gives an owner the row its members start at and lets the
    /// *next owner* mark where they end, so a list is a range rather than a
    /// search. The owner's own table matters: a type's fields end where the
    /// next type's begin, and a method's parameters where the next method's
    /// do.
    fn range(&self, owner: Token, member_table: u8, column: usize) -> Vec<Token> {
        let owners = self.assembly.table(owner.table());
        let members = self.assembly.table(member_table);
        let Some(row) = self.assembly.row(owner) else {
            return Vec::new();
        };
        let first = row.number(column);
        let next = owners
            .row(owner.row() + 1)
            .map_or(members.len() + 1, |row| row.number(column));
        (first..next)
            .filter(|&number| number >= 1 && number <= members.len())
            .map(|number| Token::new(member_table, number))
            .collect()
    }

    fn fields_of(&self, token: Token) -> Vec<Token> {
        self.range(token, table::FIELD, 4)
    }

    fn methods_of(&self, token: Token) -> Vec<Token> {
        self.range(token, table::METHOD_DEF, 5)
    }

    fn bases(&self, token: Token) -> Vec<String> {
        let mut bases = Vec::new();
        if let Some(row) = self.assembly.row(token) {
            let extends = row.token(3);
            if !extends.is_nil() {
                let name = self.type_name(extends);
                // Everything extends `object`, and a value type or enum
                // extends a name that is noise rather than information.
                if !matches!(
                    name.as_str(),
                    "System.Object" | "System.ValueType" | "System.Enum"
                ) {
                    bases.push(self.written(&name));
                }
            }
        }
        for row in self.assembly.table(table::INTERFACE_IMPL).iter() {
            if row.token(0) == token {
                bases.push(self.written(&self.type_name(row.token(1))));
            }
        }
        bases
    }

    /// The type of a field, from its signature blob.
    fn field_type(&self, token: Token) -> String {
        let Some(row) = self.assembly.row(token) else {
            return "object".into();
        };
        // `Field` is flags, name, signature.
        let Ok(blob) = self.assembly.heaps().blob(row.number(2)) else {
            return "object".into();
        };
        Blob::new(blob).field_sig().map_or_else(
            |_| "object".to_owned(),
            |signature| self.type_text(&signature),
        )
    }

    /// The return type and parameter list of a method, as text.
    fn signature_of(&self, token: Token) -> (String, String) {
        let Some(row) = self.assembly.row(token) else {
            return ("void".into(), String::new());
        };
        let Ok(blob) = self.assembly.heaps().blob(row.number(4)) else {
            return ("void".into(), String::new());
        };
        let Ok(signature) = Blob::new(blob).method_sig() else {
            return ("void".into(), String::new());
        };
        let names = self.parameter_names(token, signature.parameters.len());
        let parameters = signature
            .parameters
            .iter()
            .zip(names)
            .map(|(type_signature, name)| format!("{} {name}", self.type_text(type_signature)))
            .collect::<Vec<_>>()
            .join(", ");
        (self.type_text(&signature.returns), parameters)
    }

    /// A signature type written the way C# writes it.
    ///
    /// A signature names types by token and type parameters by position, so
    /// this is where the tables get consulted. A parameter whose name is not
    /// in this assembly keeps its position (`!0`), because inventing a letter
    /// for it would be inventing information.
    fn type_text(&self, signature: &TypeSig) -> String {
        match signature {
            TypeSig::Void => "void".into(),
            TypeSig::Boolean => "bool".into(),
            TypeSig::Char => "char".into(),
            TypeSig::SByte => "sbyte".into(),
            TypeSig::Byte => "byte".into(),
            TypeSig::Int16 => "short".into(),
            TypeSig::UInt16 => "ushort".into(),
            TypeSig::Int32 => "int".into(),
            TypeSig::UInt32 => "uint".into(),
            TypeSig::Int64 => "long".into(),
            TypeSig::UInt64 => "ulong".into(),
            TypeSig::Single => "float".into(),
            TypeSig::Double => "double".into(),
            TypeSig::String => "string".into(),
            TypeSig::Object => "object".into(),
            TypeSig::IntPtr => "nint".into(),
            TypeSig::UIntPtr => "nuint".into(),
            TypeSig::TypedReference => "typedref".into(),
            TypeSig::Class(token) | TypeSig::ValueType(token) => {
                self.written(&self.type_name(*token))
            }
            TypeSig::Vector(element) => format!("{}[]", self.type_text(element)),
            TypeSig::Array { element, rank } => format!(
                "{}[{}]",
                self.type_text(element),
                ",".repeat((*rank).saturating_sub(1) as usize)
            ),
            TypeSig::Pointer(element) => format!("{}*", self.type_text(element)),
            TypeSig::ByRef(element) => format!("ref {}", self.type_text(element)),
            TypeSig::Var(index) => format!("!{index}"),
            TypeSig::MVar(index) => format!("!!{index}"),
            TypeSig::Generic {
                definition,
                arguments,
            } => {
                let name = self.type_text(definition);
                // `List\`1` in metadata is `List<T>` in C#: the arity is
                // spelled by the arguments, so the suffix is noise.
                let name = name.split_once('`').map_or(name.as_str(), |(head, _)| head);
                format!(
                    "{name}<{}>",
                    arguments
                        .iter()
                        .map(|argument| self.type_text(argument))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeSig::FunctionPointer(_) => "delegate*".into(),
            TypeSig::Unknown(element) => format!("/* element type {element:#04x} */ object"),
        }
    }

    /// A method's parameter names, filled in with positional ones where the
    /// metadata has none.
    fn parameter_names(&self, token: Token, count: usize) -> Vec<String> {
        let mut names: Vec<String> = (0..count).map(|index| format!("arg{index}")).collect();
        for parameter in self.range(token, table::PARAM, 5) {
            let Some(row) = self.assembly.row(parameter) else {
                continue;
            };
            // Sequence zero is the return value, which has no name to give.
            let sequence = row.number(1) as usize;
            if sequence == 0 || sequence > count {
                continue;
            }
            let name = self.assembly.heaps().string(row.number(2));
            if !name.is_empty() {
                names[sequence - 1] = name.to_owned();
            }
        }
        names
    }

    /// The value a `Constant` row gives a field, as text.
    ///
    /// Only the integer shapes an enum can have: this exists so that an
    /// enum's members read as the numbers they are, and anything else would
    /// be guessing at a blob whose type it has not checked.
    fn constant_of(&self, field: Token) -> Option<String> {
        let row = self
            .assembly
            .table(table::CONSTANT)
            .iter()
            .find(|row| row.token(2) == field)?;
        let blob = self.assembly.heaps().blob(row.number(3)).ok()?;
        Some(match row.number(0) as u8 {
            0x04 => i8::from_le_bytes([*blob.first()?]).to_string(),
            0x05 => blob.first()?.to_string(),
            0x06 => i16::from_le_bytes(blob.get(..2)?.try_into().ok()?).to_string(),
            0x07 => u16::from_le_bytes(blob.get(..2)?.try_into().ok()?).to_string(),
            0x08 => i32::from_le_bytes(blob.get(..4)?.try_into().ok()?).to_string(),
            0x09 => u32::from_le_bytes(blob.get(..4)?.try_into().ok()?).to_string(),
            0x0A => i64::from_le_bytes(blob.get(..8)?.try_into().ok()?).to_string(),
            0x0B => u64::from_le_bytes(blob.get(..8)?.try_into().ok()?).to_string(),
            _ => return None,
        })
    }

    /// `Namespace.Type::Method`, which is how IL names a method.
    fn method_name(&self, token: Token) -> String {
        let name = self.simple_name(token);
        // A method belongs to the last type whose method list starts at or
        // before it: metadata gives each type a first row and lets the next
        // type mark the end. Walking forwards and keeping the last match is
        // the same answer as walking backwards, and the table only iterates
        // one way.
        let types = self.assembly.table(table::TYPE_DEF);
        let mut owner = None;
        for number in 1..=types.len() {
            let Some(row) = types.row(number) else {
                continue;
            };
            if row.number(5) <= token.row() {
                owner = Some(Token::new(table::TYPE_DEF, number));
            } else {
                break;
            }
        }
        match owner {
            Some(owner) => format!("{}::{name}", self.type_name(owner)),
            None => name,
        }
    }

    /// What a token in an instruction refers to, for printing beside it.
    fn describe(&self, token: Token) -> String {
        match token.table() {
            table::TYPE_DEF | table::TYPE_REF => self.written(&self.type_name(token)),
            table::FIELD | table::METHOD_DEF => self.method_name(token),
            table::MEMBER_REF => self.assembly.row(token).map_or_else(
                || format!("{token:?}"),
                |row| {
                    let name = self.assembly.heaps().string(row.number(1));
                    let parent = row.token(0);
                    if parent.is_nil() {
                        name.to_owned()
                    } else {
                        format!("{}::{name}", short(&self.type_name(parent)))
                    }
                },
            ),
            // The user string heap, which is where `ldstr` points.
            0x70 => self
                .assembly
                .heaps()
                .user_string(token.row())
                .map_or_else(|_| "\"?\"".to_owned(), |text| format!("{text:?}")),
            _ => format!("{token:?}"),
        }
    }
}

/// Prints one decoded body as IL.
fn print_body(body: &Body, names: &Names<'_>, name: &str) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "// {name}");
    let _ = writeln!(out, "// .maxstack {}", body.max_stack);
    if body.init_locals {
        let _ = writeln!(out, "// .locals init");
    }
    let _ = writeln!(out);

    // Anything branched to gets a label, so a jump reads as a destination
    // rather than as a number to go and count bytes for.
    let mut targets: Vec<u32> = Vec::new();
    for instruction in &body.instructions {
        match &instruction.value {
            Value::Target(target) => targets.push(*target),
            Value::Targets(list) => targets.extend(list.iter().copied()),
            _ => {}
        }
    }
    for region in &body.regions {
        targets.push(region.try_offset);
        targets.push(region.handler_offset);
        if let Handler::Filter(offset) = region.kind {
            targets.push(offset);
        }
    }
    targets.sort_unstable();
    targets.dedup();

    let label = |offset: u32| match targets.binary_search(&offset) {
        Ok(index) => format!("L{index}"),
        Err(_) => format!("IL_{offset:04x}"),
    };

    for instruction in &body.instructions {
        // A region beginning here is worth saying before the instruction it
        // begins with: a reader scanning for `try` should find it in column
        // one rather than in a table at the end.
        for region in &body.regions {
            if region.try_offset == instruction.offset {
                let _ = writeln!(out, "  .try {{");
            }
            if region.handler_offset == instruction.offset {
                let _ = match region.kind {
                    Handler::Catch(token) => {
                        writeln!(out, "  }} catch ({}) {{", names.describe(token))
                    }
                    Handler::Filter(_) => writeln!(out, "  }} filter {{"),
                    Handler::Finally => writeln!(out, "  }} finally {{"),
                    Handler::Fault => writeln!(out, "  }} fault {{"),
                };
            }
        }

        if targets.binary_search(&instruction.offset).is_ok() {
            let _ = writeln!(out, "{}:", label(instruction.offset));
        }

        let operand = match &instruction.value {
            Value::None => String::new(),
            Value::Variable(number) => format!(" {number}"),
            Value::Int(number) => format!(" {number}"),
            Value::Float(number) => format!(" {number}"),
            Value::Token(token) => format!(" {}", names.describe(*token)),
            Value::Target(target) => format!(" {}", label(*target)),
            Value::Targets(list) => format!(
                " ({})",
                list.iter()
                    .map(|&target| label(target))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        let _ = writeln!(
            out,
            "    IL_{:04x}:  {}{operand}",
            instruction.offset, instruction.name
        );
    }
    out
}

// MARK: - reading the flags

/// The accessibility of a type, §II.23.1.15.
fn accessibility(flags: u32, nested: bool) -> &'static str {
    if nested {
        return match flags & 0x07 {
            0 => "private",
            1 => "public",
            2 | 4 => "protected",
            3 => "internal",
            5 => "protected internal",
            _ => "private protected",
        };
    }
    if flags & 0x07 == 1 {
        "public"
    } else {
        "internal"
    }
}

/// The accessibility of a field or method, §II.23.1.5 and §II.23.1.10.
const fn accessibility_of_member(flags: u32) -> &'static str {
    match flags & 0x07 {
        1 => "private",
        2 => "private protected",
        3 => "internal",
        4 => "protected",
        5 => "protected internal",
        6 => "public",
        _ => "private",
    }
}

fn type_keyword(flags: u32, names: &Names<'_>, token: Token) -> &'static str {
    if flags & 0x0020 != 0 {
        return "interface";
    }
    let base = names
        .assembly
        .row(token)
        .map(|row| row.token(3))
        .filter(|extends| !extends.is_nil())
        .map(|extends| names.type_name(extends))
        .unwrap_or_default();
    match base.as_str() {
        "System.Enum" => "enum",
        "System.ValueType" => "struct",
        "System.MulticastDelegate" | "System.Delegate" => "delegate",
        _ => "class",
    }
}

/// A type name with `System.` and the like taken off, the way a `using` would.
///
/// A name from a namespace the file would not have brought in keeps it,
/// because that is the part that says which library the type came from.
fn short(name: &str) -> String {
    for prefix in ["System.Collections.Generic.", "System.", "UnityEngine."] {
        if let Some(rest) = name.strip_prefix(prefix)
            && !rest.contains('.')
        {
            return rest.to_owned();
        }
    }
    name.to_owned()
}

// MARK: - keeping it between runs

impl Cacheable for AssemblySurface {
    // 2: the text is decompiled C# with bodies, not the surface alone.
    const VERSION: u32 = 2;

    fn encode(&self, writer: &mut Writer) {
        writer.str(&self.name);
        writer.str(&self.text);
        writer.seq(&self.declarations, |w, declaration| {
            w.str(&declaration.name);
            w.u32(declaration.name_start);
            w.u32(declaration.name_length);
            w.u32(declaration.line);
            w.u32(declaration.token);
            w.u8(u8::from(declaration.is_type));
        });
    }

    fn decode(reader: &mut Reader<'_>) -> Option<Self> {
        Some(Self {
            name: reader.string()?,
            text: reader.string()?,
            declarations: reader.seq(|r| {
                Some(Rendered {
                    name: r.string()?,
                    name_start: r.u32()?,
                    name_length: r.u32()?,
                    line: r.u32()?,
                    token: r.u32()?,
                    is_type: r.u8()? != 0,
                })
            })?,
        })
    }

    fn weight(&self) -> usize {
        self.text.len()
            + self
                .declarations
                .iter()
                .map(|declaration| declaration.name.len() + 48)
                .sum::<usize>()
    }
}

impl Cacheable for MethodBody {
    const VERSION: u32 = 1;

    fn encode(&self, writer: &mut Writer) {
        writer.str(&self.name);
        writer.str(&self.text);
        writer.u32(self.instructions);
        writer.u8(u8::from(self.is_empty));
    }

    fn decode(reader: &mut Reader<'_>) -> Option<Self> {
        Some(Self {
            name: reader.string()?,
            text: reader.string()?,
            instructions: reader.u32()?,
            is_empty: reader.u8()? != 0,
        })
    }

    fn weight(&self) -> usize {
        self.text.len() + self.name.len() + 32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_assembly_opens_as_csharp_with_its_bodies() {
        let bytes = std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../rustlyn-decompile/tests/fixtures/roslyn_sample.dll"
        ))
        .expect("fixture");
        let surface =
            AssemblySurface::decompiled(&bytes, "roslyn_sample.dll", &[]).expect("readable");
        assert!(
            surface
                .text
                .contains("for (int i = 0; i < items.Length; i++)"),
            "{}",
            surface.text
        );
        let line = |declaration: &Rendered| {
            surface
                .text
                .lines()
                .nth(declaration.line as usize)
                .unwrap_or_default()
                .to_owned()
        };
        let point = surface
            .declarations
            .iter()
            .position(|d| d.is_type && d.name == "Demo.Point")
            .expect("Point");
        assert!(line(&surface.declarations[point]).contains("class Point"));
        // A member follows its type, sits on its own line, and keeps the
        // token its IL is asked for by.
        let sum = surface.declarations[point..]
            .iter()
            .find(|d| d.name == "Sum")
            .expect("Sum");
        assert!(
            line(sum).contains("public int Sum(int[] items)"),
            "{}",
            line(sum)
        );
        assert_eq!(sum.token >> 24, 0x06, "a MethodDef token");
        let start = sum.name_start as usize;
        assert_eq!(
            &surface.text[start..start + sum.name_length as usize],
            "Sum"
        );
    }

    #[test]
    fn a_file_that_is_not_a_pe_image_says_so_rather_than_panicking() {
        let error =
            AssemblySurface::of(b"not an assembly at all", "x.dll").expect_err("it should refuse");
        assert!(matches!(error, Failure::Damaged(_)), "{error:?}");
    }

    #[test]
    fn an_empty_file_is_refused() {
        assert!(AssemblySurface::of(&[], "x.dll").is_err());
    }

    #[test]
    fn a_truncated_pe_header_is_refused_rather_than_read_past() {
        // `MZ` and then nothing: the shape of a file that was cut off.
        let mut bytes = b"MZ".to_vec();
        bytes.resize(64, 0);
        assert!(AssemblySurface::of(&bytes, "x.dll").is_err());
    }

    #[test]
    fn asking_for_a_body_in_a_broken_file_fails_rather_than_panicking() {
        assert!(MethodBody::of(b"rubbish", 0x0600_0001).is_err());
    }

    #[test]
    fn names_are_shortened_only_where_a_using_would_have() {
        assert_eq!(short("System.String"), "String");
        assert_eq!(short("System.Collections.Generic.List"), "List");
        assert_eq!(short("UnityEngine.Vector3"), "Vector3");
        // A nested namespace keeps its name: that is what says where it came
        // from, and a `using System;` would not have covered it.
        assert_eq!(
            short("System.Text.StringBuilder"),
            "System.Text.StringBuilder"
        );
        assert_eq!(short("MyGame.Thing"), "MyGame.Thing");
    }

    #[test]
    fn accessibility_reads_the_flags_the_standard_defines() {
        assert_eq!(accessibility(1, false), "public");
        assert_eq!(accessibility(0, false), "internal");
        assert_eq!(accessibility(1, true), "public");
        assert_eq!(accessibility(0, true), "private");
        assert_eq!(accessibility_of_member(6), "public");
        assert_eq!(accessibility_of_member(1), "private");
        assert_eq!(accessibility_of_member(4), "protected");
    }

    #[test]
    fn a_surface_survives_being_written_and_read_back() {
        let surface = AssemblySurface {
            name: "UnityEngine.CoreModule".into(),
            text: "namespace UnityEngine\n{\n    public struct Vector3\n    {\n    }\n}\n".into(),
            declarations: vec![Rendered {
                name: "UnityEngine.Vector3".into(),
                name_start: 40,
                name_length: 7,
                line: 2,
                token: 0x0200_0005,
                is_type: true,
            }],
        };
        let mut writer = Writer::new();
        surface.encode(&mut writer);
        let bytes = writer.finish();
        assert_eq!(
            AssemblySurface::decode(&mut Reader::new(&bytes)),
            Some(surface),
        );
    }

    #[test]
    fn a_body_survives_being_written_and_read_back() {
        let body = MethodBody {
            name: "System.Console::WriteLine".into(),
            text: "    IL_0000:  ldarg.0\n    IL_0001:  ret\n".into(),
            instructions: 2,
            is_empty: false,
        };
        let mut writer = Writer::new();
        body.encode(&mut writer);
        let bytes = writer.finish();
        assert_eq!(MethodBody::decode(&mut Reader::new(&bytes)), Some(body));
    }

    #[test]
    fn a_truncated_cache_entry_reads_as_nothing() {
        let body = MethodBody {
            name: "A::B".into(),
            text: "    IL_0000:  ret\n".into(),
            instructions: 1,
            is_empty: false,
        };
        let mut writer = Writer::new();
        body.encode(&mut writer);
        let bytes = writer.finish();
        for length in 0..bytes.len() {
            assert_ne!(
                MethodBody::decode(&mut Reader::new(&bytes[..length])),
                Some(body.clone()),
            );
        }
    }
}

/// Reading back an assembly this workspace compiled.
///
/// The surest check that a reader is right is to write something with the
/// other end of the same standard and read it back. `rustlyn-emit` lays out
/// the PE file, the heaps, the tables and the IL; everything below asks
/// whether this layer sees what was put there.
#[cfg(test)]
mod round_trip {
    use super::*;
    use rustlyn_semantics::Compilation;
    use rustlyn_syntax::{ParseOptions, parse_with};
    use rustlyn_text::SourceText;

    /// Compiles a snippet to a real .NET assembly.
    const DEMO: &str = r#"
using System;
namespace Game
{
    public class Pawn : IThing
    {
        public int Health;
        private int _secret;
        public string Name;
        public int Damage(int amount, int extra)
        {
            Health = Health - amount - extra;
            if (Health < 0) { Health = 0; }
            return Health;
        }
        public static void Main() { Console.WriteLine("hello"); }
    }
    public struct Point { public int X; public int Y; }
    public interface IThing { }
    public enum Mode { A, B }
}
"#;

    fn assemble(source: &str) -> Vec<u8> {
        let tree = parse_with(
            SourceText::new("Program.cs", source),
            &ParseOptions::default(),
        );
        let compilation = Compilation::create(vec![tree]);
        let errors: Vec<String> = compilation
            .semantic_diagnostics()
            .iter()
            .filter(|entry| entry.diagnostic.is_error())
            .map(|entry| compilation.render(entry))
            .collect();
        assert!(
            errors.is_empty(),
            "the test source should compile: {errors:#?}"
        );
        rustlyn_emit::emit(&compilation, "Test")
            .expect("it should emit")
            .assembly
    }

    const PROGRAM: &str = r#"
using System;

namespace Game
{
    public class Pawn
    {
        public int Health;
        private int _secret;

        public int Damage(int amount)
        {
            Health = Health - amount;
            return Health;
        }

        public static void Main()
        {
            Console.WriteLine("hello");
        }
    }

    public struct Point
    {
        public int X;
    }

    public interface IThing
    {
    }
}
"#;

    #[test]
    fn the_surface_shows_the_types_that_were_compiled() {
        let bytes = assemble(PROGRAM);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("it should read");

        assert_eq!(surface.name, "Test");
        assert!(surface.text.contains("namespace Game"), "{}", surface.text);
        assert!(surface.text.contains("class Pawn"), "{}", surface.text);
        assert!(surface.text.contains("struct Point"), "{}", surface.text);
        assert!(
            surface.text.contains("interface IThing"),
            "{}",
            surface.text
        );
    }

    #[test]
    fn the_surface_shows_members_with_their_signatures() {
        let bytes = assemble(PROGRAM);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("it should read");
        assert!(
            surface.text.contains("public int Health;"),
            "a public field with its type: {}",
            surface.text,
        );
        assert!(
            surface.text.contains("int Damage(int amount)"),
            "a method with its return type and parameter name: {}",
            surface.text,
        );
        assert!(
            surface.text.contains("static void Main()"),
            "`static` comes from the flags: {}",
            surface.text,
        );
    }

    #[test]
    fn a_private_member_is_left_out_of_a_surface_that_has_no_bodies() {
        let bytes = assemble(PROGRAM);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("it should read");
        assert!(
            !surface.text.contains("_secret"),
            "a private field is an implementation detail of an implementation \
             that is not here: {}",
            surface.text,
        );
    }

    #[test]
    fn every_declaration_points_at_its_own_name_in_the_text() {
        // What makes the rendered text navigable: the editor above jumps to
        // these spans, so they have to land on the name and nothing else.
        let bytes = assemble(PROGRAM);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("it should read");
        assert!(!surface.declarations.is_empty());
        for declaration in &surface.declarations {
            let start = declaration.name_start as usize;
            let end = start + declaration.name_length as usize;
            let found = surface
                .text
                .get(start..end)
                .unwrap_or_else(|| panic!("{declaration:?} is outside the text"));
            // A type's `name` is qualified (`Game.Pawn`) and the text holds
            // its last part; a member's `name` is already just the member,
            // and `.ctor` keeps its leading dot because that is the name
            // metadata gives a constructor rather than a qualification.
            let expected = if declaration.is_type {
                declaration.name.rsplit(['.', '/']).next().unwrap_or("")
            } else {
                declaration.name.as_str()
            };
            assert_eq!(found, expected, "{declaration:?}");
        }
    }

    #[test]
    fn a_declarations_line_number_is_the_line_it_is_on() {
        let bytes = assemble(PROGRAM);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("it should read");
        for declaration in &surface.declarations {
            let actual = surface.text[..declaration.name_start as usize]
                .bytes()
                .filter(|&byte| byte == b'\n')
                .count() as u32;
            assert_eq!(declaration.line, actual, "{declaration:?}");
        }
    }

    #[test]
    fn a_method_body_comes_back_as_il_with_its_names_resolved() {
        let bytes = assemble(PROGRAM);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("it should read");
        let main = surface
            .declarations
            .iter()
            .find(|declaration| !declaration.is_type && declaration.name == "Main")
            .expect("Main should be in the surface");

        let body = MethodBody::of(&bytes, main.token).expect("it should decode");
        assert!(!body.is_empty);
        assert!(body.instructions > 0, "{body:#?}");
        assert!(
            body.text.contains("ldstr") && body.text.contains("\"hello\""),
            "the string literal should be resolved out of the user string heap: {}",
            body.text,
        );
        assert!(
            body.text.contains("WriteLine"),
            "a call should name what it calls: {}",
            body.text,
        );
        assert!(body.text.contains("ret"), "{}", body.text);
    }

    #[test]
    fn a_body_is_only_read_when_it_is_asked_for() {
        // The point of the layer: the surface is one pass over the tables and
        // carries no IL at all, however many methods there are.
        let bytes = assemble(PROGRAM);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("it should read");
        assert!(
            !surface.text.contains("IL_0000"),
            "the surface must not contain any IL: {}",
            surface.text,
        );
    }

    #[test]
    fn asking_for_a_method_that_is_not_there_fails_rather_than_inventing_one() {
        let bytes = assemble(PROGRAM);
        assert!(MethodBody::of(&bytes, 0x0600_9999).is_err());
    }

    #[test]
    fn a_branch_becomes_a_label_rather_than_a_number() {
        let bytes = assemble(
            r#"
class Program
{
    public static int Choose(int n)
    {
        if (n > 0) { return 1; }
        return 2;
    }

    public static void Main() { }
}
"#,
        );
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("it should read");
        let choose = surface
            .declarations
            .iter()
            .find(|declaration| declaration.name == "Choose")
            .expect("Choose");
        let body = MethodBody::of(&bytes, choose.token).expect("it should decode");
        assert!(
            body.text.contains("L0") || body.text.contains("L1"),
            "a branch target should be a label: {}",
            body.text,
        );
    }

    #[test]
    fn a_method_with_no_body_says_so_rather_than_failing() {
        let bytes = assemble(
            "abstract class A { public abstract void M(); }\n\
             class B : A { public override void M() { } }\n\
             class Program { public static void Main() { } }",
        );
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("it should read");
        // Both `A.M` and `B.M` are called `M`; the one under test is the
        // abstract one, which is whichever of them has no body.
        let bodies: Vec<MethodBody> = surface
            .declarations
            .iter()
            .filter(|declaration| declaration.name == "M")
            .map(|declaration| {
                MethodBody::of(&bytes, declaration.token).expect("it should not fail")
            })
            .collect();
        assert_eq!(bodies.len(), 2, "A.M and B.M");
        let body = bodies
            .iter()
            .find(|body| body.is_empty)
            .expect("the abstract one has no body");
        assert_eq!(body.instructions, 0);
        assert!(body.text.contains("no body"), "{}", body.text);
    }

    #[test]
    fn the_surface_of_an_assembly_is_the_same_every_time() {
        // It is cached against the file, so two reads of the same bytes that
        // differed would be a cache that returns whichever it saw first.
        let bytes = assemble(PROGRAM);
        let once = AssemblySurface::of(&bytes, "Test.dll").expect("read");
        let twice = AssemblySurface::of(&bytes, "Test.dll").expect("read");
        assert_eq!(once, twice);
    }

    #[test]
    fn a_constructor_is_written_the_way_c_sharp_writes_one() {
        // Metadata calls it `.ctor` with a `void` return; nobody writes that.
        let bytes = assemble(DEMO);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("read");
        assert!(surface.text.contains("public Pawn();"), "{}", surface.text);
        assert!(
            !surface.text.contains("void .ctor"),
            "the metadata spelling should not reach the reader: {}",
            surface.text,
        );
    }

    #[test]
    fn an_enum_is_its_members_and_their_values() {
        let bytes = assemble(DEMO);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("read");
        assert!(
            surface.text.contains("public enum Mode"),
            "{}",
            surface.text
        );
        assert!(surface.text.contains("A = 0,"), "{}", surface.text);
        assert!(surface.text.contains("B = 1,"), "{}", surface.text);
        assert!(
            !surface.text.contains("value__"),
            "the hidden field an enum carries is not one of its members: {}",
            surface.text,
        );
    }

    #[test]
    fn a_type_in_the_namespace_being_written_needs_no_prefix() {
        let bytes = assemble(DEMO);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("read");
        assert!(
            surface.text.contains("class Pawn : IThing"),
            "inside `namespace Game`, `Game.IThing` is `IThing`: {}",
            surface.text,
        );
    }

    #[test]
    fn each_namespace_is_opened_once() {
        let bytes = assemble(DEMO);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("read");
        assert_eq!(
            surface.text.matches("namespace Game").count(),
            1,
            "one block for the namespace, not one per type: {}",
            surface.text,
        );
    }

    #[test]
    fn a_field_read_in_il_names_the_field() {
        let bytes = assemble(DEMO);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("read");
        let damage = surface
            .declarations
            .iter()
            .find(|declaration| declaration.name == "Damage")
            .expect("Damage");
        let body = MethodBody::of(&bytes, damage.token).expect("decode");
        assert!(
            body.text.contains("ldfld Game.Pawn::Health"),
            "a field token should resolve to the field: {}",
            body.text,
        );
    }

    #[test]
    fn a_surface_read_from_a_real_assembly_survives_the_cache() {
        let bytes = assemble(PROGRAM);
        let surface = AssemblySurface::of(&bytes, "Test.dll").expect("read");
        let mut writer = Writer::new();
        surface.encode(&mut writer);
        let encoded = writer.finish();
        assert_eq!(
            AssemblySurface::decode(&mut Reader::new(&encoded)),
            Some(surface),
        );
    }
}
