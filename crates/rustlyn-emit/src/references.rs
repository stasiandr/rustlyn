//! The bridge from symbols to metadata tokens.
//!
//! A compilation holds two kinds of symbol that look identical from the
//! binder's side and could hardly be more different from emit's. One kind the
//! assembly *defines*: a `TypeDef`, a `MethodDef`, a `Field`. The other it
//! *references*: a `TypeRef` into another assembly and a `MemberRef` under it.
//! The only thing that tells them apart is which file declared them, and the
//! synthesised core library is a file like any other.
//!
//! Where the compilation was given real assemblies, each referenced type
//! carries the one it came from, and the `AssemblyRef` says exactly that. Where
//! it was given the synthesised core library instead, that stand-in holds no
//! such answer, so a reference is resolved by name against the framework the
//! program will run on.

use std::collections::HashMap;

use rustlyn_semantics::{Compilation, Reference, SymbolKind};

use crate::il::Token;
use crate::metadata::Metadata;
use crate::signature::type_def_or_ref;

/// The version every framework reference is made against.
const FRAMEWORK_VERSION: [u16; 4] = [8, 0, 0, 0];
/// The public key token the .NET framework assemblies are signed with.
const ECMA_PUBLIC_KEY_TOKEN: [u8; 8] = [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A];

/// Which framework assembly a core-library type really lives in.
///
/// Nearly everything a small program touches is type-forwarded to
/// `System.Runtime`, but not everything: the console has an assembly of its
/// own, and the concrete collections live in `System.Collections` even though
/// the interfaces beside them (`IEnumerable<T>` and friends) do not. Naming
/// the wrong one is a `TypeLoadException` when the program runs, not anything
/// the writer can catch.
fn assembly_by_name(qualified_name: &str) -> Reference {
    let name = match qualified_name {
        "System.Console" => "System.Console",
        "System.Collections.Generic.List`1"
        | "System.Collections.Generic.Dictionary`2"
        | "System.Collections.Generic.HashSet`1"
        | "System.Collections.Generic.Queue`1"
        | "System.Collections.Generic.Stack`1"
        | "System.Collections.Generic.EqualityComparer`1" => "System.Collections",
        _ => "System.Runtime",
    };
    Reference {
        name: name.to_string(),
        version: FRAMEWORK_VERSION,
        public_key_token: Some(ECMA_PUBLIC_KEY_TOKEN),
    }
}

/// Whether an assembly is part of the framework rather than a library
/// beside the program.
pub(crate) fn is_framework(name: &str) -> bool {
    name.starts_with("System.")
        || matches!(
            name,
            "System" | "mscorlib" | "netstandard" | "Microsoft.CSharp"
        )
        || name.starts_with("Microsoft.")
}

/// Holds the references an assembly makes and hands out their tokens.
#[derive(Debug)]
pub(crate) struct References {
    assemblies: HashMap<String, Token>,
    /// Which assembly each referenced type really lives in, as the loaded
    /// metadata said rather than as anything here guessed.
    homes: HashMap<String, Reference>,
    /// Each `TypeRef` by the assembly it points into and the type's name:
    /// two assemblies may each define a type of the same name, and they are
    /// two types.
    types: HashMap<(String, String), Token>,
    members: HashMap<(String, String, Vec<u8>), Token>,
    specs: HashMap<Vec<u8>, Token>,
}

impl References {
    #[must_use]
    pub(crate) fn new(compilation: &Compilation) -> Self {
        let symbols = compilation.symbols();
        let homes = symbols
            .iter()
            .filter(|symbol| {
                symbol.kind == SymbolKind::NamedType && compilation.is_from_metadata(symbol.id)
            })
            .filter_map(|symbol| {
                let reference = compilation.assembly_of(symbol.id)?;
                Some((
                    symbols.metadata_qualified_name(symbol.id),
                    reference.clone(),
                ))
            })
            // A type only a name reaches is the framework's where a library
            // declares one of the same name too: `InAttribute` of its own
            // does not make every `modreq` the compiler writes point at it.
            .fold(
                HashMap::new(),
                |mut homes: HashMap<String, Reference>, (name, reference)| {
                    let framework = is_framework(&reference.name);
                    match homes.get(&name) {
                        Some(existing) if is_framework(&existing.name) || !framework => {}
                        _ => {
                            homes.insert(name, reference);
                        }
                    }
                    homes
                },
            );
        Self {
            assemblies: HashMap::new(),
            homes,
            types: HashMap::new(),
            members: HashMap::new(),
            specs: HashMap::new(),
        }
    }

    fn assembly(&mut self, metadata: &mut Metadata, reference: &Reference) -> Token {
        if let Some(token) = self.assemblies.get(&reference.name) {
            return *token;
        }
        // The token is the referenced assembly's own: the core library and
        // `System.Runtime` are signed with different keys, and a library
        // beside the program with none at all.
        let token = metadata.add_assembly_ref(
            &reference.name,
            reference.version,
            reference
                .public_key_token
                .as_ref()
                .map_or(&[][..], |token| &token[..]),
        );
        self.assemblies.insert(reference.name.clone(), token);
        token
    }

    /// The major version of the framework the references came from, for
    /// the runtime configuration to ask for the same one.
    #[must_use]
    pub(crate) fn framework_major(&self) -> u16 {
        self.homes
            .values()
            .filter(|reference| {
                matches!(
                    reference.name.as_str(),
                    "System.Runtime" | "System.Private.CoreLib"
                )
            })
            .map(|reference| reference.version[0])
            .max()
            .unwrap_or(FRAMEWORK_VERSION[0])
    }

    /// The `MemberRef` for a member of a type whose `TypeRef` is already
    /// known, which is how a member of a type from a particular assembly is
    /// reached.
    pub(crate) fn member_ref_on(
        &mut self,
        metadata: &mut Metadata,
        ty: Token,
        name: &str,
        signature: &[u8],
    ) -> Token {
        let key = (
            format!("ref:{}", ty.0),
            name.to_string(),
            signature.to_vec(),
        );
        if let Some(token) = self.members.get(&key) {
            return *token;
        }
        // A `MemberRefParent` tagged 1 is a `TypeRef`.
        let parent = ((ty.0 & 0x00FF_FFFF) << 3) | 1;
        let token = metadata.add_member_ref(parent, name, signature);
        self.members.insert(key, token);
        token
    }

    /// The `TypeRef` for a framework type, named the way metadata names it.
    pub(crate) fn type_ref(&mut self, metadata: &mut Metadata, qualified_name: &str) -> Token {
        let outermost = qualified_name.split('+').next().unwrap_or(qualified_name);
        let home = self
            .homes
            .get(outermost)
            .cloned()
            .unwrap_or_else(|| assembly_by_name(outermost));
        self.type_ref_in(metadata, &home, qualified_name)
    }

    /// The `TypeRef` for a type of one particular assembly, which is how a
    /// type read from a reference is named: by where it came from, not only
    /// by what it is called.
    pub(crate) fn type_ref_in(
        &mut self,
        metadata: &mut Metadata,
        home: &Reference,
        qualified_name: &str,
    ) -> Token {
        let key = (home.name.clone(), qualified_name.to_string());
        if let Some(token) = self.types.get(&key) {
            return *token;
        }
        // A nested type is scoped to the type it is nested in, not to an
        // assembly, and carries no namespace of its own.
        let (scope, namespace, name) = match qualified_name.rsplit_once('+') {
            Some((outer, name)) => {
                let outer = self.type_ref_in(metadata, home, outer);
                // A `ResolutionScope` tagged 3 is a `TypeRef`.
                (((outer.0 & 0x00FF_FFFF) << 2) | 3, "", name)
            }
            None => {
                let assembly = self.assembly(metadata, home);
                let (namespace, name) = match qualified_name.rsplit_once('.') {
                    Some((namespace, name)) => (namespace, name),
                    None => ("", qualified_name),
                };
                // A `ResolutionScope` tagged 2 is an `AssemblyRef`.
                (((assembly.0 & 0x00FF_FFFF) << 2) | 2, namespace, name)
            }
        };
        let token = metadata.add_type_ref(scope, namespace, name);
        self.types.insert(key, token);
        token
    }

    /// The `MemberRef` for a member of a framework type.
    ///
    /// Two members of one type can share a name, so the signature is part of
    /// the key: `WriteLine(string)` and `WriteLine(int)` are two rows.
    pub(crate) fn member_ref(
        &mut self,
        metadata: &mut Metadata,
        qualified_type: &str,
        name: &str,
        signature: &[u8],
    ) -> Token {
        let ty = self.type_ref(metadata, qualified_type);
        self.member_ref_on(metadata, ty, name, signature)
    }

    /// The `TypeSpec` naming a constructed type, one row per distinct shape.
    pub(crate) fn type_spec(&mut self, metadata: &mut Metadata, signature: &[u8]) -> Token {
        if let Some(token) = self.specs.get(signature) {
            return *token;
        }
        let token = metadata.add_type_spec(signature);
        self.specs.insert(signature.to_vec(), token);
        token
    }

    /// A `MemberRef` whose parent is a constructed type rather than a named
    /// one: `Box<int>::Get`, which has no definition of its own.
    pub(crate) fn member_of_spec(
        &mut self,
        metadata: &mut Metadata,
        spec: Token,
        name: &str,
        signature: &[u8],
    ) -> Token {
        let key = (
            format!("spec:{}", spec.0),
            name.to_string(),
            signature.to_vec(),
        );
        if let Some(token) = self.members.get(&key) {
            return *token;
        }
        // A `MemberRefParent` tagged 4 is a `TypeSpec`.
        let parent = ((spec.0 & 0x00FF_FFFF) << 3) | 4;
        let token = metadata.add_member_ref(parent, name, signature);
        self.members.insert(key, token);
        token
    }

    /// The `TypeDefOrRef` coded index for a framework type, for the places a
    /// signature or an instruction wants one.
    pub(crate) fn type_ref_coded(&mut self, metadata: &mut Metadata, qualified_name: &str) -> u32 {
        let token = self.type_ref(metadata, qualified_name);
        type_def_or_ref(1, token.0 & 0x00FF_FFFF)
    }
}
