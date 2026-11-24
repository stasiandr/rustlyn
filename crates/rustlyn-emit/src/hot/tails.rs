//! Room for the fields an edit adds to a struct.
//!
//! A struct has no identity to keep a field beside, and a loaded struct
//! cannot grow. So an editor's build gives structs a tail they never use, a
//! field written into each one's declaration as the daemon reads the file —
//! the file on disk is not touched, and the generators never see it — and a
//! field an edit adds lives in the tail. Copying the struct copies the tail,
//! so the new field behaves as a field of a value does.
//!
//! Which structs: every one but those laid out for something outside the
//! program — a vertex, a compute buffer, a native container, a job, a native
//! call — whose size may be written down somewhere a tail would break. Those
//! are found by how the code uses them: a type argument of a native
//! container or of what sends data to the GPU, `sizeof`, a pointer, a
//! `[StructLayout]`, a job's interface. A struct that holds a reference can
//! be none of them, and an ECS component is the game's own.
//!
//! What goes where is decided at run time (`PilotTail.Access`), the first
//! time each field is reached, from its size: a value without references in
//! 32 bytes, anything else in one of four object slots, which only a struct
//! that already holds references has.

use std::collections::HashMap;

use rustlyn_semantics::{Binder, Compilation, Modifiers, SymbolId, SymbolKind, Type, TypeKind};
use rustlyn_syntax::SyntaxKind;

/// What the tails are made of, and the one way into them.
pub(crate) const SUPPORT: &str = r#"namespace PilotTail
{
    using System.Collections.Generic;
    using System.Runtime.CompilerServices;

    /// The tail of a struct of values alone: bytes.
    public struct ValueTail
    {
        public long a, b, c, d;
    }

    /// The tail of a struct that holds references: bytes, and four slots.
    public struct Tail
    {
        public ValueTail bytes;
        public object r0, r1, r2, r3;
    }

    public static class Access
    {
        sealed class Places
        {
            public int bytes, slots;
            public readonly Dictionary<string, int> of = new Dictionary<string, int>();
        }

        static readonly Dictionary<string, Places> owners = new Dictionary<string, Places>();

        // Where `field` of `owner` sits: a byte offset, or a slot. Decided the
        // first time it is asked for and kept for as long as the assembly is
        // loaded, which is as long as any value with the tail lives.
        static int Place(string owner, string field, int size, bool slot)
        {
            if (!owners.TryGetValue(owner, out var places)) owners[owner] = places = new Places();
            if (places.of.TryGetValue(field, out var at)) return at;
            if (slot)
            {
                if (places.slots == 4) throw Full(owner, field);
                at = places.slots++;
            }
            else
            {
                var align = size >= 8 ? 8 : size >= 4 ? 4 : size >= 2 ? 2 : 1;
                at = (places.bytes + align - 1) / align * align;
                if (at + size > 32) throw Full(owner, field);
                places.bytes = at + size;
            }
            places.of[field] = at;
            return at;
        }

        static System.InvalidOperationException Full(string owner, string field) =>
            new System.InvalidOperationException(
                owner + "." + field + ": the struct's tail has no room left for it; a reload brings it in");

        static ref T Bytes<T>(ref ValueTail tail, string owner, string field) =>
            ref Unsafe.As<byte, T>(ref Unsafe.Add(
                ref Unsafe.As<ValueTail, byte>(ref tail), Place(owner, field, Unsafe.SizeOf<T>(), false)));

        public static ref T Field<T>(ref ValueTail tail, string owner, string field)
        {
            if (RuntimeHelpers.IsReferenceOrContainsReferences<T>())
                throw new System.InvalidOperationException(
                    owner + "." + field + ": a struct of values alone has no room for a reference; a reload brings it in");
            return ref Bytes<T>(ref tail, owner, field);
        }

        public static ref T Field<T>(ref Tail tail, string owner, string field)
        {
            if (!RuntimeHelpers.IsReferenceOrContainsReferences<T>())
                return ref Bytes<T>(ref tail.bytes, owner, field);
            ref object slot = ref Slot(ref tail, Place(owner, field, 1, true));
            if (!typeof(T).IsValueType) return ref Unsafe.As<object, T>(ref slot);
            // A value with references in it is kept in a box of its own, which
            // a copy of the struct shares.
            if (slot == null) slot = new StrongBox<T>();
            return ref ((StrongBox<T>)slot).Value;
        }

        static ref object Slot(ref Tail tail, int index)
        {
            switch (index)
            {
                case 0: return ref tail.r0;
                case 1: return ref tail.r1;
                case 2: return ref tail.r2;
                default: return ref tail.r3;
            }
        }
    }
}
"#;

/// The structs that get a tail: each by its qualified name, with whether its
/// tail has slots for references, and the file whose declaration of it the
/// tail is written into.
#[derive(Default, Debug, Clone)]
pub(crate) struct Tailed {
    structs: HashMap<String, (bool, String)>,
}

impl Tailed {
    /// Each struct given a tail, by qualified name, and whether its tail
    /// has slots for references: what the emitter writes them from.
    pub(crate) fn references(&self) -> std::collections::HashMap<String, bool> {
        self.structs
            .iter()
            .map(|(name, (references, _))| (name.clone(), *references))
            .collect()
    }

    /// Each struct given a tail, and whether its tail has slots for
    /// references, one per line: what two builds must agree on for an
    /// editor to reload from one onto the other.
    pub(crate) fn listing(&self) -> String {
        let mut lines: Vec<String> = self
            .structs
            .iter()
            .map(|(name, (references, _))| format!("{name}\t{references}\n"))
            .collect();
        lines.sort();
        lines.concat()
    }

    /// Whether the struct `ty` has a tail, and whether that has slots.
    pub(crate) fn of(&self, compilation: &Compilation, ty: SymbolId) -> Option<bool> {
        self.structs
            .get(&compilation.symbols().qualified_name(ty))
            .map(|(references, _)| *references)
    }
}

/// Which structs of the compilation get a tail.
pub(crate) fn choose(compilation: &Compilation) -> Tailed {
    let binder = Binder::new(compilation);
    let symbols = compilation.symbols();
    let mut structs = HashMap::new();
    // The types with an instance field whose type is a reference for
    // certain: a class, an interface, a delegate, an array, `string`,
    // `object`.
    let mut holding: std::collections::HashSet<SymbolId> = std::collections::HashSet::new();
    for member in symbols.iter() {
        if member.kind == SymbolKind::Field
            && !member.modifiers.contains(Modifiers::STATIC)
            && !member.modifiers.contains(Modifiers::CONST)
            && let Some(owner) = member.container
            && !holding.contains(&owner)
            && symbols.get(owner).type_kind() == Some(TypeKind::Struct)
            && !compilation.is_from_metadata(owner)
            && is_reference(&binder, &binder.type_of(member.id, &mut Default::default()))
        {
            holding.insert(owner);
        }
    }
    let native = native_names(compilation);
    for ty in compilation.all_types() {
        let id = ty.id;
        // The tails' own types are what a tail is made of: one given a
        // tail would hold itself, which no runtime can lay out.
        if ty.type_kind() != Some(TypeKind::Struct)
            || compilation.is_from_metadata(id)
            || ty.modifiers.contains(Modifiers::REF)
            || generic_around(compilation, id)
            || symbols.qualified_name(id).starts_with("PilotTail.")
        {
            continue;
        }
        let nodes = compilation.declaration_nodes(id);
        let heads: Vec<(usize, String)> = nodes
            .iter()
            .filter_map(|&(tree, span)| {
                let node = compilation.trees().get(tree)?.root().find_node(span)?;
                let text = node.text();
                Some((tree, text.split('{').next().unwrap_or(&text).to_string()))
            })
            .collect();
        if heads.iter().any(|(_, head)| head.contains("StructLayout")) {
            continue;
        }
        let component = heads.iter().any(|(_, head)| head.contains("EcsComponent"));
        let references = holding.contains(&id);
        if !component && !references && native.contains(&ty.name) {
            continue;
        }
        if heads
            .iter()
            .any(|(_, head)| head.contains("IJob") || head.contains("IComponentData"))
        {
            continue;
        }
        // One declaration holds the tail: the one in the first of its files
        // by name, the same every time the files are read.
        let Some(file) = heads
            .iter()
            .filter_map(|(tree, _)| {
                compilation
                    .trees()
                    .source(*tree)
                    .map(|source| source.name().to_string())
            })
            .min()
        else {
            continue;
        };
        structs.insert(symbols.qualified_name(id), (references, file));
    }
    Tailed { structs }
}

/// Whether the fields an edit adds to structs fit their tails: an error
/// where the struct has none, or where a reference would go in a tail of
/// values alone.
pub(crate) fn check(
    compilation: &Compilation,
    tailed: &Tailed,
    fields: &[SymbolId],
) -> Result<HashMap<SymbolId, u32>, String> {
    let binder = Binder::new(compilation);
    let symbols = compilation.symbols();
    let mut placed = HashMap::new();
    for &field in fields {
        let Some(owner) = symbols.get(field).container else {
            continue;
        };
        let Some(references) = tailed.of(compilation, owner) else {
            continue;
        };
        let ty = binder.type_of(field, &mut Default::default());
        if !references && is_reference(&binder, &ty) {
            return Err(format!(
                "{}: {} holds values alone, and its tail has no room for a reference",
                symbols.qualified_name(field),
                symbols.qualified_name(owner)
            ));
        }
        placed.insert(field, 0);
    }
    Ok(placed)
}

/// The names of the types the code hands to something outside it: type
/// arguments of native containers and of what writes to the GPU or sizes
/// memory, what `sizeof` measures, what a pointer points at.
fn native_names(compilation: &Compilation) -> std::collections::HashSet<String> {
    const NATIVE: &[&str] = &[
        "NativeArray",
        "NativeList",
        "NativeSlice",
        "NativeHashMap",
        "NativeParallelHashMap",
        "NativeMultiHashMap",
        "NativeParallelMultiHashMap",
        "NativeQueue",
        "NativeHashSet",
        "NativeParallelHashSet",
        "NativeReference",
        "NativeStream",
        "UnsafeList",
        "UnsafeHashMap",
        "UnsafeParallelHashMap",
        "UnsafeArray",
        "SetData",
        "GetData",
        "SetVertexBufferData",
        "SetIndexBufferData",
        "SetBufferData",
        "SizeOf",
        "AlignOf",
        "ReadArrayElement",
        "WriteArrayElement",
        "AsArray",
        "Reinterpret",
        "BeginWrite",
        "GetSubArray",
        "CopyFrom",
        "MemCpy",
        "PtrToStructure",
        "StructureToPtr",
        "BufferElement",
    ];
    let mut names = std::collections::HashSet::new();
    let trees = compilation.trees();
    for index in 0..trees.len() {
        let Some(tree) = trees.get(index) else {
            continue;
        };
        for node in tree.root().descendants() {
            let arguments = match node.kind() {
                SyntaxKind::GenericName
                    if node
                        .first_token()
                        .is_some_and(|token| NATIVE.contains(&token.text())) =>
                {
                    node.children()
                        .find(|child| child.kind() == SyntaxKind::TypeArgumentList)
                        .map(|list| list.children().collect::<Vec<_>>())
                        .unwrap_or_default()
                }
                SyntaxKind::SizeOfExpression | SyntaxKind::PointerType => node.children().collect(),
                _ => continue,
            };
            for argument in arguments {
                if let Some(name) = argument
                    .last_token()
                    .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                {
                    names.insert(name.text().to_string());
                }
            }
        }
    }
    names
}

fn is_reference(binder: &Binder<'_>, ty: &Type) -> bool {
    match ty {
        Type::Array { .. } | Type::Dynamic => true,
        Type::Named { symbol, .. } => {
            let symbols = binder.compilation().symbols();
            matches!(
                symbols.get(*symbol).type_kind(),
                Some(TypeKind::Class | TypeKind::Interface | TypeKind::Delegate | TypeKind::Record)
            )
        }
        _ => false,
    }
}

fn generic_around(compilation: &Compilation, ty: SymbolId) -> bool {
    let symbols = compilation.symbols();
    let mut current = Some(ty);
    while let Some(id) = current {
        let symbol = symbols.get(id);
        if symbol.kind != SymbolKind::NamedType {
            break;
        }
        if symbol
            .as_named_type()
            .is_some_and(|detail| !detail.type_parameters.is_empty())
        {
            return true;
        }
        current = symbol.container;
    }
    false
}
