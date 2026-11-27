//! What an extension block (C# 14) leaves in metadata beside its members.
//!
//! A block is not a type in the CLI. Each member of it is a static method of
//! the class that holds the block, taking the block's receiver first where
//! the member is an instance one and the block's type parameters before its
//! own, and that is all a call needs. What the class does not say is which
//! methods belong to a block, and what the block extends: Roslyn writes that
//! beside them, and another compiler reads the members back by it.
//!
//! A *grouping type* `<G>$…` is nested in the class, sealed and
//! `[Extension]`, and declares the block's type parameters as its own. It
//! holds a marker method for every member of the blocks that extend the same
//! type, with the signature the block gave the member: no receiver, and the
//! type parameters of the block as the type's. Each block has a *marker
//! type* `<M>$…` nested in the grouping type, whose `<Extension>$` method
//! takes the receiver as the block wrote it, and each marker method says
//! which block it is of with `[ExtensionMarker("<M>$…")]`.

use rustlyn_semantics::{Detail, Modifiers, SymbolId, SymbolKind, TypeSyntaxRef};

use crate::emitter::{EmitError, Emitter, generic_param_flags, method_flags};
use crate::il::Token;
use crate::metadata::{method_attributes, type_attributes};
use crate::signature::{
    ElementType, SigType, generic_method_signature, method_signature, property_signature,
};

/// One extension block of a static class, as its members tell it.
struct Block {
    class: SymbolId,
    extended: TypeSyntaxRef,
    /// The methods and properties it declared, in order.
    members: Vec<SymbolId>,
}

/// What the `Property` row of a marker property needs: its name, signature
/// and accessors, and the marker type it is of.
struct MarkerProperty {
    name: String,
    signature: Vec<u8>,
    getter: Option<Token>,
    setter: Option<Token>,
    marker: String,
}

/// The blocks that extend one type in one class, which share a grouping type.
struct Group {
    class: SymbolId,
    blocks: Vec<usize>,
}

impl Emitter<'_> {
    /// Whether a static class holds an extension block.
    pub(crate) fn holds_extension_blocks(&self, class: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        symbols
            .get(class)
            .members
            .iter()
            .any(|member| match &symbols.get(*member).detail {
                Detail::Method(detail) => detail.extended.is_some(),
                Detail::Property(detail) => detail.extended.is_some(),
                _ => false,
            })
    }

    /// The extension blocks of the classes this compilation declares, in the
    /// order their first members were.
    fn extension_blocks(&self) -> Vec<Block> {
        let symbols = self.compilation.symbols();
        let mut blocks: Vec<Block> = Vec::new();
        for class in symbols.iter() {
            if class.kind != SymbolKind::NamedType || !self.types.contains_key(&class.id) {
                continue;
            }
            for member in &class.members {
                let extended = match &symbols.get(*member).detail {
                    Detail::Method(detail) => detail.extended,
                    Detail::Property(detail) => detail.extended,
                    _ => None,
                };
                let Some(extended) = extended else {
                    continue;
                };
                match blocks
                    .iter_mut()
                    .find(|block| block.class == class.id && block.extended == extended)
                {
                    Some(block) => block.members.push(*member),
                    None => blocks.push(Block {
                        class: class.id,
                        extended,
                        members: vec![*member],
                    }),
                }
            }
        }
        blocks
    }

    /// The type parameters a block declares, as its first member has them.
    fn block_type_parameters(&self, block: &Block) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        match &symbols.get(block.members[0]).detail {
            Detail::Property(detail) => detail.extension_generics.clone(),
            Detail::Method(detail) => detail
                .type_parameters
                .iter()
                .copied()
                .filter(|parameter| {
                    symbols
                        .get(*parameter)
                        .container
                        .is_some_and(|holder| symbols.get(holder).name == "<extension>")
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    /// Whether a method is an operator or a conversion of an extension block.
    pub(crate) fn is_extension_operator(&self, method: SymbolId) -> bool {
        self.compilation
            .symbols()
            .get(method)
            .as_method()
            .is_some_and(|detail| {
                detail.extended.is_some()
                    && matches!(
                        detail.method_kind,
                        rustlyn_semantics::MethodKind::Operator
                            | rustlyn_semantics::MethodKind::Conversion
                    )
            })
    }

    /// The parameter a block's receiver is, as an instance member of it has
    /// it: the name, and how it is passed.
    fn block_receiver(&self, block: &Block) -> Option<SymbolId> {
        let instance = block
            .members
            .iter()
            .copied()
            .find(|member| self.is_instance_extension_member(*member))?;
        match &self.compilation.symbols().get(instance).detail {
            Detail::Method(detail) => detail.parameters.first().copied(),
            Detail::Property(detail) => detail.parameters.first().copied(),
            _ => None,
        }
    }

    /// Whether a member of a block is an instance one, which takes the
    /// block's receiver as its first parameter.
    fn is_instance_extension_member(&self, member: SymbolId) -> bool {
        match &self.compilation.symbols().get(member).detail {
            Detail::Method(detail) => detail.takes_receiver,
            Detail::Property(detail) => !detail.parameters.is_empty(),
            _ => false,
        }
    }

    /// Writes the two bodies every marker method of the assembly shares into
    /// the code, where the compilation has any block: `throw new
    /// NotSupportedException()` for a marker method, which nothing may
    /// call, and `ret` for the `<Extension>$` method of a marker type.
    pub(crate) fn add_extension_bodies(&mut self, il: &mut Vec<u8>) {
        if self.extension_blocks().is_empty() {
            return;
        }
        let constructor = self.references.member_ref(
            &mut self.metadata,
            "System.NotSupportedException",
            ".ctor",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &[]),
        );
        let mut write = |code: &[u8]| {
            while !il.len().is_multiple_of(4) {
                il.push(0);
            }
            let offset = il.len() as u32;
            // A tiny header carries the code size in its top six bits.
            il.push(0x02 | ((code.len() as u8) << 2));
            il.extend_from_slice(code);
            offset
        };
        let mut throwing = vec![0x73];
        throwing.extend_from_slice(&constructor.0.to_le_bytes());
        throwing.push(0x7A);
        let thrown = write(&throwing);
        let returned = write(&[0x2A]);
        self.extension_bodies = Some((thrown, returned));
    }

    /// Writes the grouping types and marker types of every extension block.
    pub(crate) fn write_extension_groups(&mut self) -> Result<(), EmitError> {
        let Some((thrown, returned)) = self.extension_bodies else {
            return Ok(());
        };
        const MARKER: &str = "System.Runtime.CompilerServices.ExtensionMarkerAttribute";
        if self.compilation.type_by_metadata_name(MARKER).is_none() {
            return Ok(());
        }
        let blocks = self.extension_blocks();
        // Blocks that extend the same type, with no type parameters of their
        // own to tell apart, are the one group.
        let mut groups: Vec<Group> = Vec::new();
        let mut keys: Vec<String> = Vec::new();
        for (at, block) in blocks.iter().enumerate() {
            let generics = self.block_type_parameters(block);
            let mut sink = rustlyn_semantics::Diagnostics::new();
            let extended = self.binder.resolve_type_ref(block.extended, &mut sink);
            let key = if generics.is_empty() {
                format!("{}|{extended:?}", block.class.index())
            } else {
                format!("{}|block {at}", block.class.index())
            };
            match keys.iter().position(|known| *known == key) {
                Some(found) => groups[found].blocks.push(at),
                None => {
                    keys.push(key);
                    groups.push(Group {
                        class: block.class,
                        blocks: vec![at],
                    });
                }
            }
        }
        for (group, key) in groups.iter().zip(&keys) {
            self.write_extension_group(&blocks, group, key, thrown, returned)?;
        }
        self.display_generics = Vec::new();
        self.method_generics = Vec::new();
        Ok(())
    }

    fn write_extension_group(
        &mut self,
        blocks: &[Block],
        group: &Group,
        key: &str,
        thrown: u32,
        returned: u32,
    ) -> Result<(), EmitError> {
        let Some(class) = self.types.get(&group.class).copied() else {
            return Ok(());
        };
        let generics = self.block_type_parameters(&blocks[group.blocks[0]]);
        let object = self
            .references
            .type_ref_coded(&mut self.metadata, "System.Object");
        let mut name = format!("<G>${}", hash_of(key));
        if !generics.is_empty() {
            name.push_str(&format!("`{}", generics.len()));
        }
        let grouping = self.metadata.add_type_def(
            type_attributes::NESTED_PUBLIC
                | type_attributes::SEALED
                | type_attributes::SPECIAL_NAME,
            "",
            &name,
            object,
        );
        self.metadata.add_nested_class(grouping, class);
        self.mark_extension(((grouping.0 & 0x00FF_FFFF) << 5) | 3);
        let owner = (grouping.0 & 0x00FF_FFFF) << 1;
        self.display_generics = generics.clone();
        for (number, parameter) in generics.iter().enumerate() {
            let flags = generic_param_flags(self.compilation.symbols(), *parameter) & !0x0003u16;
            self.metadata
                .add_generic_param(number as u16, flags, owner, &format!("$T{number}"));
            self.write_constraints(owner, number as u16, *parameter)?;
        }

        // The marker types are named before their members are, since each
        // member says which one it is of. Blocks that write the receiver the
        // same way share one.
        let markers: Vec<String> = group
            .blocks
            .iter()
            .map(|at| {
                let receiver = self.block_receiver(&blocks[*at]);
                let (name, by_ref) = receiver.map_or((String::new(), false), |symbol| {
                    (
                        self.compilation.symbols().get(symbol).name.clone(),
                        self.is_by_reference(Some(symbol)),
                    )
                });
                format!("<M>${}", hash_of(&format!("{key}|{name}|{by_ref}")))
            })
            .collect();
        let mut properties: Vec<MarkerProperty> = Vec::new();
        for (at, marker) in group.blocks.iter().zip(&markers) {
            for member in blocks[*at].members.clone() {
                match &self.compilation.symbols().get(member).detail {
                    Detail::Method(_) => {
                        self.write_marker_method(member, marker, generics.len(), thrown)?;
                    }
                    Detail::Property(_) => {
                        let written = self.write_marker_property(member, marker, thrown)?;
                        properties.push(written);
                    }
                    _ => {}
                }
            }
        }
        if !properties.is_empty() {
            self.metadata.add_property_map(grouping);
            for property in properties {
                let row = self.metadata.add_property(
                    &property.name,
                    &property.signature,
                    property.getter,
                    property.setter,
                );
                self.mark_extension_marker(((row.0 & 0x00FF_FFFF) << 5) | 9, &property.marker);
            }
        }

        let mut written: Vec<&String> = Vec::new();
        for (at, marker) in group.blocks.iter().zip(&markers) {
            if written.contains(&marker) {
                continue;
            }
            written.push(marker);
            let block = &blocks[*at];
            let token = self.metadata.add_type_def(
                type_attributes::NESTED_PUBLIC
                    | type_attributes::ABSTRACT
                    | type_attributes::SEALED
                    | type_attributes::SPECIAL_NAME,
                "",
                marker,
                object,
            );
            self.metadata.add_nested_class(token, grouping);
            let owner = (token.0 & 0x00FF_FFFF) << 1;
            self.display_generics = generics.clone();
            for (number, parameter) in generics.iter().enumerate() {
                let symbols = self.compilation.symbols();
                let flags = generic_param_flags(symbols, *parameter) & !0x0003u16;
                let name = symbols.get(*parameter).name.clone();
                self.metadata
                    .add_generic_param(number as u16, flags, owner, &name);
                self.write_constraints(owner, number as u16, *parameter)?;
            }
            // The receiver as the block wrote it: the first parameter of an
            // instance member, which says its name and how it is passed.
            let receiver_symbol = self.block_receiver(block);
            let mut sink = rustlyn_semantics::Diagnostics::new();
            let extended = self.binder.resolve_type_ref(block.extended, &mut sink);
            let mut receiver = self.sig_type(&extended)?;
            let mut names = Vec::new();
            if let Some(symbol) = receiver_symbol {
                receiver = self.parameter_sig(symbol, receiver);
                names.push(self.compilation.symbols().get(symbol).name.clone());
            }
            let signature = method_signature(
                false,
                &SigType::Primitive(ElementType::Void),
                std::slice::from_ref(&receiver),
            );
            let method = self.metadata.add_method(
                method_attributes::PUBLIC
                    | method_attributes::STATIC
                    | method_attributes::HIDE_BY_SIG
                    | method_attributes::SPECIAL_NAME,
                0,
                "<Extension>$",
                &signature,
                Some(returned),
                &names,
            );
            self.mark_with(
                (method.0 & 0x00FF_FFFF) << 5,
                "System.Runtime.CompilerServices.CompilerGeneratedAttribute",
            );
        }
        self.display_generics = Vec::new();
        Ok(())
    }

    /// The marker method of a method a block declared: its signature as the
    /// block wrote it, without the receiver.
    fn write_marker_method(
        &mut self,
        member: SymbolId,
        marker: &str,
        block_generics: usize,
        thrown: u32,
    ) -> Result<(), EmitError> {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        let Some(detail) = symbol.as_method() else {
            return Ok(());
        };
        let instance = detail.takes_receiver;
        let accessibility = symbol.accessibility;
        let name = symbol.name.clone();
        let special = matches!(
            detail.method_kind,
            rustlyn_semantics::MethodKind::Operator | rustlyn_semantics::MethodKind::Conversion
        );
        let own: Vec<SymbolId> = detail
            .type_parameters
            .iter()
            .copied()
            .skip(block_generics)
            .collect();
        let parameters: Vec<SymbolId> = detail
            .parameters
            .iter()
            .copied()
            .skip(usize::from(instance))
            .collect();
        let returns = self.type_of(member);
        self.method_generics = own.clone();
        let returned = self.sig_type(&returns)?;
        let mut written = Vec::new();
        let mut names = Vec::new();
        for parameter in &parameters {
            let ty = self.type_of(*parameter);
            let ty = self.sig_type(&ty)?;
            written.push(self.parameter_sig(*parameter, ty));
            names.push(self.compilation.symbols().get(*parameter).name.clone());
        }
        let signature = generic_method_signature(instance, own.len() as u32, &returned, &written);
        let mut flags = method_flags(accessibility, instance, Modifiers::empty())
            | method_attributes::HIDE_BY_SIG;
        if special {
            flags |= method_attributes::SPECIAL_NAME;
        }
        let token = self
            .metadata
            .add_method(flags, 0, &name, &signature, Some(thrown), &names);
        self.mark_extension_marker((token.0 & 0x00FF_FFFF) << 5, marker);
        let owner = ((token.0 & 0x00FF_FFFF) << 1) | 1;
        for (number, parameter) in own.iter().enumerate() {
            let symbols = self.compilation.symbols();
            let flags = generic_param_flags(symbols, *parameter) & !0x0003u16;
            let name = symbols.get(*parameter).name.clone();
            self.metadata
                .add_generic_param(number as u16, flags, owner, &name);
            self.write_constraints(owner, number as u16, *parameter)?;
        }
        self.method_generics = Vec::new();
        Ok(())
    }

    /// The marker accessors of a property a block declared, and what its
    /// `Property` row needs: the name, the signature, the two accessors.
    fn write_marker_property(
        &mut self,
        member: SymbolId,
        marker: &str,
        thrown: u32,
    ) -> Result<MarkerProperty, EmitError> {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        let name = symbol.name.clone();
        let accessibility = symbol.accessibility;
        let Some(detail) = symbol.as_property() else {
            return Err(EmitError::new("an extension property without detail"));
        };
        let instance = !detail.parameters.is_empty();
        let (has_get, has_set) = (detail.has_get, detail.has_set || detail.has_init);
        let indices: Vec<SymbolId> = detail
            .parameters
            .iter()
            .copied()
            .skip(usize::from(instance))
            .collect();
        let ty = self.type_of(member);
        let value = self.sig_type(&ty)?;
        let mut written = Vec::new();
        let mut names = Vec::new();
        for parameter in &indices {
            let parameter_type = self.type_of(*parameter);
            let sig = self.sig_type(&parameter_type)?;
            written.push(self.parameter_sig(*parameter, sig));
            names.push(self.compilation.symbols().get(*parameter).name.clone());
        }
        let flags = method_flags(accessibility, instance, Modifiers::empty())
            | method_attributes::HIDE_BY_SIG
            | method_attributes::SPECIAL_NAME;
        let mut accessors = [None, None];
        for (at, wanted) in [has_get, has_set].into_iter().enumerate() {
            if !wanted {
                continue;
            }
            let (accessor, signature, parameters) = if at == 0 {
                (
                    format!("get_{name}"),
                    generic_method_signature(instance, 0, &value, &written),
                    names.clone(),
                )
            } else {
                let mut with_value = written.clone();
                with_value.push(value.clone());
                let mut with_name = names.clone();
                with_name.push("value".to_string());
                (
                    format!("set_{name}"),
                    generic_method_signature(
                        instance,
                        0,
                        &SigType::Primitive(ElementType::Void),
                        &with_value,
                    ),
                    with_name,
                )
            };
            let token = self.metadata.add_method(
                flags,
                0,
                &accessor,
                &signature,
                Some(thrown),
                &parameters,
            );
            self.mark_extension_marker((token.0 & 0x00FF_FFFF) << 5, marker);
            accessors[at] = Some(token);
        }
        let signature = property_signature(instance, &value, &written);
        Ok(MarkerProperty {
            name,
            signature,
            getter: accessors[0],
            setter: accessors[1],
            marker: marker.to_string(),
        })
    }

    /// `[ExtensionMarker("<M>$…")]` on a member of a grouping type.
    fn mark_extension_marker(&mut self, parent: u32, marker: &str) {
        let constructor = self.references.member_ref(
            &mut self.metadata,
            "System.Runtime.CompilerServices.ExtensionMarkerAttribute",
            ".ctor",
            &method_signature(
                true,
                &SigType::Primitive(ElementType::Void),
                &[SigType::Primitive(ElementType::String)],
            ),
        );
        let mut blob = vec![0x01, 0x00];
        crate::signature::compress(&mut blob, marker.len() as u32);
        blob.extend_from_slice(marker.as_bytes());
        blob.extend_from_slice(&[0x00, 0x00]);
        // A `CustomAttributeType` tagged 3 is a `MemberRef`.
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }
}

/// Thirty-two hexadecimal digits that tell one name from another and the
/// same name from itself in every build: what a type's name carries of the
/// block it stands for.
fn hash_of(text: &str) -> String {
    let mut lanes = [0xcbf2_9ce4_8422_2325u64, 0x8422_2325_cbf2_9ce4];
    for byte in text.bytes() {
        for (salt, lane) in lanes.iter_mut().enumerate() {
            *lane ^= u64::from(byte) + salt as u64;
            *lane = lane.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    format!("{:016X}{:016X}", lanes[0], lanes[1])
}
