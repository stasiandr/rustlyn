//! Types as the binder sees them.
//!
//! A [`SymbolId`] names a *declaration*: `List<T>` is one symbol however many
//! times it is used. A [`Type`] is what a particular use of it means —
//! `List<int>` and `List<string>` are two types built from that one symbol, and
//! `int[]` is a type with no symbol of its own at all. Roslyn draws the same
//! line between a named type's definition and its constructions.

use std::collections::HashMap;

use crate::corlib::SpecialType;
use crate::symbol::{RefKind, SymbolId, SymbolKind, Symbols, TypeKind};

/// A type, as written or as inferred.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Type {
    /// A type that could not be worked out. It converts to and from anything,
    /// so one mistake does not turn into a cascade of them.
    Error,
    /// A named type, with its type arguments if it has any.
    Named {
        symbol: SymbolId,
        type_arguments: Vec<Type>,
    },
    Array {
        element: Box<Type>,
        rank: usize,
    },
    Pointer(Box<Type>),
    /// A use of a type parameter, such as the `T` inside `class C<T>`.
    TypeParameter(SymbolId),
    /// `(int x, string y)`
    Tuple(Vec<TupleElement>),
    /// `ref T`, which is a type only in a signature.
    ByRef(Box<Type>),
    /// The type of the `null` literal, which converts to any reference type
    /// and has no name of its own.
    Null,
    Void,
    /// `dynamic`: an `object` to the runtime, whose operations are bound
    /// when the program runs rather than when it is compiled (§8.2.4).
    Dynamic,
    /// `delegate*<int, string>`: the address of a method, which is called
    /// with `calli` and a signature of its own rather than through an object.
    FunctionPointer(Box<FunctionPointer>),
}

/// What a function pointer type says about the methods it points at: how
/// they are called, what they take and what they give back.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FunctionPointer {
    /// The calling convention as a method signature spells it (§II.23.2.3):
    /// 0 is managed, 1 to 4 are `Cdecl`, `Stdcall`, `Thiscall` and
    /// `Fastcall`, and 9 is `unmanaged` with the platform's default.
    pub convention: u8,
    /// The `CallConv*` types an `unmanaged[...]` names beyond what the
    /// convention byte can say, such as `SuppressGCTransition`, by the
    /// name after `CallConv`. The signature carries them as `modopt`s on the
    /// return type.
    pub modifiers: Vec<String>,
    pub returns: Type,
    /// `ref` or `ref readonly` (`In`) on the return.
    pub returns_ref: RefKind,
    pub parameters: Vec<(RefKind, Type)>,
}

impl FunctionPointer {
    /// Every type the signature names: the return first, then each
    /// parameter's.
    pub fn types(&self) -> impl Iterator<Item = &Type> {
        std::iter::once(&self.returns).chain(self.parameters.iter().map(|(_, ty)| ty))
    }

    /// The same signature with every type in it mapped.
    #[must_use]
    pub fn map(&self, mut each: impl FnMut(&Type) -> Type) -> Self {
        Self {
            convention: self.convention,
            modifiers: self.modifiers.clone(),
            returns: each(&self.returns),
            returns_ref: self.returns_ref,
            parameters: self
                .parameters
                .iter()
                .map(|(kind, ty)| (*kind, each(ty)))
                .collect(),
        }
    }
}

/// One element of a tuple type, with the name the source gave it.
///
/// The name is not part of the type. `(int a, string b)` and `(int, string)`
/// are the same type to the runtime and to the language: §8.3.11 says the
/// names are there for whoever reads the code, and a `ValueTuple<int, string>`
/// is all either one is. So equality — and the hash that has to agree with it
/// — looks only at the element types, and an `ImmutableArray<(Step, int n)>`
/// is an `ImmutableArray<(Step s, int n)>` wherever one is wanted.
#[derive(Clone, Eq, Debug)]
pub struct TupleElement {
    pub name: Option<String>,
    pub ty: Type,
}

impl PartialEq for TupleElement {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty
    }
}

impl std::hash::Hash for TupleElement {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ty.hash(state);
    }
}

impl Type {
    /// A named type with no type arguments.
    #[must_use]
    pub fn named(symbol: SymbolId) -> Self {
        Self::Named {
            symbol,
            type_arguments: Vec::new(),
        }
    }

    #[must_use]
    pub const fn is_error(&self) -> bool {
        matches!(self, Self::Error)
    }

    /// The declaration behind a named type, if there is one.
    #[must_use]
    pub const fn symbol(&self) -> Option<SymbolId> {
        match self {
            Self::Named { symbol, .. } | Self::TypeParameter(symbol) => Some(*symbol),
            _ => None,
        }
    }

    /// Whether values of this type are held by reference, which decides
    /// whether `null` converts to it.
    #[must_use]
    pub fn is_reference_type(&self, symbols: &Symbols) -> bool {
        match self {
            Self::Array { .. } | Self::Null | Self::Pointer(_) | Self::Dynamic => true,
            Self::Named { symbol, .. } => symbols
                .get(*symbol)
                .type_kind()
                .is_some_and(TypeKind::is_reference_type),
            // `where T : class` says which it is. Without a constraint a type
            // parameter could be either, so the safe answer is no.
            Self::TypeParameter(symbol) => symbols
                .get(*symbol)
                .as_type_parameter()
                .is_some_and(|detail| detail.reference_type),
            Self::Tuple(_) | Self::Void | Self::Error | Self::FunctionPointer(_) => false,
            Self::ByRef(inner) => inner.is_reference_type(symbols),
        }
    }

    /// Replaces type parameters with the arguments given for them.
    ///
    /// This is what makes `List<string>.this[int]` return a `string`: the
    /// indexer is declared as returning `T`, and the receiver says what `T` is.
    #[must_use]
    pub fn substitute(&self, arguments: &HashMap<SymbolId, Self>) -> Self {
        if arguments.is_empty() {
            return self.clone();
        }
        match self {
            Self::TypeParameter(symbol) => arguments
                .get(symbol)
                .cloned()
                .unwrap_or_else(|| self.clone()),
            Self::Named {
                symbol,
                type_arguments,
            } => Self::Named {
                symbol: *symbol,
                type_arguments: type_arguments
                    .iter()
                    .map(|argument| argument.substitute(arguments))
                    .collect(),
            },
            Self::Array { element, rank } => Self::Array {
                element: Box::new(element.substitute(arguments)),
                rank: *rank,
            },
            Self::Pointer(inner) => Self::Pointer(Box::new(inner.substitute(arguments))),
            Self::ByRef(inner) => Self::ByRef(Box::new(inner.substitute(arguments))),
            Self::Tuple(elements) => Self::Tuple(
                elements
                    .iter()
                    .map(|element| TupleElement {
                        name: element.name.clone(),
                        ty: element.ty.substitute(arguments),
                    })
                    .collect(),
            ),
            Self::FunctionPointer(pointer) => {
                Self::FunctionPointer(Box::new(pointer.map(|ty| ty.substitute(arguments))))
            }
            Self::Error | Self::Null | Self::Void | Self::Dynamic => self.clone(),
        }
    }

    /// What reading this gives back.
    ///
    /// `ref T M()` returns a variable rather than a value, and C# calls that
    /// variable a `T`: only a `ref` assignment cares about the difference, and
    /// that is spelled out in the syntax rather than carried in the type.
    #[must_use]
    pub fn value(&self) -> &Self {
        match self {
            Self::ByRef(inner) => inner,
            other => other,
        }
    }

    /// How the type reads in a diagnostic.
    #[must_use]
    pub fn display(&self, symbols: &Symbols) -> String {
        self.display_by(symbols, &|_, _| None)
    }

    /// [`Type::display`], with `named` asked first how a named type with
    /// these type arguments reads, at every depth; `None` is the usual way.
    #[must_use]
    pub fn display_by(
        &self,
        symbols: &Symbols,
        named: &dyn Fn(SymbolId, &[Self]) -> Option<String>,
    ) -> String {
        let display = |ty: &Self| ty.display_by(symbols, named);
        match self {
            Self::Error => "?".to_string(),
            Self::Void => "void".to_string(),
            Self::Dynamic => "dynamic".to_string(),
            Self::Null => "<null>".to_string(),
            Self::TypeParameter(symbol) => symbols.get(*symbol).name.clone(),
            Self::Pointer(inner) => format!("{}*", display(inner)),
            Self::ByRef(inner) => format!("ref {}", display(inner)),
            Self::FunctionPointer(pointer) => {
                let convention = match pointer.convention {
                    0 => String::new(),
                    1 => " unmanaged[Cdecl]".to_string(),
                    2 => " unmanaged[Stdcall]".to_string(),
                    3 => " unmanaged[Thiscall]".to_string(),
                    4 => " unmanaged[Fastcall]".to_string(),
                    _ if pointer.modifiers.is_empty() => " unmanaged".to_string(),
                    _ => format!(" unmanaged[{}]", pointer.modifiers.join(", ")),
                };
                let with_ref = |kind: RefKind, ty: &Self, returned: bool| {
                    let prefix = match kind {
                        RefKind::None => "",
                        RefKind::Ref => "ref ",
                        RefKind::Out => "out ",
                        RefKind::In if returned => "ref readonly ",
                        RefKind::In => "in ",
                    };
                    format!("{prefix}{}", display(ty))
                };
                let mut parts: Vec<_> = pointer
                    .parameters
                    .iter()
                    .map(|(kind, ty)| with_ref(*kind, ty, false))
                    .collect();
                parts.push(with_ref(pointer.returns_ref, &pointer.returns, true));
                format!("delegate*{convention}<{}>", parts.join(", "))
            }
            Self::Array { element, rank } => {
                let commas = ",".repeat(rank.saturating_sub(1));
                format!("{}[{commas}]", display(element))
            }
            Self::Tuple(elements) => {
                let parts: Vec<_> = elements
                    .iter()
                    .map(|element| match &element.name {
                        Some(name) => format!("{} {name}", display(&element.ty)),
                        None => display(&element.ty),
                    })
                    .collect();
                format!("({})", parts.join(", "))
            }
            Self::Named {
                symbol,
                type_arguments,
            } => {
                if let Some(shown) = named(*symbol, type_arguments) {
                    return shown;
                }
                let name = display_name(symbols, *symbol);
                if type_arguments.is_empty() {
                    name
                } else {
                    let arguments: Vec<_> = type_arguments.iter().map(display).collect();
                    format!("{name}<{}>", arguments.join(", "))
                }
            }
        }
    }
}

/// A named type's name with its containing types, but without its namespace,
/// which is how C# diagnostics spell it.
///
/// The built-in types read as their keywords, so a message says `int` rather
/// than `System.Int32`, as `csc` does.
fn display_name(symbols: &Symbols, symbol: SymbolId) -> String {
    let qualified = symbols.qualified_name(symbol);
    if let Some(special) = SpecialType::ALL
        .iter()
        .find(|special| special.metadata_name() == qualified)
    {
        return special.keyword().to_string();
    }

    let mut parts = vec![symbols.get(symbol).name.clone()];
    let mut current = symbols.get(symbol).container;
    while let Some(container) = current {
        let parent = symbols.get(container);
        if parent.kind != SymbolKind::NamedType {
            break;
        }
        parts.push(parent.name.clone());
        current = parent.container;
    }
    parts.reverse();
    parts.join(".")
}
