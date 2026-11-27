//! Semantic analysis for Rustlyn: what the names in a syntax tree refer to.
//!
//! The syntax layer answers "what does this text say"; this one answers "what
//! does it mean". It starts with the declaration table — one pass that turns
//! every declaration into a symbol without resolving anything — because a type
//! may be used before it is declared, in the same file or another one.

mod binder;
mod body;
mod bound;
mod checks;
mod compilation;
mod constant;
mod constraints;
mod conversions;
mod corlib;
mod decimal;
mod declare;
mod definite;
mod delegates;
mod flow;
mod fxhash;
mod incremental;
mod metadata;
mod model;
mod nullable;
mod obsolete;
pub mod parallel;
mod pragma;
mod priority;
mod sha256;
mod warnings;
pub use sha256::sha256;
mod snapshot;
mod symbol;
pub mod timing;
mod trees;
mod types;
mod unions;

pub use binder::{Binder, Context, Diagnostics, Resolution, Speculation};
pub use body::BodyBinder;
pub use bound::{
    BoundAttribute, BoundAwaiting, BoundBody, BoundCaseLabel, BoundCatch, BoundDynamic,
    BoundEnumeration, BoundExpression, BoundExpressionKind, BoundLambda, BoundListPattern,
    BoundListSlice, BoundLocalFunction, BoundPattern, BoundPatternKind, BoundRecursivePattern,
    BoundStatement, BoundStatementKind, BoundSwitchArm, BoundSwitchLabel, BoundSwitchSection,
    BoundSymbol, BoundUsingResource, ConstantValue, ConversionKind, DynamicOperation, DynamicUnary,
    IncrementOperator, LocalId, LocalSymbol, LockScope, SpecialConstant, UnaryOperator,
    composite_clauses,
};
pub use compilation::{Compilation, CompilationDiagnostic, CompilationOptions};
pub use conversions::BinaryOperator;
pub use corlib::SpecialType;
pub use delegates::{DelegateParameter, DelegateSignature};
pub use metadata::{ComDefault, Reference, SignatureModifier};
pub use model::{SemanticModel, is_body_owner};
pub use nullable::NullableContexts;
pub use pragma::WarningState;
pub use symbol::{
    Accessibility, CallerInfo, Detail, Event, Field, Local, Location, Method, MethodKind,
    Modifiers, NamedType, Parameter, Property, RefKind, Symbol, SymbolId, SymbolKind, Symbols,
    SynthesizedType, TypeKind, TypeParameter, TypeSyntaxRef, Variance,
};
pub use trees::Trees;
pub use types::{FunctionPointer, TupleElement, Type};
pub use unions::UnionMembers;
