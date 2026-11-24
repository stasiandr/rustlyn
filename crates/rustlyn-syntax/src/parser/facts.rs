//! The bits of the grammar that are lookup tables rather than code: which token
//! starts which expression, how tightly an operator binds, which keywords are
//! modifiers.
//!
//! Roslyn keeps the same knowledge in `SyntaxFacts`, and for the same reason:
//! the parser reads better when "what does `<<=` mean" is a table lookup.

use crate::SyntaxKind;

/// How tightly an operator binds, loosest first.
///
/// The order is Roslyn's `Precedence` enum, which in turn is the order of the
/// operator table in the language specification. Assignment and lambda share
/// the loosest level, which is why `x = y = z` and `x => y => z` both group to
/// the right.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) enum Precedence {
    /// Accepts every expression; also the level of assignment and `=>`.
    Expression = 0,
    Conditional,
    Coalescing,
    ConditionalOr,
    ConditionalAnd,
    LogicalOr,
    LogicalXor,
    LogicalAnd,
    Equality,
    Relational,
    Shift,
    Additive,
    Multiplicative,
    Switch,
    Range,
    Unary,
    Cast,
    Primary,
}

impl Precedence {
    /// The next level up, used to parse the right operand of a left-associative
    /// operator.
    pub(crate) const fn next(self) -> Self {
        match self {
            Self::Expression => Self::Conditional,
            Self::Conditional => Self::Coalescing,
            Self::Coalescing => Self::ConditionalOr,
            Self::ConditionalOr => Self::ConditionalAnd,
            Self::ConditionalAnd => Self::LogicalOr,
            Self::LogicalOr => Self::LogicalXor,
            Self::LogicalXor => Self::LogicalAnd,
            Self::LogicalAnd => Self::Equality,
            Self::Equality => Self::Relational,
            Self::Relational => Self::Shift,
            Self::Shift => Self::Additive,
            Self::Additive => Self::Multiplicative,
            Self::Multiplicative => Self::Switch,
            Self::Switch => Self::Range,
            Self::Range => Self::Unary,
            Self::Unary => Self::Cast,
            Self::Cast | Self::Primary => Self::Primary,
        }
    }
}

/// The expression kind a binary operator token produces.
pub(crate) const fn binary_expression_kind(token: SyntaxKind) -> Option<SyntaxKind> {
    Some(match token {
        SyntaxKind::BarBarToken => SyntaxKind::LogicalOrExpression,
        SyntaxKind::AmpersandAmpersandToken => SyntaxKind::LogicalAndExpression,
        SyntaxKind::BarToken => SyntaxKind::BitwiseOrExpression,
        SyntaxKind::CaretToken => SyntaxKind::ExclusiveOrExpression,
        SyntaxKind::AmpersandToken => SyntaxKind::BitwiseAndExpression,
        SyntaxKind::EqualsEqualsToken => SyntaxKind::EqualsExpression,
        SyntaxKind::ExclamationEqualsToken => SyntaxKind::NotEqualsExpression,
        SyntaxKind::LessThanToken => SyntaxKind::LessThanExpression,
        SyntaxKind::LessThanEqualsToken => SyntaxKind::LessThanOrEqualExpression,
        SyntaxKind::GreaterThanToken => SyntaxKind::GreaterThanExpression,
        SyntaxKind::GreaterThanEqualsToken => SyntaxKind::GreaterThanOrEqualExpression,
        SyntaxKind::LessThanLessThanToken => SyntaxKind::LeftShiftExpression,
        SyntaxKind::GreaterThanGreaterThanToken => SyntaxKind::RightShiftExpression,
        SyntaxKind::GreaterThanGreaterThanGreaterThanToken => {
            SyntaxKind::UnsignedRightShiftExpression
        }
        SyntaxKind::PlusToken => SyntaxKind::AddExpression,
        SyntaxKind::MinusToken => SyntaxKind::SubtractExpression,
        SyntaxKind::AsteriskToken => SyntaxKind::MultiplyExpression,
        SyntaxKind::SlashToken => SyntaxKind::DivideExpression,
        SyntaxKind::PercentToken => SyntaxKind::ModuloExpression,
        SyntaxKind::QuestionQuestionToken => SyntaxKind::CoalesceExpression,
        SyntaxKind::IsKeyword => SyntaxKind::IsExpression,
        SyntaxKind::AsKeyword => SyntaxKind::AsExpression,
        _ => return None,
    })
}

/// The expression kind an assignment operator token produces.
pub(crate) const fn assignment_expression_kind(token: SyntaxKind) -> Option<SyntaxKind> {
    Some(match token {
        SyntaxKind::EqualsToken => SyntaxKind::SimpleAssignmentExpression,
        SyntaxKind::PlusEqualsToken => SyntaxKind::AddAssignmentExpression,
        SyntaxKind::MinusEqualsToken => SyntaxKind::SubtractAssignmentExpression,
        SyntaxKind::AsteriskEqualsToken => SyntaxKind::MultiplyAssignmentExpression,
        SyntaxKind::SlashEqualsToken => SyntaxKind::DivideAssignmentExpression,
        SyntaxKind::PercentEqualsToken => SyntaxKind::ModuloAssignmentExpression,
        SyntaxKind::AmpersandEqualsToken => SyntaxKind::AndAssignmentExpression,
        SyntaxKind::CaretEqualsToken => SyntaxKind::ExclusiveOrAssignmentExpression,
        SyntaxKind::BarEqualsToken => SyntaxKind::OrAssignmentExpression,
        SyntaxKind::LessThanLessThanEqualsToken => SyntaxKind::LeftShiftAssignmentExpression,
        SyntaxKind::GreaterThanGreaterThanEqualsToken => SyntaxKind::RightShiftAssignmentExpression,
        SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken => {
            SyntaxKind::UnsignedRightShiftAssignmentExpression
        }
        SyntaxKind::QuestionQuestionEqualsToken => SyntaxKind::CoalesceAssignmentExpression,
        _ => return None,
    })
}

/// The expression kind a prefix operator token produces.
pub(crate) const fn prefix_unary_expression_kind(token: SyntaxKind) -> Option<SyntaxKind> {
    Some(match token {
        SyntaxKind::PlusToken => SyntaxKind::UnaryPlusExpression,
        SyntaxKind::MinusToken => SyntaxKind::UnaryMinusExpression,
        SyntaxKind::TildeToken => SyntaxKind::BitwiseNotExpression,
        SyntaxKind::ExclamationToken => SyntaxKind::LogicalNotExpression,
        SyntaxKind::PlusPlusToken => SyntaxKind::PreIncrementExpression,
        SyntaxKind::MinusMinusToken => SyntaxKind::PreDecrementExpression,
        SyntaxKind::AsteriskToken => SyntaxKind::PointerIndirectionExpression,
        SyntaxKind::AmpersandToken => SyntaxKind::AddressOfExpression,
        SyntaxKind::CaretToken => SyntaxKind::IndexExpression,
        _ => return None,
    })
}

/// The expression kind a postfix operator token produces.
pub(crate) const fn postfix_unary_expression_kind(token: SyntaxKind) -> Option<SyntaxKind> {
    Some(match token {
        SyntaxKind::PlusPlusToken => SyntaxKind::PostIncrementExpression,
        SyntaxKind::MinusMinusToken => SyntaxKind::PostDecrementExpression,
        SyntaxKind::ExclamationToken => SyntaxKind::SuppressNullableWarningExpression,
        _ => return None,
    })
}

/// The expression kind a literal token produces.
pub(crate) const fn literal_expression_kind(token: SyntaxKind) -> Option<SyntaxKind> {
    Some(match token {
        SyntaxKind::NumericLiteralToken => SyntaxKind::NumericLiteralExpression,
        SyntaxKind::StringLiteralToken
        | SyntaxKind::SingleLineRawStringLiteralToken
        | SyntaxKind::MultiLineRawStringLiteralToken => SyntaxKind::StringLiteralExpression,
        SyntaxKind::Utf8SingleLineRawStringLiteralToken
        | SyntaxKind::Utf8MultiLineRawStringLiteralToken => SyntaxKind::Utf8StringLiteralExpression,
        SyntaxKind::Utf8StringLiteralToken => SyntaxKind::Utf8StringLiteralExpression,
        SyntaxKind::CharacterLiteralToken => SyntaxKind::CharacterLiteralExpression,
        SyntaxKind::TrueKeyword => SyntaxKind::TrueLiteralExpression,
        SyntaxKind::FalseKeyword => SyntaxKind::FalseLiteralExpression,
        SyntaxKind::NullKeyword => SyntaxKind::NullLiteralExpression,
        _ => return None,
    })
}

/// How tightly the operator that produces `expression` binds.
pub(crate) const fn precedence_of(expression: SyntaxKind) -> Precedence {
    match expression {
        SyntaxKind::CoalesceExpression => Precedence::Coalescing,
        SyntaxKind::LogicalOrExpression => Precedence::ConditionalOr,
        SyntaxKind::LogicalAndExpression => Precedence::ConditionalAnd,
        SyntaxKind::BitwiseOrExpression => Precedence::LogicalOr,
        SyntaxKind::ExclusiveOrExpression => Precedence::LogicalXor,
        SyntaxKind::BitwiseAndExpression => Precedence::LogicalAnd,
        SyntaxKind::EqualsExpression | SyntaxKind::NotEqualsExpression => Precedence::Equality,
        SyntaxKind::LessThanExpression
        | SyntaxKind::LessThanOrEqualExpression
        | SyntaxKind::GreaterThanExpression
        | SyntaxKind::GreaterThanOrEqualExpression
        | SyntaxKind::IsExpression
        | SyntaxKind::AsExpression
        | SyntaxKind::IsPatternExpression => Precedence::Relational,
        SyntaxKind::LeftShiftExpression
        | SyntaxKind::RightShiftExpression
        | SyntaxKind::UnsignedRightShiftExpression => Precedence::Shift,
        SyntaxKind::AddExpression | SyntaxKind::SubtractExpression => Precedence::Additive,
        SyntaxKind::MultiplyExpression
        | SyntaxKind::DivideExpression
        | SyntaxKind::ModuloExpression => Precedence::Multiplicative,
        SyntaxKind::SwitchExpression | SyntaxKind::WithExpression => Precedence::Switch,
        SyntaxKind::RangeExpression => Precedence::Range,
        _ => Precedence::Expression,
    }
}

/// Whether equal precedence groups to the right, as `??` and `?:` do.
pub(crate) const fn is_right_associative(expression: SyntaxKind) -> bool {
    matches!(
        expression,
        SyntaxKind::CoalesceExpression | SyntaxKind::ConditionalExpression
    ) || assignment_expression_kind_exists(expression)
}

const fn assignment_expression_kind_exists(expression: SyntaxKind) -> bool {
    matches!(
        expression,
        SyntaxKind::SimpleAssignmentExpression
            | SyntaxKind::AddAssignmentExpression
            | SyntaxKind::SubtractAssignmentExpression
            | SyntaxKind::MultiplyAssignmentExpression
            | SyntaxKind::DivideAssignmentExpression
            | SyntaxKind::ModuloAssignmentExpression
            | SyntaxKind::AndAssignmentExpression
            | SyntaxKind::ExclusiveOrAssignmentExpression
            | SyntaxKind::OrAssignmentExpression
            | SyntaxKind::LeftShiftAssignmentExpression
            | SyntaxKind::RightShiftAssignmentExpression
            | SyntaxKind::UnsignedRightShiftAssignmentExpression
            | SyntaxKind::CoalesceAssignmentExpression
    )
}

/// Whether the token is a built-in type name such as `int` or `string`.
pub(crate) const fn is_predefined_type(token: SyntaxKind) -> bool {
    matches!(
        token,
        SyntaxKind::BoolKeyword
            | SyntaxKind::ByteKeyword
            | SyntaxKind::SByteKeyword
            | SyntaxKind::ShortKeyword
            | SyntaxKind::UShortKeyword
            | SyntaxKind::IntKeyword
            | SyntaxKind::UIntKeyword
            | SyntaxKind::LongKeyword
            | SyntaxKind::ULongKeyword
            | SyntaxKind::DoubleKeyword
            | SyntaxKind::FloatKeyword
            | SyntaxKind::DecimalKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::CharKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::VoidKeyword
    )
}

/// Whether the token is a modifier that needs no context to recognise.
pub(crate) const fn is_reserved_modifier(token: SyntaxKind) -> bool {
    matches!(
        token,
        SyntaxKind::PublicKeyword
            | SyntaxKind::PrivateKeyword
            | SyntaxKind::ProtectedKeyword
            | SyntaxKind::InternalKeyword
            | SyntaxKind::StaticKeyword
            | SyntaxKind::ReadOnlyKeyword
            | SyntaxKind::SealedKeyword
            | SyntaxKind::ConstKeyword
            | SyntaxKind::FixedKeyword
            | SyntaxKind::VolatileKeyword
            | SyntaxKind::NewKeyword
            | SyntaxKind::OverrideKeyword
            | SyntaxKind::AbstractKeyword
            | SyntaxKind::VirtualKeyword
            | SyntaxKind::ExternKeyword
            | SyntaxKind::UnsafeKeyword
            | SyntaxKind::RefKeyword
    )
}

/// Whether the contextual keyword can be a modifier where one is allowed.
///
/// Only *can*: `async` is a modifier in `async void M()` and a variable name in
/// `var async = 1;`, so the parser still has to look at what follows.
pub(crate) const fn is_contextual_modifier(contextual: SyntaxKind) -> bool {
    matches!(
        contextual,
        SyntaxKind::PartialKeyword
            | SyntaxKind::AsyncKeyword
            | SyntaxKind::RequiredKeyword
            | SyntaxKind::FileKeyword
            | SyntaxKind::ScopedKeyword
    )
}

/// Whether the token can begin a type.
pub(crate) const fn can_start_type(token: SyntaxKind) -> bool {
    is_predefined_type(token)
        || matches!(
            token,
            SyntaxKind::IdentifierToken
                | SyntaxKind::OpenParenToken // tuple type
                | SyntaxKind::RefKeyword
                | SyntaxKind::DelegateKeyword
                | SyntaxKind::AsteriskToken
        )
}

/// Whether the token can begin an expression.
///
/// `switch` is absent on purpose: a switch expression needs a governing
/// expression to its left, so `(x) switch` is a parenthesised expression
/// rather than a cast of something.
pub(crate) const fn can_start_expression(token: SyntaxKind) -> bool {
    is_predefined_type(token)
        || literal_expression_kind(token).is_some()
        || prefix_unary_expression_kind(token).is_some()
        || matches!(
            token,
            SyntaxKind::IdentifierToken
                | SyntaxKind::InterpolatedStringStartToken
                | SyntaxKind::InterpolatedVerbatimStringStartToken
                | SyntaxKind::InterpolatedSingleLineRawStringStartToken
                | SyntaxKind::InterpolatedMultiLineRawStringStartToken
                | SyntaxKind::OpenParenToken
                | SyntaxKind::OpenBracketToken
                | SyntaxKind::ThisKeyword
                | SyntaxKind::BaseKeyword
                | SyntaxKind::NewKeyword
                | SyntaxKind::TypeOfKeyword
                | SyntaxKind::SizeOfKeyword
                | SyntaxKind::DefaultKeyword
                | SyntaxKind::CheckedKeyword
                | SyntaxKind::UncheckedKeyword
                | SyntaxKind::MakeRefKeyword
                | SyntaxKind::RefTypeKeyword
                | SyntaxKind::RefValueKeyword
                | SyntaxKind::ArgListKeyword
                | SyntaxKind::DelegateKeyword
                | SyntaxKind::ThrowKeyword
                | SyntaxKind::StackAllocKeyword
                | SyntaxKind::RefKeyword
                | SyntaxKind::DotDotToken
        )
}
