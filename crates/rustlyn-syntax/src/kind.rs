//! Every kind of node, token and trivia the C# grammar can produce.
//!
//! The names mirror Roslyn's `SyntaxKind` so that the two can be compared
//! side by side; node kinds are added as the parser learns to produce them.

macro_rules! define_kinds {
    ($(
        $group:literal $predicate:ident $all:ident {
            $( $name:ident $( = $text:literal )? ),* $(,)?
        }
    )*) => {
        /// The classification of a syntax element.
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        #[repr(u16)]
        #[non_exhaustive]
        pub enum SyntaxKind {
            $( $( $name, )* )*
        }

        impl SyntaxKind {
            $(
                #[doc = concat!("Whether this kind is ", $group, ".")]
                #[must_use]
                pub const fn $predicate(self) -> bool {
                    matches!(self, $( SyntaxKind::$name )|* )
                }

                #[doc = concat!("Every kind that is ", $group, ".")]
                pub const $all: &'static [SyntaxKind] = &[ $( SyntaxKind::$name, )* ];
            )*

            /// The fixed text of a kind that always spells the same way, such as
            /// a keyword or an operator. Identifiers and literals return `None`
            /// because their text comes from the source.
            #[must_use]
            pub const fn text(self) -> Option<&'static str> {
                match self {
                    $( $( $( SyntaxKind::$name => Some($text), )? )* )*
                    _ => None,
                }
            }
        }

        /// The kind spelled exactly `text`, if any.
        #[must_use]
        pub fn kind_from_text(text: &str) -> Option<SyntaxKind> {
            match text {
                $( $( $( $text => Some(SyntaxKind::$name), )? )* )*
                _ => None,
            }
        }
    };
}

define_kinds! {
    "a placeholder" is_none NONE {
        None,
    }

    "punctuation" is_punctuation PUNCTUATION {
        TildeToken = "~",
        ExclamationToken = "!",
        DollarToken = "$",
        PercentToken = "%",
        CaretToken = "^",
        AmpersandToken = "&",
        AsteriskToken = "*",
        OpenParenToken = "(",
        CloseParenToken = ")",
        MinusToken = "-",
        PlusToken = "+",
        EqualsToken = "=",
        OpenBraceToken = "{",
        CloseBraceToken = "}",
        OpenBracketToken = "[",
        CloseBracketToken = "]",
        BarToken = "|",
        BackslashToken = "\\",
        ColonToken = ":",
        SemicolonToken = ";",
        DoubleQuoteToken = "\"",
        SingleQuoteToken = "'",
        LessThanToken = "<",
        CommaToken = ",",
        GreaterThanToken = ">",
        DotToken = ".",
        QuestionToken = "?",
        HashToken = "#",
        SlashToken = "/",
        DotDotToken = "..",
        BarBarToken = "||",
        AmpersandAmpersandToken = "&&",
        MinusMinusToken = "--",
        PlusPlusToken = "++",
        ColonColonToken = "::",
        QuestionQuestionToken = "??",
        MinusGreaterThanToken = "->",
        ExclamationEqualsToken = "!=",
        EqualsEqualsToken = "==",
        EqualsGreaterThanToken = "=>",
        LessThanEqualsToken = "<=",
        LessThanLessThanToken = "<<",
        LessThanLessThanEqualsToken = "<<=",
        GreaterThanEqualsToken = ">=",
        GreaterThanGreaterThanToken = ">>",
        GreaterThanGreaterThanEqualsToken = ">>=",
        GreaterThanGreaterThanGreaterThanToken = ">>>",
        GreaterThanGreaterThanGreaterThanEqualsToken = ">>>=",
        SlashEqualsToken = "/=",
        AsteriskEqualsToken = "*=",
        BarEqualsToken = "|=",
        AmpersandEqualsToken = "&=",
        PlusEqualsToken = "+=",
        MinusEqualsToken = "-=",
        CaretEqualsToken = "^=",
        PercentEqualsToken = "%=",
        QuestionQuestionEqualsToken = "??=",
    }

    "a reserved keyword" is_reserved_keyword RESERVED_KEYWORDS {
        BoolKeyword = "bool",
        ByteKeyword = "byte",
        SByteKeyword = "sbyte",
        ShortKeyword = "short",
        UShortKeyword = "ushort",
        IntKeyword = "int",
        UIntKeyword = "uint",
        LongKeyword = "long",
        ULongKeyword = "ulong",
        DoubleKeyword = "double",
        FloatKeyword = "float",
        DecimalKeyword = "decimal",
        StringKeyword = "string",
        CharKeyword = "char",
        VoidKeyword = "void",
        ObjectKeyword = "object",
        TypeOfKeyword = "typeof",
        SizeOfKeyword = "sizeof",
        NullKeyword = "null",
        TrueKeyword = "true",
        FalseKeyword = "false",
        IfKeyword = "if",
        ElseKeyword = "else",
        WhileKeyword = "while",
        ForKeyword = "for",
        ForEachKeyword = "foreach",
        DoKeyword = "do",
        SwitchKeyword = "switch",
        CaseKeyword = "case",
        DefaultKeyword = "default",
        TryKeyword = "try",
        CatchKeyword = "catch",
        FinallyKeyword = "finally",
        LockKeyword = "lock",
        GotoKeyword = "goto",
        BreakKeyword = "break",
        ContinueKeyword = "continue",
        ReturnKeyword = "return",
        ThrowKeyword = "throw",
        PublicKeyword = "public",
        PrivateKeyword = "private",
        InternalKeyword = "internal",
        ProtectedKeyword = "protected",
        StaticKeyword = "static",
        ReadOnlyKeyword = "readonly",
        SealedKeyword = "sealed",
        ConstKeyword = "const",
        FixedKeyword = "fixed",
        StackAllocKeyword = "stackalloc",
        VolatileKeyword = "volatile",
        NewKeyword = "new",
        OverrideKeyword = "override",
        AbstractKeyword = "abstract",
        VirtualKeyword = "virtual",
        EventKeyword = "event",
        ExternKeyword = "extern",
        RefKeyword = "ref",
        OutKeyword = "out",
        InKeyword = "in",
        IsKeyword = "is",
        AsKeyword = "as",
        ParamsKeyword = "params",
        ArgListKeyword = "__arglist",
        MakeRefKeyword = "__makeref",
        RefTypeKeyword = "__reftype",
        RefValueKeyword = "__refvalue",
        ThisKeyword = "this",
        BaseKeyword = "base",
        NamespaceKeyword = "namespace",
        UsingKeyword = "using",
        ClassKeyword = "class",
        StructKeyword = "struct",
        InterfaceKeyword = "interface",
        EnumKeyword = "enum",
        DelegateKeyword = "delegate",
        CheckedKeyword = "checked",
        UncheckedKeyword = "unchecked",
        UnsafeKeyword = "unsafe",
        OperatorKeyword = "operator",
        ExplicitKeyword = "explicit",
        ImplicitKeyword = "implicit",
    }

    "a contextual keyword" is_contextual_keyword CONTEXTUAL_KEYWORDS {
        YieldKeyword = "yield",
        PartialKeyword = "partial",
        AliasKeyword = "alias",
        GlobalKeyword = "global",
        AssemblyKeyword = "assembly",
        ModuleKeyword = "module",
        TypeKeyword = "type",
        FieldKeyword = "field",
        MethodKeyword = "method",
        ParamKeyword = "param",
        PropertyKeyword = "property",
        TypeVarKeyword = "typevar",
        GetKeyword = "get",
        SetKeyword = "set",
        AddKeyword = "add",
        RemoveKeyword = "remove",
        WhereKeyword = "where",
        FromKeyword = "from",
        GroupKeyword = "group",
        JoinKeyword = "join",
        IntoKeyword = "into",
        LetKeyword = "let",
        ByKeyword = "by",
        SelectKeyword = "select",
        OrderByKeyword = "orderby",
        OnKeyword = "on",
        EqualsKeyword = "equals",
        AscendingKeyword = "ascending",
        DescendingKeyword = "descending",
        NameOfKeyword = "nameof",
        AsyncKeyword = "async",
        AwaitKeyword = "await",
        WhenKeyword = "when",
        OrKeyword = "or",
        AndKeyword = "and",
        NotKeyword = "not",
        WithKeyword = "with",
        InitKeyword = "init",
        RecordKeyword = "record",
        ManagedKeyword = "managed",
        UnmanagedKeyword = "unmanaged",
        RequiredKeyword = "required",
        ScopedKeyword = "scoped",
        FileKeyword = "file",
        AllowsKeyword = "allows",
        ExtensionKeyword = "extension",
        VarKeyword = "var",
        UnderscoreToken = "_",
    }

    "a preprocessing keyword" is_preprocessor_keyword PREPROCESSOR_KEYWORDS {
        ElifKeyword = "elif",
        EndIfKeyword = "endif",
        RegionKeyword = "region",
        EndRegionKeyword = "endregion",
        DefineKeyword = "define",
        UndefKeyword = "undef",
        WarningKeyword = "warning",
        ErrorKeyword = "error",
        LineKeyword = "line",
        PragmaKeyword = "pragma",
        HiddenKeyword = "hidden",
        ChecksumKeyword = "checksum",
        DisableKeyword = "disable",
        RestoreKeyword = "restore",
        ReferenceKeyword = "reference",
        LoadKeyword = "load",
        NullableKeyword = "nullable",
        EnableKeyword = "enable",
        WarningsKeyword = "warnings",
        AnnotationsKeyword = "annotations",
    }

    "a literal token" is_literal_token LITERAL_TOKENS {
        NumericLiteralToken,
        CharacterLiteralToken,
        StringLiteralToken,
        Utf8StringLiteralToken,
        SingleLineRawStringLiteralToken,
        MultiLineRawStringLiteralToken,
        Utf8SingleLineRawStringLiteralToken,
        Utf8MultiLineRawStringLiteralToken,
    }

    "a token without fixed text" is_other_token OTHER_TOKENS {
        IdentifierToken,
        InterpolatedStringStartToken,
        InterpolatedVerbatimStringStartToken,
        InterpolatedSingleLineRawStringStartToken,
        InterpolatedMultiLineRawStringStartToken,
        InterpolatedStringTextToken,
        InterpolatedStringEndToken,
        InterpolatedRawStringEndToken,
        EndOfDirectiveToken,
        EndOfFileToken,
        BadToken,
    }

    "trivia" is_trivia TRIVIA {
        WhitespaceTrivia,
        EndOfLineTrivia,
        SingleLineCommentTrivia,
        MultiLineCommentTrivia,
        SingleLineDocumentationCommentTrivia,
        MultiLineDocumentationCommentTrivia,
        DisabledTextTrivia,
        PreprocessingMessageTrivia,
        ShebangDirectiveTrivia,
        IgnoredDirectiveTrivia,
        IfDirectiveTrivia,
        ElifDirectiveTrivia,
        ElseDirectiveTrivia,
        EndIfDirectiveTrivia,
        RegionDirectiveTrivia,
        EndRegionDirectiveTrivia,
        DefineDirectiveTrivia,
        UndefDirectiveTrivia,
        ErrorDirectiveTrivia,
        WarningDirectiveTrivia,
        LineDirectiveTrivia,
        PragmaWarningDirectiveTrivia,
        PragmaChecksumDirectiveTrivia,
        ReferenceDirectiveTrivia,
        LoadDirectiveTrivia,
        NullableDirectiveTrivia,
        BadDirectiveTrivia,
    }

    "a name or type" is_type_node TYPE_NODES {
        IdentifierName,
        QualifiedName,
        GenericName,
        AliasQualifiedName,
        TypeArgumentList,
        PredefinedType,
        ArrayType,
        ArrayRankSpecifier,
        PointerType,
        NullableType,
        TupleType,
        TupleElement,
        RefType,
        ScopedType,
        FunctionPointerType,
        OmittedTypeArgument,
    }

    "an expression" is_expression_node EXPRESSION_NODES {
        ParenthesizedExpression,
        ConditionalExpression,
        InvocationExpression,
        ElementAccessExpression,
        ImplicitElementAccess,
        CastExpression,
        AnonymousMethodExpression,
        SimpleLambdaExpression,
        ParenthesizedLambdaExpression,
        ObjectCreationExpression,
        ImplicitObjectCreationExpression,
        AnonymousObjectCreationExpression,
        ArrayCreationExpression,
        ImplicitArrayCreationExpression,
        StackAllocArrayCreationExpression,
        ImplicitStackAllocArrayCreationExpression,
        OmittedArraySizeExpression,
        InterpolatedStringExpression,
        QueryExpression,
        InterpolatedStringText,
        Interpolation,
        InterpolationAlignmentClause,
        InterpolationFormatClause,
        IsPatternExpression,
        RangeExpression,
        AddExpression,
        SubtractExpression,
        MultiplyExpression,
        DivideExpression,
        ModuloExpression,
        LeftShiftExpression,
        RightShiftExpression,
        UnsignedRightShiftExpression,
        LogicalOrExpression,
        LogicalAndExpression,
        BitwiseOrExpression,
        BitwiseAndExpression,
        ExclusiveOrExpression,
        EqualsExpression,
        NotEqualsExpression,
        LessThanExpression,
        LessThanOrEqualExpression,
        GreaterThanExpression,
        GreaterThanOrEqualExpression,
        IsExpression,
        AsExpression,
        CoalesceExpression,
        SimpleMemberAccessExpression,
        PointerMemberAccessExpression,
        ConditionalAccessExpression,
        MemberBindingExpression,
        ElementBindingExpression,
        SimpleAssignmentExpression,
        AddAssignmentExpression,
        SubtractAssignmentExpression,
        MultiplyAssignmentExpression,
        DivideAssignmentExpression,
        ModuloAssignmentExpression,
        AndAssignmentExpression,
        ExclusiveOrAssignmentExpression,
        OrAssignmentExpression,
        LeftShiftAssignmentExpression,
        RightShiftAssignmentExpression,
        UnsignedRightShiftAssignmentExpression,
        CoalesceAssignmentExpression,
        UnaryPlusExpression,
        UnaryMinusExpression,
        BitwiseNotExpression,
        LogicalNotExpression,
        PreIncrementExpression,
        PreDecrementExpression,
        PointerIndirectionExpression,
        AddressOfExpression,
        PostIncrementExpression,
        PostDecrementExpression,
        AwaitExpression,
        IndexExpression,
        ThisExpression,
        BaseExpression,
        ArgListExpression,
        NumericLiteralExpression,
        StringLiteralExpression,
        Utf8StringLiteralExpression,
        CharacterLiteralExpression,
        TrueLiteralExpression,
        FalseLiteralExpression,
        NullLiteralExpression,
        DefaultLiteralExpression,
        TypeOfExpression,
        SizeOfExpression,
        CheckedExpression,
        UncheckedExpression,
        DefaultExpression,
        MakeRefExpression,
        RefValueExpression,
        RefTypeExpression,
        ThrowExpression,
        RefExpression,
        DeclarationExpression,
        TupleExpression,
        SwitchExpression,
        WithExpression,
        SuppressNullableWarningExpression,
        CollectionExpression,
        ExpressionElement,
        SpreadElement,
        // `with(capacity: 16)` among a collection expression's elements:
        // the arguments the collection is made with (C# 15).
        WithElement,
        ObjectInitializerExpression,
        CollectionInitializerExpression,
        ArrayInitializerExpression,
        ComplexElementInitializerExpression,
        WithInitializerExpression,
    }

    "a pattern" is_pattern_node PATTERN_NODES {
        DeclarationPattern,
        ConstantPattern,
        DiscardPattern,
        VarPattern,
        TypePattern,
        RecursivePattern,
        ParenthesizedPattern,
        RelationalPattern,
        OrPattern,
        AndPattern,
        NotPattern,
        ListPattern,
        SlicePattern,
        PropertyPatternClause,
        Subpattern,
        PositionalPatternClause,
        SingleVariableDesignation,
        ParenthesizedVariableDesignation,
        DiscardDesignation,
        WhenClause,
        SwitchExpressionArm,
    }

    "a statement" is_statement_node STATEMENT_NODES {
        Block,
        LocalDeclarationStatement,
        ExpressionStatement,
        EmptyStatement,
        LabeledStatement,
        GotoStatement,
        GotoCaseStatement,
        GotoDefaultStatement,
        BreakStatement,
        ContinueStatement,
        ReturnStatement,
        YieldReturnStatement,
        YieldBreakStatement,
        ThrowStatement,
        WhileStatement,
        DoStatement,
        ForStatement,
        ForEachStatement,
        ForEachVariableStatement,
        UsingStatement,
        FixedStatement,
        CheckedStatement,
        UncheckedStatement,
        UnsafeStatement,
        LockStatement,
        IfStatement,
        SwitchStatement,
        TryStatement,
        LocalFunctionStatement,
        GlobalStatement,
    }

    "a declaration" is_declaration_node DECLARATION_NODES {
        CompilationUnit,
        NamespaceDeclaration,
        FileScopedNamespaceDeclaration,
        UsingDirective,
        ExternAliasDirective,
        ClassDeclaration,
        StructDeclaration,
        InterfaceDeclaration,
        EnumDeclaration,
        DelegateDeclaration,
        RecordDeclaration,
        RecordStructDeclaration,
        EnumMemberDeclaration,
        FieldDeclaration,
        EventFieldDeclaration,
        MethodDeclaration,
        OperatorDeclaration,
        ConversionOperatorDeclaration,
        ConstructorDeclaration,
        DestructorDeclaration,
        PropertyDeclaration,
        EventDeclaration,
        IndexerDeclaration,
        GetAccessorDeclaration,
        SetAccessorDeclaration,
        InitAccessorDeclaration,
        AddAccessorDeclaration,
        RemoveAccessorDeclaration,
        UnknownAccessorDeclaration,
        IncompleteMember,
        ExtensionBlockDeclaration,
    }

    "a structural node" is_structural_node STRUCTURAL_NODES {
        ArgumentList,
        BracketedArgumentList,
        Argument,
        NameColon,
        NameEquals,
        ExpressionColon,
        ElseClause,
        SwitchSection,
        CaseSwitchLabel,
        CasePatternSwitchLabel,
        DefaultSwitchLabel,
        CatchClause,
        CatchDeclaration,
        CatchFilterClause,
        FinallyClause,
        VariableDeclaration,
        VariableDeclarator,
        EqualsValueClause,
        AttributeList,
        AttributeTargetSpecifier,
        Attribute,
        AttributeArgumentList,
        AttributeArgument,
        AnonymousObjectMemberDeclarator,
        BaseList,
        SimpleBaseType,
        PrimaryConstructorBaseType,
        TypeParameterConstraintClause,
        ConstructorConstraint,
        ClassConstraint,
        StructConstraint,
        TypeConstraint,
        DefaultConstraint,
        AllowsConstraintClause,
        RefStructConstraint,
        FunctionPointerCallingConvention,
        FunctionPointerUnmanagedCallingConventionList,
        FunctionPointerUnmanagedCallingConvention,
        FunctionPointerParameterList,
        FunctionPointerParameter,
        ExplicitInterfaceSpecifier,
        AccessorList,
        ParameterList,
        BracketedParameterList,
        Parameter,
        TypeParameterList,
        TypeParameter,
        ArrowExpressionClause,
        QueryBody,
        FromClause,
        LetClause,
        JoinClause,
        JoinIntoClause,
        WhereClause,
        OrderByClause,
        AscendingOrdering,
        DescendingOrdering,
        SelectClause,
        GroupClause,
        QueryContinuation,
        BaseConstructorInitializer,
        ThisConstructorInitializer,
        // Produced by the parser, never by the lexer: a run of tokens the
        // grammar had no place for, kept so the tree still covers the file.
        SkippedTokensTrivia,
    }
}

impl SyntaxKind {
    /// Whether the kind is any kind of keyword: reserved, contextual or one of
    /// the identifiers that only mean something inside a directive.
    #[must_use]
    pub const fn is_any_keyword(self) -> bool {
        self.is_reserved_keyword() || self.is_contextual_keyword() || self.is_preprocessor_keyword()
    }

    /// Whether the kind can stand where an expression is expected.
    ///
    /// A name is both a type and an expression — `Console` names a type in
    /// `Console.WriteLine` and a value nowhere, but the grammar reaches it
    /// through the same node either way, and so does `int` in
    /// `int.TryParse`. Roslyn says the same thing with its class hierarchy,
    /// where `NameSyntax` derives from `TypeSyntax` derives from
    /// `ExpressionSyntax`.
    #[must_use]
    pub const fn is_expression(self) -> bool {
        self.is_expression_node()
            || matches!(
                self,
                Self::IdentifierName
                    | Self::GenericName
                    | Self::QualifiedName
                    | Self::AliasQualifiedName
                    | Self::PredefinedType
            )
    }

    /// Whether the kind denotes an interior node rather than a token or
    /// trivia.
    #[must_use]
    pub const fn is_node(self) -> bool {
        self.is_type_node()
            || self.is_expression_node()
            || self.is_pattern_node()
            || self.is_statement_node()
            || self.is_declaration_node()
            || self.is_structural_node()
    }

    /// Whether the kind denotes a token rather than trivia or a node.
    ///
    /// Contextual and preprocessing keywords are lexed as identifiers, so they
    /// are not tokens in their own right; they show up as a token's
    /// [`contextual_kind`](crate::Token::contextual_kind).
    #[must_use]
    pub const fn is_token(self) -> bool {
        self.is_punctuation()
            || self.is_reserved_keyword()
            || self.is_literal_token()
            || self.is_other_token()
    }

    /// The fixed text of the kind, or its name when it has none. Intended for
    /// diagnostics and debugging output.
    #[must_use]
    pub fn describe(self) -> String {
        match self.text() {
            Some(text) => text.to_string(),
            None => format!("{self:?}"),
        }
    }
}

/// The reserved keyword spelled `text`, if there is one.
///
/// Returns `None` for contextual keywords: those are identifiers that the
/// parser reinterprets depending on where they appear.
#[must_use]
pub fn reserved_keyword_kind(text: &str) -> Option<SyntaxKind> {
    kind_from_text(text).filter(|kind| kind.is_reserved_keyword())
}

/// The contextual keyword spelled `text`, if there is one.
#[must_use]
pub fn contextual_keyword_kind(text: &str) -> Option<SyntaxKind> {
    kind_from_text(text).filter(|kind| kind.is_contextual_keyword())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_round_trips() {
        for kind in SyntaxKind::PUNCTUATION
            .iter()
            .chain(SyntaxKind::RESERVED_KEYWORDS)
            .chain(SyntaxKind::CONTEXTUAL_KEYWORDS)
            .chain(SyntaxKind::PREPROCESSOR_KEYWORDS)
        {
            let text = kind.text().expect("kind should have fixed text");
            assert_eq!(kind_from_text(text), Some(*kind), "for {text:?}");
        }
    }

    #[test]
    fn tokens_without_fixed_text() {
        assert_eq!(SyntaxKind::IdentifierToken.text(), None);
        assert_eq!(SyntaxKind::NumericLiteralToken.text(), None);
        assert_eq!(SyntaxKind::EndOfFileToken.text(), None);
    }

    #[test]
    fn classification() {
        assert!(SyntaxKind::ClassKeyword.is_reserved_keyword());
        assert!(!SyntaxKind::ClassKeyword.is_contextual_keyword());
        assert!(SyntaxKind::VarKeyword.is_contextual_keyword());
        assert!(SyntaxKind::VarKeyword.is_any_keyword());
        assert!(!SyntaxKind::VarKeyword.is_token());
        assert!(SyntaxKind::PlusEqualsToken.is_punctuation());
        assert!(SyntaxKind::WhitespaceTrivia.is_trivia());
        assert!(!SyntaxKind::WhitespaceTrivia.is_token());
    }

    #[test]
    fn keyword_lookup_separates_reserved_from_contextual() {
        assert_eq!(
            reserved_keyword_kind("class"),
            Some(SyntaxKind::ClassKeyword)
        );
        assert_eq!(reserved_keyword_kind("var"), None);
        assert_eq!(contextual_keyword_kind("var"), Some(SyntaxKind::VarKeyword));
        assert_eq!(
            contextual_keyword_kind("_"),
            Some(SyntaxKind::UnderscoreToken)
        );
        assert_eq!(reserved_keyword_kind("dynamic"), None);
        assert_eq!(contextual_keyword_kind("dynamic"), None);
    }
}
