use std::fmt;

/// How loudly a diagnostic complains.
///
/// `Hidden` and `Info` never fail a build; they exist for IDE-only messages
/// such as "unnecessary using directive".
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Severity {
    Hidden,
    Info,
    Warning,
    Error,
}

impl Severity {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Hidden => "hidden",
            Self::Info => "info",
            Self::Warning => "warning",
            Self::Error => "error",
        }
    }
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

macro_rules! error_codes {
    ($( $name:ident = $number:literal, $severity:ident, $template:literal; )*) => {
        /// A C# diagnostic identifier.
        ///
        /// The discriminant is the number printed after `CS`, so the codes match
        /// the ones the Microsoft compiler reports for the same mistake. Names
        /// follow Roslyn's `ErrorCode` enum to keep the mapping obvious.
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        #[repr(u16)]
        #[non_exhaustive]
        pub enum ErrorCode {
            $( $name = $number, )*
        }

        impl ErrorCode {
            /// The numeric part of the identifier, e.g. `1056` for `CS1056`.
            #[must_use]
            pub const fn number(self) -> u16 {
                self as u16
            }

            /// The severity this code carries unless a caller overrides it.
            #[must_use]
            pub const fn default_severity(self) -> Severity {
                match self {
                    $( Self::$name => Severity::$severity, )*
                }
            }

            /// The message text, with `{0}`-style placeholders for arguments.
            #[must_use]
            pub const fn message_template(self) -> &'static str {
                match self {
                    $( Self::$name => $template, )*
                }
            }
        }
    };
}

error_codes! {
    // Literals.
    ErrFloatOverflow = 594, Error, "Floating-point constant is outside the range of type '{0}'";
    ErrIntOverflow = 1021, Error, "Integral constant is too large";
    ErrInvalidNumber = 1013, Error, "Invalid number";
    ErrIllegalEscape = 1009, Error, "Unrecognized escape sequence";
    ErrNewlineInConst = 1010, Error, "Newline in constant";
    ErrEmptyCharConst = 1011, Error, "Empty character literal";
    ErrTooManyCharsInConst = 1012, Error, "Too many characters in character literal";
    ErrUnterminatedStringLit = 1039, Error, "Unterminated string literal";

    // Trivia and stray input.
    ErrOpenEndedComment = 1035, Error, "End-of-file found, '*/' expected";
    ErrUnexpectedCharacter = 1056, Error, "Unexpected character '{0}'";
    ErrExpectedVerbatimLiteral = 1646, Error, "Keyword, identifier, or string expected after verbatim specifier: @";

    // Binding.
    ErrBadBinaryOps = 19, Error, "Operator '{0}' cannot be applied to operands of type '{1}' and '{2}'";
    ErrAmbigBinaryOps = 34, Error, "Operator '{0}' is ambiguous on operands of type '{1}' and '{2}'";
    ErrBadIndexLHS = 21, Error, "Cannot apply indexing with [] to an expression of type '{0}'";
    ErrPtrExpected = 193, Error, "The * or -> operator must be applied to a pointer";
    ErrIllegalStatement = 201, Error, "Only assignment, call, increment, decrement, await, and new object expressions can be used as a statement";
    ErrBadEmbeddedStmt = 1023, Error, "Embedded statement cannot be a declaration or labeled statement";
    WrnPossibleMistakenNullStatement = 642, Warning, "Possible mistaken empty statement";
    ErrBadAttributeArgument = 182, Error, "An attribute argument must be a constant expression, typeof expression or array creation expression of an attribute parameter type";
    ErrMissingDeconstruct = 8129, Error, "No suitable 'Deconstruct' instance or extension method was found for type '{0}', with {1} out parameters and a void return type.";
    ErrTypeInferenceFailedForImplicitlyTypedDeconstructionVariable = 8130, Error, "Cannot infer the type of implicitly-typed deconstruction variable '{0}'.";
    ErrUnsafeNeeded = 214, Error, "Pointers and fixed size buffers may only be used in an unsafe context";
    ErrNoConvToIDisp = 1674, Error, "'{0}': type used in a using statement must implement 'System.IDisposable'.";
    ErrNoConvToIAsyncDisp = 8410, Error, "'{0}': type used in an asynchronous using statement must implement 'System.IAsyncDisposable' or implement a suitable 'DisposeAsync' method.";
    ErrSpecialTypeAsBound = 702, Error, "Constraint cannot be special class '{0}'";
    ErrDefaultValueMustBeConstant = 1736, Error, "Default parameter value for '{0}' must be a compile-time constant";
    ErrBadMemberFlag = 106, Error, "The modifier '{0}' is not valid for this item";
    ErrStaticNotVirtual = 112, Error, "A static member cannot be marked as '{0}'";
    ErrPartialMisplaced = 267, Error, "The 'partial' modifier can only appear immediately before 'class', 'record', 'struct', 'interface', 'event', an instance constructor name, or a method or property return type.";
    ErrDuplicateModifier = 1004, Error, "Duplicate '{0}' modifier";
    ErrPropertyLacksGet = 154, Error, "The property or indexer '{0}' cannot be used in this context because it lacks the get accessor";
    ErrCannotInferDelegateType = 8917, Error, "The delegate type could not be inferred.";
    ErrMethodNameExpected = 149, Error, "Method name expected";
    ErrUnsafeOperation = 9360, Error, "This operation may only be used in an unsafe context";
    ErrBadUnaryOp = 23, Error, "Operator '{0}' cannot be applied to operand of type '{1}'";
    ErrCannotBeMadeNullable = 8978, Error, "'{0}' cannot be made nullable.";
    ErrNoImplicitConv = 29, Error, "Cannot implicitly convert type '{0}' to '{1}'";
    ErrNoExplicitConv = 30, Error, "Cannot convert type '{0}' to '{1}'";
    ErrLocalDuplicate = 128, Error, "A local variable or function named '{0}' is already defined in this scope";
    ErrAmbigCall = 121, Error, "The call is ambiguous between the following methods or properties: '{0}' and '{1}'";
    ErrBadArgCount = 1501, Error, "No overload for method '{0}' takes {1} arguments";
    ErrBadArgType = 1503, Error, "Argument {0}: cannot convert from '{1}' to '{2}'";
    ErrNoSuchMemberOrExtension = 1061, Error, "'{0}' does not contain a definition for '{1}' and no accessible extension method '{1}' accepting a first argument of type '{0}' could be found (are you missing a using directive or an assembly reference?)";
    ErrBadExtensionReceiver = 1929, Error, "'{0}' does not contain a definition for '{1}' and the best extension method overload '{2}' requires a receiver of type '{3}'";
    ErrBadCtorArgCount = 1729, Error, "'{0}' does not contain a constructor that takes {1} arguments";
    ErrNoCorrespondingArgument = 7036, Error, "There is no argument given that corresponds to the required parameter '{0}' of '{1}'";
    ErrNoImplicitConvCast = 266, Error, "Cannot implicitly convert type '{0}' to '{1}'. An explicit conversion exists (are you missing a cast?)";
    ErrCheckedOverflow = 220, Error, "The operation overflows at compile time in checked mode";
    ErrIntDivByZero = 20, Error, "Division by constant zero";
    ErrDecimalConstantFailed = 463, Error, "Evaluation of the decimal constant expression failed";
    ErrNotConstantExpression = 133, Error, "The expression being assigned to '{0}' must be constant";
    ErrLiteralDoubleCast = 664, Error, "Literal of type double cannot be implicitly converted to type '{1}'; use an '{0}' suffix to create a literal of this type";
    ErrCircConstValue = 110, Error, "The evaluation of the constant value for '{0}' involves a circular definition";
    ErrConstOutOfRangeChecked = 221, Error, "Constant value '{0}' cannot be converted to a '{1}' (use 'unchecked' syntax to override)";
    ErrEnumeratorOverflow = 543, Error, "'{0}': the enumerator value is too large to fit in its type";
    ErrConstOutOfRange = 31, Error, "Constant value '{0}' cannot be converted to a '{1}'";
    ErrObjectRequired = 120, Error, "An object reference is required for the non-static field, method, or property '{0}'";
    ErrObjectProhibited = 176, Error, "Member '{0}' cannot be accessed with an instance reference; qualify it with a type name instead";
    ErrNoNewAbstract = 144, Error, "Cannot create an instance of the abstract type or interface '{0}'";
    ErrValueTypeExtDelegate = 1113, Error, "Extension method '{0}' defined on value type '{1}' cannot be used to create delegates";
    ErrAssgReadonlyProp = 200, Error, "Property or indexer '{0}' cannot be assigned to -- it is read only";
    ErrAssgReadonly = 191, Error, "A readonly field cannot be assigned to (except in a constructor or init-only setter of the type in which the field is defined or a variable initializer)";
    ErrAssgReadonlyStatic = 198, Error, "A static readonly field cannot be assigned to (except in a static constructor or a variable initializer)";
    ErrAssgLvalueExpected = 131, Error, "The left-hand side of an assignment must be a variable, property or indexer";
    ErrImplicitlyTypedVariableAssignedBadValue = 815, Error, "Cannot assign {0} to an implicitly-typed variable";
    ErrImplicitlyTypedVariableUsedInForbiddenZone = 8196, Error, "Reference to an implicitly-typed variable '{0}' is not permitted in this location.";
    ErrImplicitlyTypedVariableWithNoInitializer = 818, Error, "Implicitly-typed variables must be initialized";
    ErrBadAwaitWithoutAsyncMethod = 4032, Error, "The 'await' operator can only be used within an async method. Consider marking this method with the 'async' modifier and changing its return type to 'Task<{0}>'.";
    ErrBadAwaitWithoutVoidAsyncMethod = 4033, Error, "The 'await' operator can only be used within an async method. Consider marking this method with the 'async' modifier and changing its return type to 'Task'.";
    ErrBadAwaitWithoutAsyncLambda = 4034, Error, "The 'await' operator can only be used within an async lambda expression. Consider marking this lambda expression with the 'async' modifier.";
    ErrCantInferMethTypeArgs = 411, Error, "The type arguments for method '{0}' cannot be inferred from the usage. Try specifying the type arguments explicitly.";
    ErrLocalIllegallyOverrides = 136, Error, "A local or parameter named '{0}' cannot be declared in this scope because that name is used in an enclosing local scope to define a local or parameter";
    ErrRetNoObjectRequired = 127, Error, "Since '{0}' returns void, a return keyword must not be followed by an object expression";
    ErrRetObjectRequired = 126, Error, "An object of a type convertible to '{0}' is required";
    ErrConcreteMissingBody = 501, Error, "'{0}' must declare a body because it is not marked abstract, extern, or partial";
    ErrAbstractHasBody = 500, Error, "'{0}' cannot declare a body because it is marked abstract";
    ErrReturnExpected = 161, Error, "'{0}': not all code paths return a value";
    ErrAnonymousReturnExpected = 1643, Error, "Not all code paths return a value in lambda expression of type '{0}'";
    ErrBadParamRef = 1676, Error, "Parameter {0} must be declared with the '{1}' keyword";
    ErrBadParamExtraRef = 1677, Error, "Parameter {0} should not be declared with the '{1}' keyword";
    WrnUnreachableCode = 162, Warning, "Unreachable code detected";
    WrnUnreferencedLabel = 164, Warning, "This label has not been referenced";
    ErrBadFinallyLeave = 157, Error, "Control cannot leave the body of a finally clause";
    ErrNoBreakOrCont = 139, Error, "No enclosing loop out of which to break or continue";
    ErrNoBreakId = 9393, Error, "No enclosing loop or switch statement with the label '{0}' out of which to break";
    ErrNoContinueId = 9394, Error, "No enclosing loop with the label '{0}' out of which to continue";
    WrnUnreferencedVar = 168, Warning, "The variable '{0}' is declared but never used";
    WrnUnreferencedVarAssg = 219, Warning, "The variable '{0}' is assigned but its value is never used";
    ErrBadAccess = 122, Error, "'{0}' is inaccessible due to its protection level";
    ErrVariableUsedBeforeDeclaration = 841, Error, "Cannot use local variable '{0}' before it is declared";
    ErrUseDefViolation = 165, Error, "Use of unassigned local variable '{0}'";
    ErrUseDefViolationOut = 269, Error, "Use of unassigned out parameter '{0}'";
    ErrParamUnassigned = 177, Error, "The out parameter '{0}' must be assigned to before control leaves the current method";

    // Declarations.
    ErrDuplicateNameInNS = 101, Error, "The namespace '{0}' already contains a definition for '{1}'";
    ErrDuplicateNameInClass = 102, Error, "The type '{0}' already contains a definition for '{1}'";
    ErrMissingPartial = 260, Error, "Missing partial modifier on declaration of type '{0}'; another partial declaration of this type exists";
    ErrSingleTypeNameNotFound = 246, Error, "The type or namespace name '{0}' could not be found (are you missing a using directive or an assembly reference?)";
    ErrNameNotInContext = 103, Error, "The name '{0}' does not exist in the current context";
    ErrNoSuchMember = 117, Error, "'{0}' does not contain a definition for '{1}'";
    ErrAmbiguousReference = 104, Error, "'{0}' is an ambiguous reference between '{1}' and '{2}'";
    ErrSameFullNameAggAgg = 433, Error, "The type '{1}' exists in both '{0}' and '{2}'";
    ErrDottedTypeNameNotFoundInNS = 234, Error, "The type or namespace name '{0}' does not exist in the namespace '{1}' (are you missing an assembly reference?)";
    ErrGlobalSingleTypeNameNotFound = 400, Error, "The type or namespace name '{0}' could not be found in the global namespace (are you missing an assembly reference?)";
    ErrDottedTypeNameNotFoundInAgg = 426, Error, "The type name '{0}' does not exist in the type '{1}'";
    ErrBadArity = 305, Error, "Using the generic {1} '{0}' requires {2} type arguments";
    ErrUnimplementedInterfaceMember = 535, Error, "'{0}' does not implement interface member '{1}'";
    ErrUnimplementedAbstractMethod = 534, Error, "'{0}' does not implement inherited abstract member '{1}'";
    ErrCloseUnimplementedInterfaceMemberWrongReturnType = 738, Error, "'{0}' does not implement interface member '{1}'. '{2}' cannot implement '{1}' because it does not have the matching return type of '{3}'.";
    ErrOverrideNotExpected = 115, Error, "'{0}': no suitable method found to override";
    ErrCantOverrideNonVirtual = 506, Error, "'{0}': cannot override inherited member '{1}' because it is not marked virtual, abstract, or override";
    ErrCantOverrideSealed = 239, Error, "'{0}': cannot override inherited member '{1}' because it is sealed";
    WrnNewRequired = 108, Warning, "'{0}' hides inherited member '{1}'. Use the new keyword if hiding was intended.";
    WrnDuplicateUsing = 105, Warning, "The using directive for '{0}' appeared previously in this namespace";
    WrnTypeParameterSameAsOuterTypeParameter = 693, Warning, "Type parameter '{0}' has the same name as the type parameter from outer type '{1}'";
    WrnUnreferencedEvent = 67, Warning, "The event '{0}' is never used";
    WrnUnreferencedFieldAssg = 414, Warning, "The field '{0}' is assigned but its value is never used";
    WrnAsyncLacksAwaits = 1998, Warning, "This async method lacks 'await' operators and will run synchronously. Consider using the 'await' operator to await non-blocking API calls, or 'await Task.Run(...)' to do CPU-bound work on a background thread.";
    ErrBadAwaitArgVoidCall = 4008, Error, "Cannot await 'void'";
    WrnMissingNonNullTypesContextForAnnotation = 8632, Warning, "The annotation for nullable reference types should only be used in code within a '#nullable' annotations context.";
    WrnUnobservedAwaitableExpression = 4014, Warning, "Because this call is not awaited, execution of the current method continues before the call is completed. Consider applying the 'await' operator to the result of the call.";
    WrnSwitchExpressionNotExhaustive = 8509, Warning, "The switch expression does not handle all possible values of its input type (it is not exhaustive). For example, the pattern '{0}' is not covered.";
    WrnSwitchExpressionNotExhaustiveWithUnnamedEnumValue = 8524, Warning, "The switch expression does not handle some values of its input type (it is not exhaustive) involving an unnamed enum value. For example, the pattern '{0}' is not covered.";
    WrnNewOrOverrideExpected = 114, Warning, "'{0}' hides inherited member '{1}'. To make the current member override that implementation, add the override keyword. Otherwise add the new keyword.";
    ErrMemberAlreadyExists = 111, Error, "Type '{1}' already defines a member called '{0}' with the same parameter types";
    ErrAbstractInConcreteClass = 513, Error, "'{0}' is abstract but it is contained in non-abstract type '{1}'";
    WrnDeprecatedSymbol = 612, Warning, "'{0}' is obsolete";
    WrnAttributeLocationOnBadDeclaration = 657, Warning, "'{0}' is not a valid attribute location for this declaration. Valid attribute locations for this declaration are '{1}'. All attributes in this block will be ignored.";
    WrnInvalidAttributeLocation = 658, Warning, "'{0}' is not a recognized attribute location. Valid attribute locations for this declaration are '{1}'. All attributes in this block will be ignored.";
    WrnDeprecatedSymbolStr = 618, Warning, "'{0}' is obsolete: '{1}'";
    WrnEqualsWithoutGetHashCode = 659, Warning, "'{0}' overrides Object.Equals(object o) but does not override Object.GetHashCode()";
    WrnEqualityOpWithoutEquals = 660, Warning, "'{0}' defines operator == or operator != but does not override Object.Equals(object o)";
    WrnEqualityOpWithoutGetHashCode = 661, Warning, "'{0}' defines operator == or operator != but does not override Object.GetHashCode()";
    WrnObsoleteOverridingNonObsolete = 809, Warning, "Obsolete member '{0}' overrides non-obsolete member '{1}'";
    ErrDeprecatedSymbolStr = 619, Error, "'{0}' is obsolete: '{1}'";

    // Preprocessor.
    ErrPpDirectiveExpected = 1024, Error, "Preprocessor directive expected";
    ErrEndOfPpLineExpected = 1025, Error, "Single-line comment or end-of-line expected";
    ErrEndifDirectiveExpected = 1027, Error, "#endif directive expected";
    ErrUnexpectedDirective = 1028, Error, "Unexpected preprocessor directive";
    ErrErrorDirective = 1029, Error, "#error: '{0}'";
    WrnWarningDirective = 1030, Warning, "#warning: '{0}'";
    ErrInvalidPreprocExpr = 1517, Error, "Invalid preprocessor expression";

    // Parser.
    ErrIdentifierExpected = 1001, Error, "Identifier expected";
    ErrSemicolonExpected = 1002, Error, "; expected";
    ErrSyntaxError = 1003, Error, "Syntax error, '{0}' expected";
    ErrEofExpected = 1022, Error, "Type or namespace definition, or end-of-file expected";
    ErrCloseParenExpected = 1026, Error, ") expected";
    ErrTypeExpected = 1031, Error, "Type expected";
    ErrIdentifierExpectedKW = 1041, Error, "Identifier expected; '{0}' is a keyword";
    ErrRbraceExpected = 1513, Error, "} expected";
    ErrLbraceExpected = 1514, Error, "{ expected";
    ErrInvalidMemberDecl = 1519, Error, "Invalid token '{0}' in class, record, struct, or interface member declaration";
    ErrInvalidExprTerm = 1525, Error, "Invalid expression term '{0}'";
    ErrExpressionExpected = 1733, Error, "Expected expression";
    ErrInsufficientStack = 8078, Error, "An expression is too long or complex to compile";
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CS{:04}", self.number())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifiers_are_padded() {
        assert_eq!(ErrorCode::ErrFloatOverflow.to_string(), "CS0594");
        assert_eq!(ErrorCode::ErrUnexpectedCharacter.to_string(), "CS1056");
        assert_eq!(ErrorCode::ErrUnexpectedCharacter.number(), 1056);
    }
}
