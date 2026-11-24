//! Parser behaviour.
//!
//! Two things are checked everywhere: that the tree still prints back as its
//! source, and that the shape is the one C# calls for. The second is written as
//! a compact s-expression of node kinds, because a full dump would bury the
//! point of each test.

use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxTree, parse};
use rustlyn_text::SourceText;

fn tree_of(text: &str) -> SyntaxTree {
    parse(SourceText::new("Test.cs", text))
}

/// The nesting of nodes, with tokens left out.
fn shape_of(node: &SyntaxNode) -> String {
    let children: Vec<String> = node.children().map(|child| shape_of(&child)).collect();
    if children.is_empty() {
        format!("{:?}", node.kind())
    } else {
        format!("({:?} {})", node.kind(), children.join(" "))
    }
}

/// Parses `text` as an expression and returns its shape.
///
/// The expression goes inside a call so that nothing about it is read as a
/// declaration; at statement level `(a)b;` would be ambiguous.
fn expression(text: &str) -> String {
    let source = format!("class C {{ void M() {{ Use({text}); }} }}");
    let tree = tree_of(&source);
    assert!(
        !tree.has_errors(),
        "{text:?} did not parse: {:?}",
        tree.diagnostics()
    );
    let expression = tree
        .root()
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Argument)
        .and_then(|argument| argument.children().next())
        .expect("the argument should hold the expression");
    shape_of(&expression)
}

/// Parses `text` as a statement inside a method body and returns its shape.
fn statement(text: &str) -> String {
    let source = format!("class C {{ void M() {{ {text} }} }}");
    let tree = tree_of(&source);
    assert!(
        !tree.has_errors(),
        "{text:?} did not parse: {:?}",
        tree.diagnostics()
    );
    let statement = tree
        .root()
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Block)
        .and_then(|block| block.children().next())
        .expect("a statement in the body");
    shape_of(&statement)
}

/// Parses `text` at the top of a file and returns the shape of the first
/// statement there.
fn top_level_statement(text: &str) -> String {
    let tree = tree_of(text);
    assert!(
        !tree.has_errors(),
        "{text:?} did not parse: {:?}",
        tree.diagnostics()
    );
    let statement = tree
        .root()
        .child_of_kind(SyntaxKind::GlobalStatement)
        .and_then(|global| global.children().next())
        .expect("a top-level statement");
    shape_of(&statement)
}

/// Parses `text` as a member of a class and returns its shape.
fn member(text: &str) -> String {
    let source = format!("class C {{ {text} }}");
    let tree = tree_of(&source);
    assert!(
        !tree.has_errors(),
        "{text:?} did not parse: {:?}",
        tree.diagnostics()
    );
    let member = tree
        .root()
        .child_of_kind(SyntaxKind::ClassDeclaration)
        .and_then(|class| class.children().next())
        .expect("a member");
    shape_of(&member)
}

const PROGRAM: &str = r#"using System;
using System.Collections.Generic;

namespace Demo;

public interface IShape
{
    double Area { get; }
}

public abstract class Shape : IShape
{
    protected Shape(string name) => Name = name;

    public string Name { get; init; }
    public abstract double Area { get; }
    public static int Count;
}

public sealed class Circle(double radius) : Shape("circle")
{
    private readonly double _radius = radius;

    public override double Area => Math.PI * _radius * _radius;

    public static Circle? TryParse(string text)
    {
        if (double.TryParse(text, out var value) && value > 0)
        {
            return new Circle(value);
        }
        return null;
    }
}

public static class Program
{
    public static void Main(string[] args)
    {
        var shapes = new List<Shape> { new Circle(1.0), new Circle(2.5) };
        double total = 0;
        foreach (var shape in shapes)
        {
            total += shape.Area;
        }

        for (int i = 0; i < shapes.Count; i++)
        {
            Console.WriteLine(shapes[i].Name);
        }

        var label = shapes.Count switch
        {
            0 => "none",
            1 => "one",
            _ when total > 100 => "big",
            _ => "many",
        };

        Func<int, int> square = x => x * x;
        int[] numbers = { 1, 2, 3 };

        try
        {
            Console.WriteLine(label);
        }
        catch (InvalidOperationException e) when (e.Message.Length > 0)
        {
            throw;
        }
        finally
        {
            Console.WriteLine("done");
        }

        object o = shapes;
        if (o is List<Shape> list && list.Count > 0)
        {
            Console.WriteLine(list[0] is Circle ? "circle" : "other");
        }
    }
}
"#;

// -- the invariant ---------------------------------------------------------

#[test]
fn every_tree_reproduces_its_source() {
    for text in [
        "",
        "   \n",
        "// nothing but a comment\n",
        "class C {}",
        PROGRAM,
        // Broken input has to round-trip too, which is the whole point of
        // keeping skipped tokens in the tree.
        "class C { void M( }",
        "int x = ;",
        "class",
        "}}}",
        "class C { int x = 1 }",
        "if (a) { ",
        "M(a, , b);",
        "using ;",
    ] {
        let tree = tree_of(text);
        assert_eq!(tree.text(), text, "round trip failed for {text:?}");
    }
}

#[test]
fn a_realistic_program_parses_without_complaint() {
    let tree = tree_of(PROGRAM);
    assert_eq!(
        tree.diagnostics(),
        &[],
        "unexpected diagnostics:\n{}",
        tree.diagnostics()
            .iter()
            .map(|d| d.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn tokens_tile_the_file_in_order() {
    let tree = tree_of(PROGRAM);
    let mut position = 0;
    for token in tree.root().descendant_tokens() {
        assert_eq!(token.full_span().start(), position);
        position = token.full_span().end();
    }
    assert_eq!(position, tree.source().len());
}

// -- precedence ------------------------------------------------------------

#[test]
fn binary_operators_group_by_precedence() {
    assert_eq!(
        expression("a + b * c"),
        "(AddExpression IdentifierName (MultiplyExpression IdentifierName IdentifierName))"
    );
    assert_eq!(
        expression("a * b + c"),
        "(AddExpression (MultiplyExpression IdentifierName IdentifierName) IdentifierName)"
    );
    assert_eq!(
        expression("a || b && c"),
        "(LogicalOrExpression IdentifierName (LogicalAndExpression IdentifierName IdentifierName))"
    );
    assert_eq!(
        expression("a | b ^ c & d"),
        "(BitwiseOrExpression IdentifierName (ExclusiveOrExpression IdentifierName \
         (BitwiseAndExpression IdentifierName IdentifierName)))"
    );
    assert_eq!(
        expression("a == b + c"),
        "(EqualsExpression IdentifierName (AddExpression IdentifierName IdentifierName))"
    );
}

#[test]
fn same_precedence_groups_to_the_left() {
    assert_eq!(
        expression("a - b - c"),
        "(SubtractExpression (SubtractExpression IdentifierName IdentifierName) IdentifierName)"
    );
}

#[test]
fn assignment_and_coalescing_group_to_the_right() {
    assert_eq!(
        expression("a = b = c"),
        "(SimpleAssignmentExpression IdentifierName \
         (SimpleAssignmentExpression IdentifierName IdentifierName))"
    );
    assert_eq!(
        expression("a ?? b ?? c"),
        "(CoalesceExpression IdentifierName (CoalesceExpression IdentifierName IdentifierName))"
    );
    assert_eq!(
        expression("a ? b : c ? d : e"),
        "(ConditionalExpression IdentifierName IdentifierName \
         (ConditionalExpression IdentifierName IdentifierName IdentifierName))"
    );
}

#[test]
fn assignment_takes_the_whole_right_hand_side() {
    assert_eq!(
        expression("a = b + c"),
        "(SimpleAssignmentExpression IdentifierName (AddExpression IdentifierName IdentifierName))"
    );
    assert_eq!(
        expression("a += b > c"),
        "(AddAssignmentExpression IdentifierName (GreaterThanExpression IdentifierName IdentifierName))"
    );
}

#[test]
fn unary_operators_bind_tighter_than_binary_ones() {
    assert_eq!(
        expression("-a.b"),
        "(UnaryMinusExpression (SimpleMemberAccessExpression IdentifierName IdentifierName))"
    );
    assert_eq!(
        expression("-a * b"),
        "(MultiplyExpression (UnaryMinusExpression IdentifierName) IdentifierName)"
    );
    assert_eq!(
        expression("!a && b"),
        "(LogicalAndExpression (LogicalNotExpression IdentifierName) IdentifierName)"
    );
    assert_eq!(
        expression("a++ + ++b"),
        "(AddExpression (PostIncrementExpression IdentifierName) \
         (PreIncrementExpression IdentifierName))"
    );
}

// -- the ambiguities -------------------------------------------------------

#[test]
fn a_parenthesised_name_is_a_cast_only_when_it_must_be() {
    // `-` and `+` are prefix operators too, so a name in parentheses in front
    // of one is an operand, not a type.
    assert_eq!(
        expression("(a)-b"),
        "(SubtractExpression (ParenthesizedExpression IdentifierName) IdentifierName)"
    );
    assert_eq!(
        expression("(a)+b"),
        "(AddExpression (ParenthesizedExpression IdentifierName) IdentifierName)"
    );
    // A built-in type cannot be a variable, so the same shape is a cast.
    assert_eq!(
        expression("(int)-b"),
        "(CastExpression PredefinedType (UnaryMinusExpression IdentifierName))"
    );
    assert_eq!(
        expression("(int)+b"),
        "(CastExpression PredefinedType (UnaryPlusExpression IdentifierName))"
    );
    // `^` is an index from the end as well as an exclusive or, and reads
    // the same way: `(flags) ^ kind` is the operator.
    assert_eq!(
        expression("(a)^b"),
        "(ExclusiveOrExpression (ParenthesizedExpression IdentifierName) IdentifierName)"
    );
    assert_eq!(
        expression("(int)(a)^b"),
        "(ExclusiveOrExpression (CastExpression PredefinedType (ParenthesizedExpression \
         IdentifierName)) IdentifierName)"
    );
    // Nothing else can follow a parenthesised expression, so these are casts.
    assert_eq!(
        expression("(a)b"),
        "(CastExpression IdentifierName IdentifierName)"
    );
    assert_eq!(
        expression("(a)(b)"),
        "(CastExpression IdentifierName (ParenthesizedExpression IdentifierName))"
    );
    assert_eq!(
        expression("(a)"),
        "(ParenthesizedExpression IdentifierName)"
    );
}

#[test]
fn angle_brackets_are_comparisons_until_proven_generic() {
    assert_eq!(
        expression("a < b > c"),
        "(GreaterThanExpression (LessThanExpression IdentifierName IdentifierName) IdentifierName)"
    );
    assert_eq!(
        expression("a<b>(c)"),
        "(InvocationExpression (GenericName (TypeArgumentList IdentifierName)) \
         (ArgumentList (Argument IdentifierName)))"
    );
    assert_eq!(
        expression("a < b && c > d"),
        "(LogicalAndExpression (LessThanExpression IdentifierName IdentifierName) \
         (GreaterThanExpression IdentifierName IdentifierName))"
    );
}

#[test]
fn nested_generics_split_the_right_shift_back_apart() {
    let text = "List<List<int>> x;";
    let tree = tree_of(text);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert_eq!(tree.text(), text);

    // The `>>` the lexer produced has become two separate tokens.
    let closers: Vec<_> = tree
        .root()
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::GreaterThanToken)
        .map(|token| token.span())
        .collect();
    assert_eq!(closers.len(), 2);
    assert_eq!(closers[0].start(), 13);
    assert_eq!(closers[1].start(), 14);
    assert_eq!(
        statement(text),
        "(LocalDeclarationStatement (VariableDeclaration (GenericName (TypeArgumentList \
         (GenericName (TypeArgumentList PredefinedType)))) VariableDeclarator))"
    );
}

#[test]
fn a_declaration_is_told_from_an_expression_by_what_follows_the_type() {
    assert_eq!(
        statement("a.b c;"),
        "(LocalDeclarationStatement (VariableDeclaration (QualifiedName IdentifierName \
         IdentifierName) VariableDeclarator))"
    );
    assert_eq!(
        statement("a.b(c);"),
        "(ExpressionStatement (InvocationExpression (SimpleMemberAccessExpression IdentifierName \
         IdentifierName) (ArgumentList (Argument IdentifierName))))"
    );
    // `a ? b : c;` is a conditional even though `a?` could have been a type.
    assert_eq!(
        statement("a ? b : c;"),
        "(ExpressionStatement (ConditionalExpression IdentifierName IdentifierName IdentifierName))"
    );
    assert_eq!(
        statement("a? b;"),
        "(LocalDeclarationStatement (VariableDeclaration (NullableType IdentifierName) \
         VariableDeclarator))"
    );
}

#[test]
fn lambdas_are_told_from_parentheses_by_the_arrow() {
    assert_eq!(
        expression("x => x"),
        "(SimpleLambdaExpression Parameter IdentifierName)"
    );
    assert_eq!(
        expression("(x, y) => x"),
        "(ParenthesizedLambdaExpression (ParameterList Parameter Parameter) IdentifierName)"
    );
    assert_eq!(
        expression("(int x) => x"),
        "(ParenthesizedLambdaExpression (ParameterList (Parameter PredefinedType)) IdentifierName)"
    );
    assert_eq!(
        expression("(a, b)"),
        "(TupleExpression (Argument IdentifierName) (Argument IdentifierName))"
    );
    assert_eq!(
        expression("async () => 1"),
        "(ParenthesizedLambdaExpression ParameterList NumericLiteralExpression)"
    );
}

// -- expressions -----------------------------------------------------------

#[test]
fn member_access_and_calls_chain_to_the_left() {
    assert_eq!(
        expression("a.b.c()"),
        "(InvocationExpression (SimpleMemberAccessExpression (SimpleMemberAccessExpression \
         IdentifierName IdentifierName) IdentifierName) ArgumentList)"
    );
    assert_eq!(
        expression("a?.b[0]"),
        "(ConditionalAccessExpression IdentifierName (ElementAccessExpression \
         (MemberBindingExpression IdentifierName) (BracketedArgumentList \
         (Argument NumericLiteralExpression))))"
    );
    assert_eq!(
        expression("a!.b"),
        "(SimpleMemberAccessExpression (SuppressNullableWarningExpression IdentifierName) \
         IdentifierName)"
    );
}

#[test]
fn object_and_collection_creation() {
    assert_eq!(
        expression("new C(1) { X = 2 }"),
        "(ObjectCreationExpression IdentifierName (ArgumentList (Argument NumericLiteralExpression)) \
         (ObjectInitializerExpression (SimpleAssignmentExpression IdentifierName \
         NumericLiteralExpression)))"
    );
    assert_eq!(
        expression("new List<int> { 1, 2 }"),
        "(ObjectCreationExpression (GenericName (TypeArgumentList PredefinedType)) \
         (CollectionInitializerExpression NumericLiteralExpression NumericLiteralExpression))"
    );
    assert_eq!(
        expression("new int[3]"),
        "(ArrayCreationExpression (ArrayType PredefinedType (ArrayRankSpecifier \
         NumericLiteralExpression)))"
    );
    assert_eq!(
        expression("new[] { 1 }"),
        "(ImplicitArrayCreationExpression (ArrayRankSpecifier OmittedArraySizeExpression) \
         (ArrayInitializerExpression NumericLiteralExpression))"
    );
    assert_eq!(
        expression("new { a = 1 }"),
        "(AnonymousObjectCreationExpression (ObjectInitializerExpression \
         (AnonymousObjectMemberDeclarator NameEquals NumericLiteralExpression)))"
    );
}

#[test]
fn ranges_and_indices() {
    assert_eq!(
        expression("a[1..^2]"),
        "(ElementAccessExpression IdentifierName (BracketedArgumentList (Argument \
         (RangeExpression NumericLiteralExpression (IndexExpression NumericLiteralExpression)))))"
    );
    assert_eq!(
        expression("a[..]"),
        "(ElementAccessExpression IdentifierName (BracketedArgumentList (Argument RangeExpression)))"
    );
}

#[test]
fn named_and_reference_arguments() {
    assert_eq!(
        expression("M(name: 1, out var x, ref y)"),
        "(InvocationExpression IdentifierName (ArgumentList (Argument NameColon \
         NumericLiteralExpression) (Argument (DeclarationExpression IdentifierName \
         SingleVariableDesignation)) (Argument IdentifierName)))"
    );
}

// -- patterns --------------------------------------------------------------

#[test]
fn patterns() {
    assert_eq!(
        expression("x is int"),
        "(IsExpression IdentifierName PredefinedType)"
    );
    assert_eq!(
        expression("x is int i"),
        "(IsPatternExpression IdentifierName (DeclarationPattern PredefinedType \
         SingleVariableDesignation))"
    );
    assert_eq!(
        expression("x is not null"),
        "(IsPatternExpression IdentifierName (NotPattern (ConstantPattern NullLiteralExpression)))"
    );
    assert_eq!(
        expression("x is > 0 and < 10"),
        "(IsPatternExpression IdentifierName (AndPattern (RelationalPattern \
         NumericLiteralExpression) (RelationalPattern NumericLiteralExpression)))"
    );
    assert_eq!(
        expression("x is Point { X: 1 }"),
        "(IsPatternExpression IdentifierName (RecursivePattern IdentifierName \
         (PropertyPatternClause (Subpattern NameColon (ConstantPattern \
         NumericLiteralExpression)))))"
    );
    assert_eq!(
        expression("x is (1, 2)"),
        "(IsPatternExpression IdentifierName (RecursivePattern (PositionalPatternClause \
         (Subpattern (ConstantPattern NumericLiteralExpression)) (Subpattern \
         (ConstantPattern NumericLiteralExpression)))))"
    );
    // `x is T ? a : b` is a conditional, not a nullable type test.
    assert_eq!(
        expression("x is T ? a : b"),
        "(ConditionalExpression (IsExpression IdentifierName IdentifierName) IdentifierName \
         IdentifierName)"
    );
}

#[test]
fn switch_expressions_and_statements() {
    assert_eq!(
        expression("x switch { 1 => \"a\", _ => \"b\" }"),
        "(SwitchExpression IdentifierName (SwitchExpressionArm (ConstantPattern \
         NumericLiteralExpression) StringLiteralExpression) (SwitchExpressionArm DiscardPattern \
         StringLiteralExpression))"
    );
    assert_eq!(
        statement("switch (x) { case 1: break; default: break; }"),
        "(SwitchStatement IdentifierName (SwitchSection (CaseSwitchLabel NumericLiteralExpression) \
         BreakStatement) (SwitchSection DefaultSwitchLabel BreakStatement))"
    );
    assert_eq!(
        statement("switch (x) { case int n when n > 0: break; }"),
        "(SwitchStatement IdentifierName (SwitchSection (CasePatternSwitchLabel \
         (DeclarationPattern PredefinedType SingleVariableDesignation) (WhenClause \
         (GreaterThanExpression IdentifierName NumericLiteralExpression))) BreakStatement))"
    );
    // `Set<T> a` would read as `(Set < T) > a` and reach the colon, and is a
    // declaration all the same: no expression is a type and then a name.
    assert_eq!(
        statement("switch (x) { case Set<T> a: break; }"),
        "(SwitchStatement IdentifierName (SwitchSection (CasePatternSwitchLabel \
         (DeclarationPattern (GenericName (TypeArgumentList IdentifierName)) \
         SingleVariableDesignation)) BreakStatement))"
    );
}

// -- statements ------------------------------------------------------------

#[test]
fn control_flow() {
    assert_eq!(
        statement("if (a) b(); else c();"),
        "(IfStatement IdentifierName (ExpressionStatement (InvocationExpression IdentifierName \
         ArgumentList)) (ElseClause (ExpressionStatement (InvocationExpression IdentifierName \
         ArgumentList))))"
    );
    assert_eq!(
        statement("for (int i = 0; i < n; i++) { }"),
        "(ForStatement (VariableDeclaration PredefinedType (VariableDeclarator \
         (EqualsValueClause NumericLiteralExpression))) (LessThanExpression IdentifierName \
         IdentifierName) (PostIncrementExpression IdentifierName) Block)"
    );
    assert_eq!(
        statement("foreach (var x in xs) { }"),
        "(ForEachStatement IdentifierName IdentifierName Block)"
    );
    assert_eq!(
        statement("try { } catch (E e) when (c) { } finally { }"),
        "(TryStatement Block (CatchClause (CatchDeclaration IdentifierName) (CatchFilterClause \
         IdentifierName) Block) (FinallyClause Block))"
    );
    assert_eq!(
        statement("using (var f = Open()) { }"),
        "(UsingStatement (VariableDeclaration IdentifierName (VariableDeclarator \
         (EqualsValueClause (InvocationExpression IdentifierName ArgumentList)))) Block)"
    );
}

#[test]
fn local_functions_are_not_calls() {
    assert_eq!(
        statement("int Add(int a, int b) => a + b;"),
        "(LocalFunctionStatement PredefinedType (ParameterList (Parameter PredefinedType) \
         (Parameter PredefinedType)) (ArrowExpressionClause (AddExpression IdentifierName \
         IdentifierName)))"
    );
}

// -- declarations ----------------------------------------------------------

#[test]
fn members() {
    assert_eq!(
        member("public int X { get; set; } = 1;"),
        "(PropertyDeclaration PredefinedType (AccessorList GetAccessorDeclaration \
         SetAccessorDeclaration) (EqualsValueClause NumericLiteralExpression))"
    );
    assert_eq!(
        member("public int this[int i] => i;"),
        "(IndexerDeclaration PredefinedType (BracketedParameterList (Parameter PredefinedType)) \
         (ArrowExpressionClause IdentifierName))"
    );
    assert_eq!(
        member("private int _a, _b = 2;"),
        "(FieldDeclaration (VariableDeclaration PredefinedType VariableDeclarator \
         (VariableDeclarator (EqualsValueClause NumericLiteralExpression))))"
    );
    assert_eq!(
        member("public C(int x) : base(x) { }"),
        "(ConstructorDeclaration (ParameterList (Parameter PredefinedType)) \
         (BaseConstructorInitializer (ArgumentList (Argument IdentifierName))) Block)"
    );
    assert_eq!(
        member("public static C operator +(C a, C b) => a;"),
        "(OperatorDeclaration IdentifierName (ParameterList (Parameter IdentifierName) \
         (Parameter IdentifierName)) (ArrowExpressionClause IdentifierName))"
    );
    assert_eq!(
        member("public event Action? Changed;"),
        "(EventFieldDeclaration (VariableDeclaration (NullableType IdentifierName) \
         VariableDeclarator))"
    );
    assert_eq!(member("void IFoo.Bar() { }"), {
        "(MethodDeclaration PredefinedType (ExplicitInterfaceSpecifier IdentifierName) \
         ParameterList Block)"
    });
    // An interface re-abstracting another's event writes no accessors, and
    // is no field-like event for all that.
    let source = "interface I2 : I1 { abstract event Action I1.E; }";
    let tree = tree_of(source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert_eq!(tree.text(), source);
    let event = tree
        .root()
        .child_of_kind(SyntaxKind::InterfaceDeclaration)
        .and_then(|interface| interface.child_of_kind(SyntaxKind::EventDeclaration))
        .expect("an event declaration");
    assert_eq!(
        shape_of(&event),
        "(EventDeclaration IdentifierName (ExplicitInterfaceSpecifier IdentifierName))"
    );
}

#[test]
fn generic_methods_with_constraints() {
    assert_eq!(
        member("T Pick<T>(T a) where T : class, new() => a;"),
        "(MethodDeclaration IdentifierName (TypeParameterList TypeParameter) (ParameterList \
         (Parameter IdentifierName)) (TypeParameterConstraintClause ClassConstraint \
         ConstructorConstraint) (ArrowExpressionClause IdentifierName))"
    );
}

#[test]
fn attributes_are_kept_on_the_thing_they_decorate() {
    assert_eq!(
        member("[Obsolete(\"x\"), Serializable] public int F;"),
        "(FieldDeclaration (AttributeList (Attribute IdentifierName (AttributeArgumentList \
         (AttributeArgument StringLiteralExpression))) (Attribute IdentifierName)) \
         (VariableDeclaration PredefinedType VariableDeclarator))"
    );
}

#[test]
fn records_and_namespaces() {
    let tree = tree_of("namespace N { public record Point(int X, int Y) : Base(X); }");
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    let namespace = tree
        .root()
        .child_of_kind(SyntaxKind::NamespaceDeclaration)
        .expect("a namespace");
    assert_eq!(
        shape_of(&namespace),
        "(NamespaceDeclaration IdentifierName (RecordDeclaration (ParameterList \
         (Parameter PredefinedType) (Parameter PredefinedType)) (BaseList \
         (PrimaryConstructorBaseType IdentifierName (ArgumentList (Argument IdentifierName))))))"
    );
}

#[test]
fn top_level_statements_are_not_fields() {
    // At the top of a file this is a local variable; the same text inside a
    // type would be a field.
    assert_eq!(
        top_level_statement("int x = 1;"),
        "(LocalDeclarationStatement (VariableDeclaration PredefinedType (VariableDeclarator \
         (EqualsValueClause NumericLiteralExpression))))"
    );
    assert_eq!(
        member("int x = 1;"),
        "(FieldDeclaration (VariableDeclaration PredefinedType (VariableDeclarator \
         (EqualsValueClause NumericLiteralExpression))))"
    );
}

// -- error recovery --------------------------------------------------------

#[test]
fn a_missing_semicolon_is_reported_once_and_the_tree_survives() {
    let tree = tree_of("class C { void M() { int x = 1 } }");
    let codes: Vec<_> = tree
        .diagnostics()
        .iter()
        .map(|d| d.code().to_string())
        .collect();
    assert_eq!(codes, vec!["CS1002"]);
    assert_eq!(tree.text(), "class C { void M() { int x = 1 } }");

    // The statement is still a statement, with a zero-width semicolon standing
    // in for the one that is not there.
    let declaration = tree
        .root()
        .descendants()
        .find(|node| node.kind() == SyntaxKind::LocalDeclarationStatement)
        .expect("the declaration should still be a declaration");
    let semicolon = declaration
        .child_token_of_kind(SyntaxKind::SemicolonToken)
        .expect("a semicolon, real or invented");
    assert!(semicolon.is_missing());
    assert!(semicolon.span().is_empty());
}

#[test]
fn stray_tokens_are_kept_rather_than_dropped() {
    let text = "class C { @ int x; }";
    let tree = tree_of(text);
    assert_eq!(tree.text(), text);
    assert!(
        tree.root()
            .descendants()
            .any(|node| node.kind() == SyntaxKind::SkippedTokensTrivia),
        "the stray token should be parked in a skipped-tokens node"
    );
    // Parsing carries on: the field after the stray token is still a field.
    assert!(
        tree.root()
            .descendants()
            .any(|node| node.kind() == SyntaxKind::FieldDeclaration)
    );
}

#[test]
fn an_unfinished_file_still_parses() {
    for text in ["class C { void M() {", "if (", "new ", "x."] {
        let tree = tree_of(text);
        assert_eq!(tree.text(), text, "round trip failed for {text:?}");
        assert!(tree.has_errors(), "{text:?} should have been reported");
        // Whatever happened, the root still covers the whole file.
        assert_eq!(tree.root().full_span().end(), tree.source().len());
    }
}

#[test]
fn diagnostics_point_where_the_missing_token_belongs() {
    let source = SourceText::new("Test.cs", "class C\n{\n    int x = 1\n}\n");
    let tree = parse(source.clone());
    let diagnostic = &tree.diagnostics()[0];
    assert_eq!(
        diagnostic.display_with(&source).to_string(),
        "Test.cs(3,14): error CS1002: ; expected"
    );
}

// -- constructs found by parsing Roslyn's own source -----------------------

#[test]
fn an_await_call_is_not_a_local_function() {
    // `await Setup(x);` has the shape of `T M(...);`, with `await` as the
    // return type. Requiring a body is what tells them apart.
    assert_eq!(
        statement("await Setup(x);"),
        "(ExpressionStatement (AwaitExpression (InvocationExpression IdentifierName \
         (ArgumentList (Argument IdentifierName)))))"
    );
    assert_eq!(
        statement("int Add(int a) => a;"),
        "(LocalFunctionStatement PredefinedType (ParameterList (Parameter PredefinedType)) \
         (ArrowExpressionClause IdentifierName))"
    );
}

#[test]
fn a_local_function_may_carry_attributes() {
    assert_eq!(
        statement("[Conditional(\"DEBUG\")] static void Log() { }"),
        "(LocalFunctionStatement (AttributeList (Attribute IdentifierName \
         (AttributeArgumentList (AttributeArgument StringLiteralExpression)))) PredefinedType \
         ParameterList Block)"
    );
}

#[test]
fn an_extension_block_groups_extension_members() {
    let tree = tree_of(
        "static class E { extension(string text) { public bool IsLong => text.Length > 10; } }",
    );
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert!(
        tree.root()
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ExtensionBlockDeclaration)
    );

    // The receiver may be a type with no name of its own.
    for text in [
        "static class E { extension(string) { public static int Zero => 0; } }",
        "static class E { extension<T>(EqualityComparer<T>) { public static int Zero => 0; } }",
    ] {
        let tree = tree_of(text);
        assert!(!tree.has_errors(), "{text:?}: {:?}", tree.diagnostics());
        assert_eq!(tree.text(), text);
    }
}

#[test]
fn a_member_initializer_may_be_a_nested_initializer() {
    assert_eq!(
        expression("new T { State = { Kind = 1 }, Name = \"n\" }"),
        "(ObjectCreationExpression IdentifierName (ObjectInitializerExpression \
         (SimpleAssignmentExpression IdentifierName (ObjectInitializerExpression \
         (SimpleAssignmentExpression IdentifierName NumericLiteralExpression))) \
         (SimpleAssignmentExpression IdentifierName StringLiteralExpression)))"
    );
}

#[test]
fn brackets_in_an_initializer_are_a_key_only_before_an_equals() {
    // `["k"] = v` sets an entry; `[]` on its own is a collection expression
    // standing as an element.
    assert_eq!(
        expression("new T { [\"k\"] = 1 }"),
        "(ObjectCreationExpression IdentifierName (ObjectInitializerExpression \
         (SimpleAssignmentExpression (ImplicitElementAccess (BracketedArgumentList \
         (Argument StringLiteralExpression))) NumericLiteralExpression)))"
    );
    assert_eq!(
        expression("new T { \"name\", [] }"),
        "(ObjectCreationExpression IdentifierName (CollectionInitializerExpression \
         StringLiteralExpression CollectionExpression))"
    );
}

#[test]
fn a_case_constant_may_use_operators_a_pattern_could_not() {
    assert_eq!(
        statement("switch (x) { case Flags.A | Flags.B: break; }"),
        "(SwitchStatement IdentifierName (SwitchSection (CaseSwitchLabel \
         (BitwiseOrExpression (SimpleMemberAccessExpression IdentifierName IdentifierName) \
         (SimpleMemberAccessExpression IdentifierName IdentifierName))) BreakStatement))"
    );
}

#[test]
fn an_explicit_interface_indexer_keeps_its_this() {
    let text = "class C { object IList.this[int index] { get => null; } }";
    let tree = tree_of(text);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert_eq!(tree.text(), text, "the `this` has to stay in the tree");
    assert_eq!(
        member("object IList.this[int index] { get => null; }"),
        "(IndexerDeclaration PredefinedType (ExplicitInterfaceSpecifier IdentifierName) \
         (BracketedParameterList (Parameter PredefinedType)) (AccessorList \
         (GetAccessorDeclaration (ArrowExpressionClause NullLiteralExpression))))"
    );
}

#[test]
fn deconstruction_targets_nest() {
    assert_eq!(
        statement("foreach ((var name, (_, var paths)) in keys) { }"),
        "(ForEachVariableStatement (TupleExpression (Argument (DeclarationExpression \
         IdentifierName SingleVariableDesignation)) (Argument (TupleExpression \
         (Argument IdentifierName) (Argument (DeclarationExpression IdentifierName \
         SingleVariableDesignation))))) IdentifierName Block)"
    );
}

#[test]
fn a_group_that_only_starts_an_assignment_target_is_an_expression() {
    assert_eq!(
        statement("((b) ? ref x : ref y) = 1;"),
        "(ExpressionStatement (SimpleAssignmentExpression (ParenthesizedExpression \
         (ConditionalExpression (ParenthesizedExpression IdentifierName) \
         (RefExpression IdentifierName) (RefExpression IdentifierName))) \
         NumericLiteralExpression))"
    );
}

#[test]
fn a_group_without_a_comma_is_not_a_deconstruction() {
    assert_eq!(
        statement("(var(x, y)) = 42;"),
        "(ExpressionStatement (SimpleAssignmentExpression (ParenthesizedExpression \
         (InvocationExpression IdentifierName (ArgumentList (Argument IdentifierName) \
         (Argument IdentifierName)))) NumericLiteralExpression))"
    );
}

#[test]
fn a_new_expression_may_array_a_tuple_type() {
    assert_eq!(
        expression("new (int, string)[] { }"),
        "(ArrayCreationExpression (ArrayType (TupleType (TupleElement PredefinedType) \
         (TupleElement PredefinedType)) (ArrayRankSpecifier OmittedArraySizeExpression)) \
         ArrayInitializerExpression)"
    );
    // Without the brackets the same shape passes two arguments instead.
    assert_eq!(
        expression("new (a, b)"),
        "(ImplicitObjectCreationExpression (ArgumentList (Argument IdentifierName) \
         (Argument IdentifierName)))"
    );
}

#[test]
fn a_lambda_cannot_swallow_the_arrow_of_a_switch_arm() {
    // `flag => "in"` is a lambda anywhere an assignment could go, and a switch
    // arm's `when` condition is not such a place.
    assert_eq!(
        expression("o switch { Kind.In when flag => \"in\", _ => \"other\" }"),
        "(SwitchExpression IdentifierName (SwitchExpressionArm (TypePattern (QualifiedName \
         IdentifierName IdentifierName)) (WhenClause IdentifierName) StringLiteralExpression) \
         (SwitchExpressionArm DiscardPattern StringLiteralExpression))"
    );
    assert_eq!(
        statement("switch (o) { case Kind.In when flag: break; }"),
        "(SwitchStatement IdentifierName (SwitchSection (CasePatternSwitchLabel (TypePattern \
         (QualifiedName IdentifierName IdentifierName)) (WhenClause IdentifierName)) \
         BreakStatement))"
    );
    // Where a lambda is allowed, it is still a lambda.
    assert_eq!(
        expression("flag => 1"),
        "(SimpleLambdaExpression Parameter NumericLiteralExpression)"
    );
}

// -- gaps found by parsing Roslyn's own source -----------------------------

#[test]
fn a_raw_string_may_quote_raw_strings() {
    // The closing fence of a multi-line raw string has to begin its own line,
    // which is what lets the content hold `"""` of its own.
    let source = "class C { string S = \"\"\"\n    a \"\"\" b\n    \"\"\"; }";
    let tree = tree_of(source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert_eq!(tree.text(), source);
}

#[test]
fn a_hole_of_a_raw_interpolated_string_is_code() {
    // Roslyn keeps the whole literal as one token and re-lexes the holes;
    // streaming them means the nested raw strings are lexed as themselves.
    let source = "class C { string S(string s) => $$\"\"\"\n    {{s.Replace(\"\"\"\n        a\n        \"\"\", \"\"\"\n        b\n        \"\"\")}}\n    \"\"\"; }";
    let tree = tree_of(source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert_eq!(tree.text(), source);
}

#[test]
fn the_dollar_count_decides_what_opens_a_hole() {
    // `$$"""{s}"""` holds the four characters `{s}`; only `{{s}}` interpolates.
    assert_eq!(
        expression("$$\"\"\"{s}\"\"\""),
        "(InterpolatedStringExpression InterpolatedStringText)"
    );
    assert_eq!(
        expression("$$\"\"\"{{s}}\"\"\""),
        "(InterpolatedStringExpression (Interpolation IdentifierName))"
    );
    // Of `{{{` in a one-dollar string, the first two braces are content.
    assert_eq!(
        expression("$\"\"\"{{{s}\"\"\""),
        "(InterpolatedStringExpression InterpolatedStringText (Interpolation IdentifierName))"
    );
}

#[test]
fn function_pointer_types() {
    assert_eq!(
        member("public unsafe delegate*<int, void> F;"),
        "(FieldDeclaration (VariableDeclaration (FunctionPointerType \
         (FunctionPointerParameterList (FunctionPointerParameter PredefinedType) \
         (FunctionPointerParameter PredefinedType))) VariableDeclarator))"
    );
    assert_eq!(
        member("public unsafe delegate* managed<int, int> F;"),
        "(FieldDeclaration (VariableDeclaration (FunctionPointerType \
         FunctionPointerCallingConvention (FunctionPointerParameterList \
         (FunctionPointerParameter PredefinedType) (FunctionPointerParameter PredefinedType))) \
         VariableDeclarator))"
    );
    assert_eq!(
        member("public unsafe delegate* unmanaged[Cdecl, SuppressGCTransition]<int, void> F;"),
        "(FieldDeclaration (VariableDeclaration (FunctionPointerType \
         (FunctionPointerCallingConvention (FunctionPointerUnmanagedCallingConventionList \
         FunctionPointerUnmanagedCallingConvention FunctionPointerUnmanagedCallingConvention)) \
         (FunctionPointerParameterList (FunctionPointerParameter PredefinedType) \
         (FunctionPointerParameter PredefinedType))) VariableDeclarator))"
    );
    // A `delegate` that is not followed by `*` still declares a delegate.
    assert!(member("public delegate void D();").starts_with("(DelegateDeclaration"));
}

#[test]
fn a_function_pointer_type_starts_a_local_declaration() {
    assert_eq!(
        statement("delegate*<void> f = &F;"),
        "(LocalDeclarationStatement (VariableDeclaration (FunctionPointerType \
         (FunctionPointerParameterList (FunctionPointerParameter PredefinedType))) \
         (VariableDeclarator (EqualsValueClause (AddressOfExpression IdentifierName)))))"
    );
}

#[test]
fn allows_ref_struct_constraint() {
    let tree = tree_of("class C<T> where T : struct, allows ref struct { }");
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    let clause = tree
        .root()
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeParameterConstraintClause)
        .expect("a constraint clause");
    assert_eq!(
        shape_of(&clause),
        "(TypeParameterConstraintClause StructConstraint (AllowsConstraintClause \
         RefStructConstraint))"
    );
}

#[test]
fn an_array_initializer_may_initialise_a_property() {
    assert_eq!(
        member("public static int[] P { get; } = { 1, 2 };"),
        "(PropertyDeclaration (ArrayType PredefinedType (ArrayRankSpecifier OmittedArraySizeExpression)) (AccessorList \
         GetAccessorDeclaration) (EqualsValueClause (ArrayInitializerExpression \
         NumericLiteralExpression NumericLiteralExpression)))"
    );
}

#[test]
fn an_operator_after_a_type_continues_a_constant() {
    // In a switch arm the pattern binds loosely, so `E.A | E.B` is one
    // constant rather than a type pattern that stops at `E.A`.
    assert_eq!(
        expression("o switch { (_, E.A | E.B) => 1, _ => 0 }"),
        "(SwitchExpression IdentifierName (SwitchExpressionArm (RecursivePattern \
         (PositionalPatternClause (Subpattern DiscardPattern) (Subpattern (ConstantPattern \
         (BitwiseOrExpression (SimpleMemberAccessExpression IdentifierName IdentifierName) \
         (SimpleMemberAccessExpression IdentifierName IdentifierName)))))) \
         NumericLiteralExpression) (SwitchExpressionArm DiscardPattern NumericLiteralExpression))"
    );
    // `is` binds more tightly, so there the `|` applies to the whole test.
    assert_eq!(
        expression("x is T | y"),
        "(BitwiseOrExpression (IsExpression IdentifierName IdentifierName) IdentifierName)"
    );
}

#[test]
fn a_tuple_type_in_a_pattern_needs_an_array() {
    // `(A a, B b)` deconstructs, but as an array's element type it is a type.
    assert_eq!(
        statement("switch (o) { case (string a, string b): break; }"),
        "(SwitchStatement IdentifierName (SwitchSection (CasePatternSwitchLabel \
         (RecursivePattern (PositionalPatternClause (Subpattern (DeclarationPattern \
         PredefinedType SingleVariableDesignation)) (Subpattern (DeclarationPattern \
         PredefinedType SingleVariableDesignation))))) BreakStatement))"
    );
    assert_eq!(
        statement("switch (o) { case (string a, string b)[] xs: break; }"),
        "(SwitchStatement IdentifierName (SwitchSection (CasePatternSwitchLabel \
         (DeclarationPattern (ArrayType (TupleType (TupleElement PredefinedType) \
         (TupleElement PredefinedType)) (ArrayRankSpecifier OmittedArraySizeExpression)) SingleVariableDesignation)) \
         BreakStatement))"
    );
}

#[test]
fn a_query_keyword_cannot_follow_a_nullable_type() {
    // `as T?` is a nullable type; the `select` after it is not an expression
    // that a conditional could have started.
    let tree = tree_of("class C { void M() { var q = from x in xs let y = x as T? select y; } }");
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    let clause = tree
        .root()
        .descendants()
        .find(|node| node.kind() == SyntaxKind::LetClause)
        .expect("a let clause");
    assert_eq!(
        shape_of(&clause),
        "(LetClause (AsExpression IdentifierName (NullableType IdentifierName)))"
    );
}

#[test]
fn an_extern_local_function_may_end_at_a_semicolon() {
    // Without an attribute or `extern` a bodiless declaration would make every
    // `await Setup(x);` read as a local function.
    assert_eq!(
        statement("[DllImport(\"a\")] static extern bool F(int x);"),
        "(LocalFunctionStatement (AttributeList (Attribute IdentifierName \
         (AttributeArgumentList (AttributeArgument StringLiteralExpression)))) PredefinedType \
         (ParameterList (Parameter PredefinedType)))"
    );
    assert_eq!(
        statement("await Setup(x);"),
        "(ExpressionStatement (AwaitExpression (InvocationExpression IdentifierName \
         (ArgumentList (Argument IdentifierName)))))"
    );
}

#[test]
fn a_tuple_typed_foreach_variable_is_not_a_deconstruction() {
    assert_eq!(
        statement("foreach ((int a, int b) pair in pairs) { }"),
        "(ForEachStatement (TupleType (TupleElement PredefinedType) (TupleElement \
         PredefinedType)) IdentifierName Block)"
    );
    assert_eq!(
        statement("foreach ((int a, int b) in pairs) { }"),
        "(ForEachVariableStatement (TupleExpression (Argument (DeclarationExpression \
         PredefinedType SingleVariableDesignation)) (Argument (DeclarationExpression \
         PredefinedType SingleVariableDesignation))) IdentifierName Block)"
    );
}

#[test]
fn a_parenthesised_expression_may_govern_a_switch() {
    assert_eq!(
        expression("(x) switch { _ => 1 }"),
        "(SwitchExpression (ParenthesizedExpression IdentifierName) (SwitchExpressionArm \
         DiscardPattern NumericLiteralExpression))"
    );
}

#[test]
fn an_async_anonymous_method() {
    assert_eq!(
        expression("async delegate { return 1; }"),
        "(AnonymousMethodExpression (Block (ReturnStatement NumericLiteralExpression)))"
    );
}

#[test]
fn a_lambda_return_type_does_not_swallow_a_conditional() {
    assert_eq!(
        expression("flag ? (a, b) => x : y"),
        "(ConditionalExpression IdentifierName (ParenthesizedLambdaExpression (ParameterList \
         Parameter Parameter) IdentifierName) IdentifierName)"
    );
    assert_eq!(
        expression("void () => M()"),
        "(ParenthesizedLambdaExpression PredefinedType ParameterList (InvocationExpression \
         IdentifierName ArgumentList))"
    );
}

#[test]
fn a_deconstruction_target_may_declare_a_tuple_typed_variable() {
    // `(string, long) y` is a declaration, not a nested target followed by
    // a name.
    assert_eq!(
        statement("(int x, (string, long) y) = M();"),
        "(ExpressionStatement (SimpleAssignmentExpression (TupleExpression (Argument \
         (DeclarationExpression PredefinedType SingleVariableDesignation)) (Argument \
         (DeclarationExpression (TupleType (TupleElement PredefinedType) (TupleElement \
         PredefinedType)) SingleVariableDesignation))) (InvocationExpression IdentifierName \
         ArgumentList)))"
    );
}

#[test]
fn var_in_parentheses_of_its_own_is_a_call() {
    assert_eq!(
        statement("(var(x, y)) = 43;"),
        "(ExpressionStatement (SimpleAssignmentExpression (ParenthesizedExpression \
         (InvocationExpression IdentifierName (ArgumentList (Argument IdentifierName) \
         (Argument IdentifierName)))) NumericLiteralExpression))"
    );
    assert_eq!(
        statement("(var(x, y) = 44);"),
        "(ExpressionStatement (ParenthesizedExpression (SimpleAssignmentExpression \
         (InvocationExpression IdentifierName (ArgumentList (Argument IdentifierName) \
         (Argument IdentifierName))) NumericLiteralExpression)))"
    );
    // At the start of a statement, it declares.
    assert_eq!(
        statement("var (x, y) = p;"),
        "(ExpressionStatement (SimpleAssignmentExpression (DeclarationExpression \
         IdentifierName (ParenthesizedVariableDesignation SingleVariableDesignation \
         SingleVariableDesignation)) IdentifierName))"
    );
}

#[test]
fn a_product_in_a_pattern_is_not_a_pointer_declaration() {
    assert_eq!(
        expression("six is two * three"),
        "(IsPatternExpression IdentifierName (ConstantPattern (MultiplyExpression \
         IdentifierName IdentifierName)))"
    );
}

#[test]
fn break_and_continue_may_name_a_label() {
    assert_eq!(statement("break outer;"), "BreakStatement");
    assert_eq!(statement("continue outer;"), "ContinueStatement");
    let tree = tree_of("class C { void M() { outer: while (true) { break outer; } } }");
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
}

#[test]
fn a_case_label_of_an_array_type_is_a_type_pattern() {
    // `int[]` reads as indexing with nothing, which no constant is; Roslyn
    // takes the type, parenthesized or not.
    assert_eq!(
        statement("switch (o) { case int[]: break; }"),
        "(SwitchStatement IdentifierName (SwitchSection (CasePatternSwitchLabel (TypePattern \
         (ArrayType PredefinedType (ArrayRankSpecifier OmittedArraySizeExpression)))) \
         BreakStatement))"
    );
    assert_eq!(
        statement("switch (o) { case (A[]): break; }"),
        "(SwitchStatement IdentifierName (SwitchSection (CasePatternSwitchLabel \
         (ParenthesizedPattern (TypePattern (ArrayType IdentifierName (ArrayRankSpecifier \
         OmittedArraySizeExpression))))) BreakStatement))"
    );
}

#[test]
fn a_top_level_using_declaration_is_no_directive() {
    // `using var a = ...;` and `using D a = ...;` name a type and then a
    // variable, which no directive does; `using A = B;` and `using N;` stay
    // directives.
    let tree =
        tree_of("using System;\nusing A = B;\nusing var a = new D();\nusing D b = new D();\n");
    let kinds: Vec<SyntaxKind> = tree.root().children().map(|child| child.kind()).collect();
    assert_eq!(
        kinds,
        [
            SyntaxKind::UsingDirective,
            SyntaxKind::UsingDirective,
            SyntaxKind::GlobalStatement,
            SyntaxKind::GlobalStatement,
        ]
    );
}

#[test]
fn an_out_declaration_may_close_an_index_and_a_function_pointer_type_casts_an_address() {
    assert_eq!(
        expression("ia.P[out int x]"),
        "(ElementAccessExpression (SimpleMemberAccessExpression IdentifierName IdentifierName) \
         (BracketedArgumentList (Argument (DeclarationExpression PredefinedType \
         SingleVariableDesignation))))"
    );
    assert_eq!(
        expression("(delegate*<void>)&Write"),
        "(CastExpression (FunctionPointerType (FunctionPointerParameterList \
         (FunctionPointerParameter PredefinedType))) (AddressOfExpression IdentifierName))"
    );
}

#[test]
fn async_before_a_name_and_a_parenthesis_is_a_local_functions_return_type() {
    let tree = tree_of("class C { void M() { async f() => new async(); async Task g() { } } }");
    let functions: Vec<String> = tree
        .root()
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::LocalFunctionStatement)
        .map(|node| {
            node.child_tokens()
                .map(|token| format!("{:?}", token.kind()))
                .collect::<Vec<_>>()
                .join(" ")
        })
        .collect();
    assert_eq!(
        functions,
        [
            "IdentifierToken SemicolonToken",
            "AsyncKeyword IdentifierToken"
        ]
    );
}

#[test]
fn a_directive_name_may_escape_a_formatting_character_that_is_no_part_of_it() {
    let tree = tree_of("#define A\n#if A == A\\uFFFB && A\\u0041 == false\nclass X { }\n#endif\n");
    assert_eq!(
        tree.root()
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ClassDeclaration)
            .count(),
        1
    );
}

/// Attributes in front of a `using` directive, which takes none. They were
/// dropped from the tree, and every position after them moved: the editor
/// cut text in the middle of a character (found by fuzzing, `examples/fuzz.rs`
/// in rustlyn-ide).
#[test]
fn attributes_before_a_using_directive_stay_in_the_tree() {
    for text in [
        "[using",
        "[(]\u{FEFF}using",
        "[b///е.\nusing",
        "[A] using System;",
        "namespace N { [A] using X; }",
    ] {
        let tree = tree_of(text);
        assert_eq!(tree.text(), text, "round trip failed for {text:?}");
        assert!(tree.has_errors(), "{text:?} is not valid C#");
    }
    let tree = tree_of("[A] using System;\nclass C { }");
    let kinds: Vec<SyntaxKind> = tree.root().children().map(|child| child.kind()).collect();
    assert_eq!(
        kinds,
        vec![
            SyntaxKind::IncompleteMember,
            SyntaxKind::UsingDirective,
            SyntaxKind::ClassDeclaration
        ]
    );
}

/// Parentheses nested in a pattern. Each `(` once read what it held three
/// times, and fourteen of them took eleven seconds (found by fuzzing,
/// `examples/fuzz.rs` in rustlyn-ide). Now the contents are read once, and
/// what follows decides what they were.
#[test]
fn nested_parentheses_in_a_pattern_are_read_once() {
    for depth in [1, 2, 16, 40] {
        let text = format!(
            "class C {{ void M(object x) {{ _ = x is {}{} not null; _ = x is {}0{} or (A | B); }} }}",
            "(".repeat(depth),
            ")".repeat(depth),
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let started = std::time::Instant::now();
        let tree = tree_of(&text);
        assert_eq!(tree.text(), text);
        assert!(
            started.elapsed().as_secs() < 2,
            "{depth} parentheses took {:?}",
            started.elapsed()
        );
    }
    // What each shape still is: a pattern in parentheses, a positional
    // pattern of one element, and an expression `|` makes a constant.
    assert!(
        shape_of(&tree_of("class C { bool M(object x) => x is (not null); }").root())
            .contains("ParenthesizedPattern")
    );
    assert!(
        shape_of(&tree_of("class C { bool M(object x) => x is (1) { }; }").root()).contains(
            "(RecursivePattern (PositionalPatternClause (Subpattern (ConstantPattern \
                   NumericLiteralExpression))) PropertyPatternClause)"
        )
    );
    assert!(
        shape_of(&tree_of("class C { bool M(object x) => x is 0 or (A | B); }").root())
            .contains("(ParenthesizedPattern (ConstantPattern (BitwiseOrExpression")
    );
}

/// Parentheses the file never closes. Whether each opened a cast was asked by
/// reading a type out of everything after it, so `n` of them were read `n`
/// times; a pattern, which reads its parentheses again as an expression when
/// they hold no pattern, read them `n²` times: six hundred after `is` took
/// twenty seconds (found by fuzzing, `examples/fuzz.rs` in rustlyn-ide).
#[test]
fn parentheses_the_file_never_closes_are_not_read_again_for_each() {
    // Deep enough to need the stack the editor parses on.
    let parsing = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            for text in [
                format!("class C {{ bool M(object a) => a is {}", "(".repeat(300)),
                format!("class C {{ object M() => {}", "(".repeat(2000)),
            ] {
                let started = std::time::Instant::now();
                let tree = tree_of(&text);
                assert_eq!(tree.text(), text);
                assert!(
                    started.elapsed().as_secs() < 2,
                    "took {:?}",
                    started.elapsed()
                );
            }
        })
        .expect("a thread to parse on");
    parsing.join().expect("the parse");
}

/// Parentheses in a pattern that hold no pattern are read again as an
/// expression, and an `is` inside them starts another pattern each time — two
/// readings per level: `(r is (r is (… MeshRenderer)` twenty-eight deep never
/// finished (found by fuzzing, `examples/fuzz.rs` in rustlyn-ide). The same
/// goes for a pattern the expression reaches another way, as an element of a
/// tuple.
#[test]
fn a_pattern_read_again_as_an_expression_is_not_read_again() {
    let parsing = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            for text in [
                format!(
                    "class C {{ void M(object r) {{ if (r is {}M)\n{{ }} }} }}",
                    "(r is ".repeat(22)
                ),
                format!("class C {{ void M() {{ if ({} x", "is(".repeat(22)),
                format!(
                    "class C {{ bool M(object r) => {} x",
                    "((A, r is ".repeat(22)
                ),
            ] {
                let started = std::time::Instant::now();
                let tree = tree_of(&text);
                assert_eq!(tree.text(), text);
                assert!(
                    started.elapsed().as_secs() < 2,
                    "took {:?}",
                    started.elapsed()
                );
            }
        })
        .expect("a thread to parse on");
    parsing.join().expect("the parse");
}

/// A constructor initializer cut off by the end of the file. The end-of-file
/// token was taken for its `this`, and the trivia in front of it — a comment
/// on the last line — came out twice (found by fuzzing, `examples/fuzz.rs`
/// in rustlyn-ide).
#[test]
fn the_end_of_the_file_is_in_the_tree_once() {
    for text in [
        "class E r(:\n\u{FEFF}",
        "class E { E() :\n// the last line",
        "class E { E() : thos() { } }",
        "class E { E() : base",
    ] {
        let tree = tree_of(text);
        assert_eq!(tree.text(), text, "round trip failed for {text:?}");
        // Stand-ins the parser invents take no text; only the real end of
        // the file carries trivia.
        let ends = tree
            .root()
            .descendant_tokens()
            .filter(|token| {
                token.kind() == SyntaxKind::EndOfFileToken && !token.full_span().is_empty()
            })
            .count();
        assert!(ends <= 1, "{text:?} has the end of the file {ends} times");
    }
}

#[test]
fn a_name_in_parentheses_before_a_bracket_is_indexed_not_cast() {
    // `(m_Data)[idx]` reads an element of what `m_Data` holds: only a type
    // nothing could take for a value casts a collection expression
    // (Roslyn's `ScanCast`).
    assert_eq!(
        expression("(data)[i]"),
        "(ElementAccessExpression (ParenthesizedExpression IdentifierName) \
         (BracketedArgumentList (Argument IdentifierName)))"
    );
    assert_eq!(
        expression("(a.b)[i]"),
        "(ElementAccessExpression (ParenthesizedExpression (SimpleMemberAccessExpression \
         IdentifierName IdentifierName)) (BracketedArgumentList (Argument IdentifierName)))"
    );
    assert!(expression("(List<int>)[1, 2]").starts_with("(CastExpression"));
    assert!(expression("(int[])[1, 2]").starts_with("(CastExpression"));
}

#[test]
fn a_pointer_type_in_parentheses_casts_an_address() {
    // `*(Options*)&raw` reads `raw` as `Options`: a pointer, an array or a
    // nullable could not be a value, so the `&` after it takes an address
    // rather than and-ing with the parenthesized name.
    assert!(expression("(Options*)&raw").starts_with("(CastExpression"));
    assert!(expression("(ulong*)&raw").starts_with("(CastExpression"));
    assert!(expression("(Header**)&blocks[i]").starts_with("(CastExpression"));
    assert!(expression("(int?)-x").starts_with("(CastExpression"));
    assert!(expression("(flags) & kind").starts_with("(BitwiseAndExpression"));
    assert!(expression("(a) - b").starts_with("(SubtractExpression"));
}

#[test]
fn a_dot_at_the_end_of_a_line_before_a_declaration_ends_the_statement() {
    // `EditorGUI.` typed so far, and the declaration on the next line is a
    // statement of its own (Roslyn's `ParseQualifiedNameRight`): the name
    // after the dot is missing, not `var`.
    let source = "class C { void M() {\n    EditorGUI.\n    var name = 1;\n    a.b\n    .c(); } }";
    let text = shape_of(&tree_of(source).root());
    assert!(text.contains("LocalDeclarationStatement"), "{text}");
    assert!(!text.contains("QualifiedName"), "{text}");
    // A chain continued on the next line is still one expression.
    assert!(text.contains("InvocationExpression"), "{text}");
}
