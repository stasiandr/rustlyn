//! The analyzers an `.editorconfig` switches on, and what it says about the
//! ones that are always on.
//!
//! Roslyn's code-style analyzers have a preference to compare the code
//! with, and by default either no preference or a silent one. They say
//! nothing until a repository writes one down:
//!
//! * IDE0007 and IDE0008, `var` or the type written out, by
//!   `csharp_style_var_for_built_in_types`, `..._when_type_is_apparent` and
//!   `..._elsewhere`, each for its own kind of declaration;
//! * IDE0021 to IDE0027 and IDE0061, an expression body or a block, by
//!   `csharp_style_expression_bodied_*` for each kind of member;
//! * IDE0009, `this.` where the options want it, and IDE0003 only where
//!   they do not: `dotnet_style_qualification_for_{field,property,method,event}`;
//! * IDE1006, names that break a naming rule, in [`naming`](super::naming).
//!
//! [`Semantic::configured_diagnostics`] is every analyzer's answer with the
//! file's settings applied: these added, and each diagnostic at the
//! severity the settings give it, or dropped for `none`.

use std::path::Path;

use rustlyn_diagnostics::Severity;
use rustlyn_semantics::{Modifiers, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::{AnalyzerDiagnostic, Resolved, Semantic, View};
use crate::editorconfig::{CodeStyle, Configured, ExpressionBodyPreference, Settings};

impl Semantic {
    /// What the IDE analyzers find in `path` under `settings`: the
    /// analyzers the settings switch on added, every diagnostic at the
    /// severity they give it, those set to `none` left out. Sorted by
    /// place.
    #[must_use]
    pub fn configured_diagnostics(
        &self,
        path: &Path,
        text: Option<&str>,
        settings: &Settings,
    ) -> Option<Vec<AnalyzerDiagnostic>> {
        let mut view = self.view_of(path, text)?;
        Some(view.analyze_configured(settings))
    }
}

impl View<'_> {
    /// [`View::analyze`] under `settings`.
    pub(super) fn analyze_configured(&mut self, settings: &Settings) -> Vec<AnalyzerDiagnostic> {
        let style = settings.code_style();
        let mut found: Vec<AnalyzerDiagnostic> = Vec::new();
        for mut diagnostic in self.analyze() {
            if diagnostic.id == "IDE0003" && self.wants_this(&style, diagnostic.span) {
                continue;
            }
            match settings.severity(diagnostic.id, false) {
                Configured::Suppressed => continue,
                Configured::At(severity) => diagnostic.severity = severity,
                Configured::Default => {}
            }
            found.push(diagnostic);
        }
        let mut configured = Vec::new();
        if style.var != crate::editorconfig::VarPreference::default() {
            self.var_preferences(&style, settings, &mut configured);
        }
        if !style.expression_bodied.is_empty() {
            self.expression_bodies(&style, settings, &mut configured);
        }
        if [
            style.qualify_field,
            style.qualify_property,
            style.qualify_method,
            style.qualify_event,
        ]
        .contains(&Some(true))
        {
            self.missing_this(&style, settings, &mut configured);
        }
        super::naming::violations(self, settings, &mut configured);
        found.extend(configured);
        found.sort_by_key(|diagnostic| (diagnostic.span.start(), diagnostic.span.end()));
        found.dedup_by(|a, b| a.span == b.span && a.id == b.id);
        found
    }

    // MARK: - var

    /// IDE0007 and IDE0008 for every local the preferences have an opinion
    /// about.
    fn var_preferences(
        &mut self,
        style: &CodeStyle,
        settings: &Settings,
        found: &mut Vec<AnalyzerDiagnostic>,
    ) {
        let declarations: Vec<SyntaxNode> = self
            .root
            .descendants()
            .filter(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::VariableDeclaration
                        | SyntaxKind::ForEachStatement
                        | SyntaxKind::DeclarationExpression
                )
            })
            .collect();
        for owner in declarations {
            let Some(ty) = owner.children().find(|child| child.kind().is_type_node()) else {
                continue;
            };
            let (name, initializer) = match owner.kind() {
                SyntaxKind::VariableDeclaration => {
                    let Some(parent) = owner.parent() else {
                        continue;
                    };
                    let local = matches!(
                        parent.kind(),
                        SyntaxKind::LocalDeclarationStatement
                            | SyntaxKind::ForStatement
                            | SyntaxKind::UsingStatement
                    ) && parent
                        .child_token_of_kind(SyntaxKind::ConstKeyword)
                        .is_none();
                    let declarators: Vec<SyntaxNode> = owner
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                        .collect();
                    let [only] = declarators.as_slice() else {
                        continue;
                    };
                    if !local {
                        continue;
                    }
                    (
                        only.child_token_of_kind(SyntaxKind::IdentifierToken),
                        only.child_of_kind(SyntaxKind::EqualsValueClause)
                            .and_then(|clause| clause.children().next()),
                    )
                }
                SyntaxKind::ForEachStatement => {
                    (owner.child_token_of_kind(SyntaxKind::IdentifierToken), None)
                }
                _ => (
                    owner
                        .child_of_kind(SyntaxKind::SingleVariableDesignation)
                        .and_then(|designation| {
                            designation.child_token_of_kind(SyntaxKind::IdentifierToken)
                        }),
                    None,
                ),
            };
            let Some(name) = name else {
                continue;
            };
            let Some(Resolved::Local { ty: local_type, .. }) = self.resolve(&name) else {
                continue;
            };
            if matches!(local_type, Type::Error | Type::Null) {
                continue;
            }
            let written_var = ty.kind() == SyntaxKind::IdentifierName && ty.text().trim() == "var";
            let built_in = is_built_in(self, &local_type);
            let apparent = initializer.as_ref().is_some_and(is_apparent);
            let (preference, option) = if built_in {
                (style.var.built_in, "csharp_style_var_for_built_in_types")
            } else if apparent {
                (style.var.apparent, "csharp_style_var_when_type_is_apparent")
            } else {
                (style.var.elsewhere, "csharp_style_var_elsewhere")
            };
            let Some(prefers_var) = preference else {
                continue;
            };
            if written_var && !prefers_var {
                if self.display_type(&local_type, &ty).is_none() {
                    continue;
                }
                push_configured(
                    found,
                    settings,
                    "IDE0008",
                    option,
                    ty.span(),
                    "Use explicit type instead of 'var'",
                );
            } else if !written_var && prefers_var {
                // Only where `var` would infer this very type.
                let infers = match &initializer {
                    Some(initializer) => {
                        !cannot_infer(initializer)
                            && self.expression_type(initializer).as_ref() == Some(&local_type)
                    }
                    None => owner.kind() == SyntaxKind::DeclarationExpression,
                };
                if infers {
                    push_configured(
                        found,
                        settings,
                        "IDE0007",
                        option,
                        ty.span(),
                        "use 'var' instead of explicit type",
                    );
                }
            }
        }
    }

    // MARK: - expression bodies

    /// IDE0021 to IDE0027 and IDE0061: a body of the other shape than the
    /// preference for its kind of member.
    fn expression_bodies(
        &mut self,
        style: &CodeStyle,
        settings: &Settings,
        found: &mut Vec<AnalyzerDiagnostic>,
    ) {
        for node in self.root.descendants() {
            let Some((id, kind, what)) = body_kind(&node) else {
                continue;
            };
            let Some(preference) = style.expression_body(kind) else {
                continue;
            };
            let option = format!("csharp_style_expression_bodied_{kind}");
            let Some(anchor) = anchor_of(&node) else {
                continue;
            };
            let arrow = node.child_of_kind(SyntaxKind::ArrowExpressionClause);
            match (preference, arrow) {
                (ExpressionBodyPreference::Never, Some(_)) => push_configured(
                    found,
                    settings,
                    id,
                    &option,
                    anchor,
                    format!("Use block body for {what}"),
                ),
                (
                    ExpressionBodyPreference::Always | ExpressionBodyPreference::WhenOnSingleLine,
                    None,
                ) => {
                    let Some(statement) = single_statement(&node) else {
                        continue;
                    };
                    if preference == ExpressionBodyPreference::WhenOnSingleLine
                        && statement.text().to_string().contains('\n')
                    {
                        continue;
                    }
                    push_configured(
                        found,
                        settings,
                        id,
                        &option,
                        anchor,
                        format!("Use expression body for {what}"),
                    );
                }
                _ => {}
            }
        }
    }

    // MARK: - this.

    /// Whether the `this.` at `span` — an IDE0003 — is one the preferences
    /// want kept.
    fn wants_this(&mut self, style: &CodeStyle, span: TextSpan) -> bool {
        let Some(this) = self.root.find_token(span.start()) else {
            return false;
        };
        let Some(access) = this.parent().parent().cloned() else {
            return false;
        };
        let Some(name) = access.children().last().and_then(|name| {
            name.child_tokens()
                .find(|t| t.kind() == SyntaxKind::IdentifierToken)
        }) else {
            return false;
        };
        match self.resolve(&name) {
            Some(Resolved::Symbol(symbol)) => {
                qualification_preference(style, self.compilation().symbols().get(symbol).kind)
                    == Some(true)
            }
            _ => false,
        }
    }

    /// IDE0009: an instance member of the type named without `this.` where
    /// the preferences want it.
    fn missing_this(
        &mut self,
        style: &CodeStyle,
        settings: &Settings,
        found: &mut Vec<AnalyzerDiagnostic>,
    ) {
        let tokens: Vec<SyntaxToken> = self
            .root
            .descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .collect();
        for token in tokens {
            let name = token.parent().clone();
            if name.kind() != SyntaxKind::IdentifierName || !could_take_this(&name) {
                continue;
            }
            let Some(Resolved::Symbol(symbol)) = self.resolve(&token) else {
                continue;
            };
            let symbols = self.compilation().symbols();
            let member = symbols.get(symbol);
            if member.modifiers.contains(Modifiers::STATIC)
                || member.modifiers.contains(Modifiers::CONST)
                || qualification_preference(style, member.kind) != Some(true)
                || member.name.starts_with('.')
            {
                continue;
            }
            let Some(container) = member.container else {
                continue;
            };
            if symbols.get(container).kind != SymbolKind::NamedType {
                continue;
            }
            // Only inside an instance member, where there is a `this`.
            let in_instance = name
                .ancestors()
                .find(|node| is_member(node.kind()))
                .is_some_and(|owner| {
                    !owner
                        .child_tokens()
                        .any(|token| token.kind() == SyntaxKind::StaticKeyword)
                        && !matches!(
                            owner.kind(),
                            SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
                        )
                });
            if !in_instance {
                continue;
            }
            let kind = match member.kind {
                SymbolKind::Field => "field",
                SymbolKind::Property => "property",
                SymbolKind::Method => "method",
                _ => "event",
            };
            let key = format!("dotnet_style_qualification_for_{kind}");
            push_configured(
                found,
                settings,
                "IDE0009",
                &key,
                name.span(),
                "Member access should be qualified.",
            );
        }
    }
}

/// Adds a diagnostic of an analyzer the settings switched on, at the
/// severity they give it: its own `dotnet_diagnostic` entry, the `:severity`
/// after the option, or silent.
fn push_configured(
    found: &mut Vec<AnalyzerDiagnostic>,
    settings: &Settings,
    id: &'static str,
    option: &str,
    span: TextSpan,
    message: impl Into<String>,
) {
    let severity = match settings.severity_with_option(id, option) {
        Configured::Suppressed => return,
        Configured::At(severity) => severity,
        Configured::Default => match settings.severity(id, false) {
            Configured::Suppressed => return,
            Configured::At(severity) => severity,
            Configured::Default => Severity::Hidden,
        },
    };
    found.push(AnalyzerDiagnostic {
        id,
        severity,
        span,
        message: message.into(),
        unnecessary: false,
        deprecated: false,
    });
}

/// Whether `ty` is one of the types C# has a keyword for.
fn is_built_in(view: &View<'_>, ty: &Type) -> bool {
    let Type::Named { symbol, .. } = ty else {
        return false;
    };
    matches!(
        view.compilation()
            .symbols()
            .metadata_qualified_name(*symbol)
            .as_str(),
        "System.Boolean"
            | "System.Byte"
            | "System.SByte"
            | "System.Char"
            | "System.Decimal"
            | "System.Double"
            | "System.Single"
            | "System.Int16"
            | "System.Int32"
            | "System.Int64"
            | "System.UInt16"
            | "System.UInt32"
            | "System.UInt64"
            | "System.IntPtr"
            | "System.UIntPtr"
            | "System.Object"
            | "System.String"
    )
}

/// Whether the type of an initializer is plain from reading it: a `new`, a
/// cast, an `as`, a `default(T)`, as Roslyn's "when type is apparent" has it.
fn is_apparent(initializer: &SyntaxNode) -> bool {
    matches!(
        initializer.kind(),
        SyntaxKind::ObjectCreationExpression
            | SyntaxKind::ArrayCreationExpression
            | SyntaxKind::CastExpression
            | SyntaxKind::AsExpression
            | SyntaxKind::DefaultExpression
    )
}

/// Initializers `var` cannot take its type from.
fn cannot_infer(initializer: &SyntaxNode) -> bool {
    matches!(
        initializer.kind(),
        SyntaxKind::NullLiteralExpression
            | SyntaxKind::DefaultLiteralExpression
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::ArrayInitializerExpression
            | SyntaxKind::CollectionExpression
            | SyntaxKind::ImplicitObjectCreationExpression
            | SyntaxKind::StackAllocArrayCreationExpression
            | SyntaxKind::ImplicitStackAllocArrayCreationExpression
    )
}

/// The diagnostic, option suffix and title noun for a member that can
/// have either kind of body.
fn body_kind(node: &SyntaxNode) -> Option<(&'static str, &'static str, &'static str)> {
    use SyntaxKind as K;
    Some(match node.kind() {
        K::ConstructorDeclaration => ("IDE0021", "constructors", "constructor"),
        K::MethodDeclaration => ("IDE0022", "methods", "method"),
        K::ConversionOperatorDeclaration => {
            ("IDE0023", "conversion_operators", "conversion operator")
        }
        K::OperatorDeclaration => ("IDE0024", "operators", "operator"),
        K::PropertyDeclaration => ("IDE0025", "properties", "property"),
        K::IndexerDeclaration => ("IDE0026", "indexers", "indexer"),
        K::GetAccessorDeclaration
        | K::SetAccessorDeclaration
        | K::InitAccessorDeclaration
        | K::AddAccessorDeclaration
        | K::RemoveAccessorDeclaration => {
            // A lone getter is the property's body, not an accessor's.
            let list = node.parent()?;
            let accessors = list.children().count();
            if accessors == 1 && node.kind() == K::GetAccessorDeclaration {
                return None;
            }
            ("IDE0027", "accessors", "accessor")
        }
        K::LocalFunctionStatement => ("IDE0061", "local_functions", "local function"),
        _ => return None,
    })
}

/// Where the diagnostic of a member goes, and where the light bulb finds
/// its fix: the name, or the keyword that stands for one.
fn anchor_of(node: &SyntaxNode) -> Option<TextSpan> {
    use SyntaxKind as K;
    node.child_tokens()
        .find(|token| {
            matches!(
                token.kind(),
                K::IdentifierToken
                    | K::ThisKeyword
                    | K::OperatorKeyword
                    | K::GetKeyword
                    | K::SetKeyword
                    | K::InitKeyword
                    | K::AddKeyword
                    | K::RemoveKeyword
            )
        })
        .map(|token| token.span())
}

/// The one statement a block-bodied member's body is, when it could be an
/// expression body: a `return` of a value, an expression statement, or a
/// `throw`. For a property or an indexer, the body of its lone getter.
fn single_statement(node: &SyntaxNode) -> Option<SyntaxNode> {
    use SyntaxKind as K;
    let block = match node.kind() {
        K::PropertyDeclaration | K::IndexerDeclaration => {
            let list = node.child_of_kind(K::AccessorList)?;
            let accessors: Vec<SyntaxNode> = list.children().collect();
            let [getter] = accessors.as_slice() else {
                return None;
            };
            if getter.kind() != K::GetAccessorDeclaration {
                return None;
            }
            getter.child_of_kind(K::Block)?
        }
        _ => node.child_of_kind(K::Block)?,
    };
    let statements: Vec<SyntaxNode> = block.children().collect();
    let [statement] = statements.as_slice() else {
        return None;
    };
    let fits = match statement.kind() {
        K::ReturnStatement => statement.children().next().is_some(),
        K::ExpressionStatement | K::ThrowStatement => true,
        _ => false,
    };
    let commented = block.descendant_tokens().any(|token| {
        token
            .leading_trivia()
            .iter()
            .chain(token.trailing_trivia().iter())
            .any(|trivia| {
                matches!(
                    trivia.kind(),
                    K::SingleLineCommentTrivia | K::MultiLineCommentTrivia
                )
            })
    });
    (fits && !commented).then(|| statement.clone())
}

/// The preference for qualifying a member of this kind with `this.`.
fn qualification_preference(style: &CodeStyle, kind: SymbolKind) -> Option<bool> {
    match kind {
        SymbolKind::Field => style.qualify_field,
        SymbolKind::Property => style.qualify_property,
        SymbolKind::Method => style.qualify_method,
        SymbolKind::Event => style.qualify_event,
        _ => None,
    }
}

/// Whether a simple name stands where `this.` could go in front of it: not
/// after a dot, not the name in `nameof`, not a named argument or an object
/// initializer's member, not a declaration.
fn could_take_this(name: &SyntaxNode) -> bool {
    use SyntaxKind as K;
    let Some(parent) = name.parent() else {
        return false;
    };
    match parent.kind() {
        K::SimpleMemberAccessExpression | K::PointerMemberAccessExpression => {
            if parent.children().next().as_ref() != Some(name) {
                return false;
            }
        }
        K::QualifiedName
        | K::AliasQualifiedName
        | K::MemberBindingExpression
        | K::NameColon
        | K::NameEquals
        | K::TypeArgumentList => return false,
        K::SimpleAssignmentExpression => {
            if parent.children().next().as_ref() == Some(name)
                && parent
                    .parent()
                    .is_some_and(|grand| grand.kind() == K::ObjectInitializerExpression)
            {
                return false;
            }
        }
        K::Argument
            if parent
                .parent()
                .and_then(|list| list.parent())
                .is_some_and(|call| call.text().to_string().trim_start().starts_with("nameof")) =>
        {
            return false;
        }
        _ => {}
    }
    // Inside a type, not a body: a field's type, a base list.
    if parent.kind().is_type_node() {
        return false;
    }
    name.ancestors().any(|node| {
        matches!(
            node.kind(),
            K::Block | K::ArrowExpressionClause | K::EqualsValueClause
        )
    })
}

fn is_member(kind: SyntaxKind) -> bool {
    use SyntaxKind as K;
    matches!(
        kind,
        K::MethodDeclaration
            | K::ConstructorDeclaration
            | K::DestructorDeclaration
            | K::PropertyDeclaration
            | K::IndexerDeclaration
            | K::EventDeclaration
            | K::OperatorDeclaration
            | K::ConversionOperatorDeclaration
            | K::FieldDeclaration
            | K::EventFieldDeclaration
    )
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::tests::compile;
    use super::*;

    /// The configured diagnostics of `text` under `config` (an
    /// `.editorconfig` section for `*.cs`), as `ID@text`.
    pub(in super::super) fn configured(text: &str, config: &str) -> Vec<String> {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let settings =
            crate::editorconfig::settings_from_text(&format!("[*.cs]\n{config}"), "C.cs");
        semantic
            .configured_diagnostics(Path::new("/p/C.cs"), None, &settings)
            .expect("analyzed")
            .iter()
            .map(|diagnostic| {
                format!(
                    "{}@{}",
                    diagnostic.id,
                    &text[diagnostic.span.start() as usize..diagnostic.span.end() as usize]
                )
            })
            .collect()
    }

    fn with(text: &str, config: &str, id: &str) -> Vec<String> {
        configured(text, config)
            .into_iter()
            .filter_map(|entry| entry.strip_prefix(&format!("{id}@")).map(str::to_owned))
            .collect()
    }

    const LOCALS: &str = "class Box { }\n\
                          class C {\n\
                            Box Make() => new Box();\n\
                            void M() {\n\
                              int count = 1;\n\
                              var name = \"x\";\n\
                              Box made = new Box();\n\
                              var other = Make();\n\
                              long wide = 1;\n\
                              System.Console.WriteLine(count + name + made + other + wide);\n\
                            }\n\
                          }\n";

    #[test]
    fn var_preferences_are_silent_until_asked_for() {
        assert!(with(LOCALS, "", "IDE0007").is_empty());
        assert!(with(LOCALS, "", "IDE0008").is_empty());
    }

    #[test]
    fn var_is_asked_for_by_kind_of_type() {
        let config = "csharp_style_var_for_built_in_types = true\n\
                      csharp_style_var_when_type_is_apparent = true\n\
                      csharp_style_var_elsewhere = false\n";
        // `long wide = 1` is not what `var` would infer.
        assert_eq!(with(LOCALS, config, "IDE0007"), vec!["int", "Box"]);
        assert_eq!(with(LOCALS, config, "IDE0008"), vec!["var"]);
        let explicit = "csharp_style_var_for_built_in_types = false\n\
                        csharp_style_var_when_type_is_apparent = false\n\
                        csharp_style_var_elsewhere = false\n";
        assert_eq!(with(LOCALS, explicit, "IDE0008"), vec!["var", "var"]);
    }

    #[test]
    fn severities_come_from_the_option_or_the_diagnostic() {
        let semantic = compile(&[("C.cs", LOCALS)], false).expect("compiled");
        let settings = crate::editorconfig::settings_from_text(
            "[*.cs]\ncsharp_style_var_for_built_in_types = true:warning\ncsharp_style_var_when_type_is_apparent = true\ndotnet_diagnostic.IDE0007.severity = suggestion\n",
            "C.cs",
        );
        let found = semantic
            .configured_diagnostics(Path::new("/p/C.cs"), None, &settings)
            .unwrap();
        let severities: Vec<Severity> = found
            .iter()
            .filter(|found| found.id == "IDE0007")
            .map(|found| found.severity)
            .collect();
        assert_eq!(severities, vec![Severity::Info, Severity::Info]);
    }

    #[test]
    fn none_turns_an_analyzer_off() {
        let text = "class C { private int unused; }\n";
        assert_eq!(with(text, "", "IDE0051"), vec!["unused"]);
        assert!(with(text, "dotnet_diagnostic.IDE0051.severity = none", "IDE0051").is_empty());
    }

    #[test]
    fn expression_bodies_follow_the_preference() {
        let text = "class C {\n\
                      int x;\n\
                      int Get() { return x; }\n\
                      int Twice() => x * 2;\n\
                      int P { get { return x; } }\n\
                      void Long() {\n\
                        System.Console.WriteLine(\n\
                          x);\n\
                      }\n\
                    }\n";
        assert_eq!(
            with(
                text,
                "csharp_style_expression_bodied_methods = true",
                "IDE0022"
            ),
            vec!["Get", "Long"]
        );
        assert_eq!(
            with(
                text,
                "csharp_style_expression_bodied_methods = when_on_single_line",
                "IDE0022"
            ),
            vec!["Get"]
        );
        assert_eq!(
            with(
                text,
                "csharp_style_expression_bodied_methods = false",
                "IDE0022"
            ),
            vec!["Twice"]
        );
        assert_eq!(
            with(
                text,
                "csharp_style_expression_bodied_properties = true",
                "IDE0025"
            ),
            vec!["P"]
        );
    }

    #[test]
    fn this_qualification_follows_the_preference() {
        let text = "class C {\n\
                      int x;\n\
                      int P { get; set; }\n\
                      static int s;\n\
                      void M() { x = this.x + P + s; Other(); }\n\
                      void Other() { }\n\
                    }\n";
        assert_eq!(with(text, "", "IDE0003"), vec!["this."]);
        assert!(with(text, "", "IDE0009").is_empty());
        let config = "dotnet_style_qualification_for_field = true\n";
        assert!(with(text, config, "IDE0003").is_empty());
        assert_eq!(with(text, config, "IDE0009"), vec!["x"]);
        let all = "dotnet_style_qualification_for_field = true\n\
                   dotnet_style_qualification_for_property = true\n\
                   dotnet_style_qualification_for_method = true\n";
        assert_eq!(with(text, all, "IDE0009"), vec!["x", "P", "Other"]);
    }
}
