//! Quick info: what the editor shows when the mouse rests on a name.
//!
//! Roslyn's QuickInfo, as one answer with its sections: the symbol written
//! out the way Roslyn writes it — `(local variable) int count`,
//! `(property) int List<T>.Count { get; }`, `(constant) int C.Max = 10`,
//! `(awaitable) Task<int> C.LoadAsync()`, `class System.String` — then what
//! its documentation comment says, what the type parameters stand for at
//! this use (`T is int`), and for a lambda or a local function the
//! variables it captures.
//!
//! Keywords that stand for something say what: `var` is the type it
//! inferred, `int` is `System.Int32`, `this` is the type the code is in,
//! `nameof(x)` is the string it makes, and an operator is the user-defined
//! operator it calls. A literal, or a keyword that stands for nothing, has
//! no quick info.

use std::path::Path;

use rustlyn_semantics::{
    BoundExpressionKind, BoundSymbol, ConstantValue, MethodKind, RefKind, SymbolId, SymbolKind,
    Type, TypeKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::assist::{element, parse_documentation, plain};
use super::walk::find_expression;
use super::{Resolved, Semantic, View, describe_symbol};

/// What the mouse is on, in sections.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct QuickInfo {
    /// What the quick info is about, in bytes of the text asked about.
    pub span: TextSpan,
    /// The symbol, written out: `(parameter) string name`.
    pub description: String,
    /// The `<summary>`.
    pub summary: String,
    /// Each `<param>`, by name.
    pub parameters: Vec<(String, String)>,
    /// The `<returns>`.
    pub returns: String,
    /// The `<value>` of a property.
    pub value: String,
    /// The `<remarks>`.
    pub remarks: String,
    /// The types each `<exception>` names.
    pub exceptions: Vec<String>,
    /// What the type parameters stand for here: `T is int`.
    pub type_parameters: Vec<String>,
    /// For a lambda or a local function: the variables of the code around
    /// it that it reads, and `this` when it reads that.
    pub captures: Vec<String>,
    /// The value, where it is known at compile time: a constant, an enum
    /// member, what `nameof` makes. As C# would write it: `10`, `"count"`.
    pub constant: Option<String>,
}

impl Semantic {
    /// The quick info for `offset` of `path` as the editor has it.
    #[must_use]
    pub fn quick_info(&self, path: &Path, offset: u32, text: Option<&str>) -> Option<QuickInfo> {
        let mut view = self.view_of(path, text)?;
        view.quick_info(offset)
    }

    /// The documentation of a symbol, parsed: its own `///` comment or its
    /// assembly's XML file. A parameter's and a type parameter's come from
    /// what they belong to.
    fn documentation_xml(&self, symbol: SymbolId) -> Option<String> {
        if self.compilation.is_from_metadata(symbol) {
            self.metadata_documentation(symbol)
        } else {
            self.source_documentation(symbol)
        }
    }
}

impl View<'_> {
    /// The quick info for `offset` of the file this view is of.
    pub fn quick_info(&mut self, offset: u32) -> Option<QuickInfo> {
        let token = self.token_for_quick_info(offset)?;
        let span = token.span();
        // `this[...]`, `operator +` and `implicit operator int` declare an
        // indexer or an operator with a token that is not a name.
        if matches!(
            token.parent().kind(),
            SyntaxKind::IndexerDeclaration
                | SyntaxKind::OperatorDeclaration
                | SyntaxKind::ConversionOperatorDeclaration
        ) && token.kind() != SyntaxKind::IdentifierToken
            && let Some(symbol) = self.model.declared_symbol(token.parent())
        {
            let mut info = self.symbol_info(symbol, None);
            info.span = span;
            return Some(info);
        }
        let mut info = match token.kind() {
            SyntaxKind::IdentifierToken if token.value_text() == "var" && self.is_var(&token) => {
                self.var_info(&token)?
            }
            SyntaxKind::IdentifierToken if token.value_text() == "nameof" => self
                .nameof_info(&token)
                .or_else(|| self.name_info(&token))?,
            SyntaxKind::IdentifierToken | SyntaxKind::ThisKeyword | SyntaxKind::BaseKeyword => {
                self.name_info(&token)?
            }
            _ if token.parent().kind() == SyntaxKind::PredefinedType => self.name_info(&token)?,
            SyntaxKind::NewKeyword
                if token.parent().kind() == SyntaxKind::ImplicitObjectCreationExpression =>
            {
                self.implicit_new_info(&token)?
            }
            SyntaxKind::EqualsGreaterThanToken | SyntaxKind::DelegateKeyword => {
                self.lambda_info(&token)?
            }
            kind if is_operator_token(kind) => self.operator_info(&token)?,
            _ => return None,
        };
        info.span = span;
        Some(info)
    }

    /// The token under the cursor, or the one that ends at it.
    fn token_for_quick_info(&self, offset: u32) -> Option<SyntaxToken> {
        let wanted = |token: &SyntaxToken| !token.span().is_empty();
        let at = self
            .root
            .find_token(offset)
            .filter(|token| token.span().contains(offset) && wanted(token));
        at.or_else(|| {
            let before = self.root.find_token(offset.checked_sub(1)?)?;
            (before.span().end() == offset && wanted(&before)).then_some(before)
        })
    }

    /// Whether a `var` token is the keyword rather than a name.
    fn is_var(&self, token: &SyntaxToken) -> bool {
        let parent = token.parent();
        parent.kind() == SyntaxKind::IdentifierName
            && parent.parent().is_some_and(|grand| {
                matches!(
                    grand.kind(),
                    SyntaxKind::VariableDeclaration
                        | SyntaxKind::ForEachStatement
                        | SyntaxKind::ForEachVariableStatement
                        | SyntaxKind::DeclarationExpression
                        | SyntaxKind::DeclarationPattern
                )
            })
    }

    // MARK: - names

    fn name_info(&mut self, token: &SyntaxToken) -> Option<QuickInfo> {
        let resolved = self.resolve_definition(token)?;
        match resolved {
            Resolved::Local { span, name, ty, .. } => Some(self.local_info(span, &name, &ty)),
            Resolved::Symbol(symbol) => Some(self.symbol_info(symbol, Some(token))),
        }
    }

    /// A local, a lambda's parameter, or a local constant.
    fn local_info(&mut self, declared: TextSpan, name: &str, ty: &Type) -> QuickInfo {
        let symbols = self.compilation().symbols();
        let shown = ty.display(symbols);
        let declaration = self
            .root
            .find_token(declared.start())
            .filter(|token| token.span() == declared)
            .map(|token| token.parent().clone());
        let mut info = QuickInfo::default();
        match declaration {
            Some(node) if node.kind() == SyntaxKind::Parameter => {
                info.description = format!("(parameter) {shown} {name}");
            }
            Some(node)
                if node.kind() == SyntaxKind::VariableDeclarator
                    && node.ancestors().nth(1).is_some_and(|statement| {
                        statement
                            .child_token_of_kind(SyntaxKind::ConstKeyword)
                            .is_some()
                    }) =>
            {
                let value = initializer_text(&node);
                info.description = match &value {
                    Some(value) => format!("(local constant) {shown} {name} = {value}"),
                    None => format!("(local constant) {shown} {name}"),
                };
                info.constant = value;
            }
            _ => info.description = format!("(local variable) {shown} {name}"),
        }
        info
    }

    /// Anything with a symbol: a type, a member, a parameter, a namespace.
    fn symbol_info(&mut self, symbol: SymbolId, token: Option<&SyntaxToken>) -> QuickInfo {
        let symbols = self.compilation().symbols();
        let found = symbols.get(symbol);
        let mut info = QuickInfo {
            description: self.describe_for_quick_info(symbol, token),
            ..QuickInfo::default()
        };
        // The documentation: a parameter's and a type parameter's are in the
        // comment of what they belong to.
        let (owner, own_tag) = match found.kind {
            SymbolKind::Parameter => (found.container, Some("param")),
            SymbolKind::TypeParameter => (found.container, Some("typeparam")),
            _ => (Some(symbol), None),
        };
        if let Some(owner) = owner
            && let Some(xml) = self.semantic.documentation_xml(owner)
        {
            match own_tag {
                Some(tag) => info.summary = tagged(&xml, tag, &found.name).unwrap_or_default(),
                None => {
                    let parsed = parse_documentation(&xml);
                    info.summary = parsed.summary;
                    info.parameters = parsed.parameters;
                    info.returns = parsed.returns;
                    info.value = element(&xml, "value").map(plain).unwrap_or_default();
                    info.remarks = element(&xml, "remarks").map(plain).unwrap_or_default();
                    info.exceptions = exceptions(&xml);
                }
            }
        }
        info.constant = self.constant_of(symbol);
        if let Some(token) = token {
            info.type_parameters = self.type_parameter_map(symbol, token);
            if found
                .as_method()
                .is_some_and(|method| method.method_kind == MethodKind::LocalFunction)
            {
                info.captures = self.local_function_captures(symbol, token);
            }
        }
        info
    }

    /// Roslyn's main description line for a symbol.
    fn describe_for_quick_info(&mut self, symbol: SymbolId, token: Option<&SyntaxToken>) -> String {
        let compilation = self.compilation();
        let symbols = compilation.symbols();
        let found = symbols.get(symbol);
        let ty = |view: &Self, symbol| view.model.type_of_symbol(symbol).display(symbols);
        match found.kind {
            SymbolKind::Namespace | SymbolKind::NamedType => self.describe_type(symbol),
            SymbolKind::Method => self.describe_method(symbol, token),
            SymbolKind::Field => {
                let container = found
                    .container
                    .map(|container| self.container_display(container))
                    .unwrap_or_default();
                let in_enum = found.container.is_some_and(|container| {
                    symbols.get(container).type_kind() == Some(TypeKind::Enum)
                });
                let value = self.written_or_constant(symbol);
                if in_enum {
                    return match value {
                        Some(value) => format!("{container}.{} = {value}", found.name),
                        None => format!("{container}.{}", found.name),
                    };
                }
                let shown = ty(self, symbol);
                if found
                    .modifiers
                    .contains(rustlyn_semantics::Modifiers::CONST)
                {
                    match value {
                        Some(value) => {
                            format!("(constant) {shown} {container}.{} = {value}", found.name)
                        }
                        None => format!("(constant) {shown} {container}.{}", found.name),
                    }
                } else {
                    format!("(field) {shown} {container}.{}", found.name)
                }
            }
            SymbolKind::Property => {
                let Some(property) = found.as_property() else {
                    return describe_symbol(compilation, symbol);
                };
                let container = found
                    .container
                    .map(|container| self.container_display(container))
                    .unwrap_or_default();
                let mut accessors = Vec::new();
                if property.has_get {
                    accessors.push("get;");
                }
                if property.has_set {
                    accessors.push("set;");
                }
                if property.has_init {
                    accessors.push("init;");
                }
                let accessors = if accessors.is_empty() {
                    String::new()
                } else {
                    format!(" {{ {} }}", accessors.join(" "))
                };
                let shown = ty(self, symbol);
                if property.is_indexer {
                    let parameters = self.parameters_display(&property.parameters, false);
                    format!("{shown} {container}.this[{parameters}]{accessors}")
                } else {
                    format!("(property) {shown} {container}.{}{accessors}", found.name)
                }
            }
            SymbolKind::Event => {
                let container = found
                    .container
                    .map(|container| self.container_display(container))
                    .unwrap_or_default();
                format!("event {} {container}.{}", ty(self, symbol), found.name)
            }
            SymbolKind::Parameter => {
                format!("(parameter) {}", self.parameter_display(symbol, false))
            }
            SymbolKind::TypeParameter => match found.container {
                Some(container) if symbols.get(container).kind == SymbolKind::Method => {
                    let owner = self.describe_method_name(container);
                    format!("{} in {owner}", found.name)
                }
                Some(container) => {
                    format!("{} in {}", found.name, self.container_display(container))
                }
                None => found.name.clone(),
            },
            SymbolKind::Local => format!("(local variable) {} {}", ty(self, symbol), found.name),
        }
    }

    /// `class System.String`, `delegate TResult System.Func<T, TResult>(T
    /// arg)`, `namespace System.Collections`.
    fn describe_type(&self, symbol: SymbolId) -> String {
        let compilation = self.compilation();
        let symbols = compilation.symbols();
        let found = symbols.get(symbol);
        if found.type_kind() == Some(TypeKind::Delegate)
            && let Some(invoke) = symbols
                .lookup(symbol, "Invoke")
                .iter()
                .copied()
                .find(|&member| symbols.get(member).kind == SymbolKind::Method)
        {
            let returns = self.model.type_of_symbol(invoke).display(symbols);
            let name = describe_symbol(compilation, symbol);
            let name = name.strip_prefix("delegate ").unwrap_or(&name);
            let parameters = symbols
                .get(invoke)
                .as_method()
                .map(|method| self.parameters_display(&method.parameters, false))
                .unwrap_or_default();
            return format!("delegate {returns} {name}({parameters})");
        }
        describe_symbol(compilation, symbol)
    }

    /// A method: `void C.M(int a)`, with Roslyn's prefix where there is
    /// one — `(extension)`, `(awaitable)`, `(local function)`.
    fn describe_method(&mut self, symbol: SymbolId, token: Option<&SyntaxToken>) -> String {
        let symbols = self.compilation().symbols();
        let found = symbols.get(symbol);
        let Some(method) = found.as_method() else {
            return found.name.clone();
        };
        let returns = self.model.type_of_symbol(symbol);
        let awaitable = self.is_awaitable(&returns);
        let returns = returns.display(symbols);
        // `list.Where(...)` calls `Where` on the list: Roslyn shows it as a
        // member of the receiver's type, its `this` parameter gone.
        let reduced = method.is_extension && token.is_some_and(is_called_on_receiver);
        let generic = self.type_parameter_list(&method.type_parameters);
        let container = found
            .container
            .map(|container| self.container_display(container))
            .unwrap_or_default();
        let (container, parameters) = if reduced {
            let first = method.parameters.first().copied();
            let receiver = first
                .map(|first| self.model.type_of_symbol(first).display(symbols))
                .unwrap_or_default();
            (
                receiver,
                self.parameters_display(method.parameters.get(1..).unwrap_or(&[]), false),
            )
        } else {
            (
                container,
                self.parameters_display(&method.parameters, method.is_extension),
            )
        };
        let line = match method.method_kind {
            MethodKind::Constructor | MethodKind::StaticConstructor => {
                let name = found
                    .container
                    .map(|container| symbols.get(container).name.clone())
                    .unwrap_or_default();
                format!("{container}.{name}({parameters})")
            }
            MethodKind::Destructor => {
                let name = found
                    .container
                    .map(|container| symbols.get(container).name.clone())
                    .unwrap_or_default();
                format!("{container}.~{name}()")
            }
            MethodKind::Operator => {
                let operator = operator_text(&found.name);
                format!("{returns} {container}.operator {operator}({parameters})")
            }
            MethodKind::Conversion => {
                let kind = if found.name == "op_Explicit" {
                    "explicit"
                } else {
                    "implicit"
                };
                format!("{container}.{kind} operator {returns}({parameters})")
            }
            MethodKind::LocalFunction => {
                return format!(
                    "(local function) {returns} {}{generic}({parameters})",
                    found.name
                );
            }
            _ => format!(
                "{returns} {container}.{}{generic}({parameters})",
                found.name
            ),
        };
        match (awaitable, method.is_extension) {
            (true, true) => format!("(awaitable, extension) {line}"),
            (true, false) => format!("(awaitable) {line}"),
            (false, true) => format!("(extension) {line}"),
            (false, false) => line,
        }
    }

    /// `C.M<T>`: how a type parameter's method is named.
    fn describe_method_name(&self, method: SymbolId) -> String {
        let symbols = self.compilation().symbols();
        let found = symbols.get(method);
        let generic = found
            .as_method()
            .map(|detail| self.type_parameter_list(&detail.type_parameters))
            .unwrap_or_default();
        match found.container {
            Some(container) if symbols.get(container).kind == SymbolKind::NamedType => format!(
                "{}.{}{generic}",
                self.container_display(container),
                found.name
            ),
            _ => format!("{}{generic}", found.name),
        }
    }

    /// Whether what a method returns can be awaited: it has a
    /// `GetAwaiter`.
    fn is_awaitable(&self, ty: &Type) -> bool {
        let Type::Named { symbol, .. } = ty else {
            return false;
        };
        let symbols = self.compilation().symbols();
        self.model
            .binder()
            .lookup_member(*symbol, "GetAwaiter")
            .iter()
            .any(|&member| symbols.get(member).kind == SymbolKind::Method)
    }

    /// A type as the container of a member: `List<T>`, `Outer.Inner`, and
    /// `string` for `System.String`.
    fn container_display(&self, container: SymbolId) -> String {
        let symbols = self.compilation().symbols();
        let found = symbols.get(container);
        if found.kind != SymbolKind::NamedType {
            return symbols.qualified_name(container);
        }
        let arguments = found
            .as_named_type()
            .map(|named| {
                named
                    .type_parameters
                    .iter()
                    .map(|&parameter| Type::TypeParameter(parameter))
                    .collect()
            })
            .unwrap_or_default();
        Type::Named {
            symbol: container,
            type_arguments: arguments,
        }
        .display(symbols)
    }

    fn type_parameter_list(&self, parameters: &[SymbolId]) -> String {
        if parameters.is_empty() {
            return String::new();
        }
        let symbols = self.compilation().symbols();
        let names: Vec<&str> = parameters
            .iter()
            .map(|&parameter| symbols.get(parameter).name.as_str())
            .collect();
        format!("<{}>", names.join(", "))
    }

    fn parameters_display(&self, parameters: &[SymbolId], extension: bool) -> String {
        parameters
            .iter()
            .enumerate()
            .map(|(index, &parameter)| self.parameter_display(parameter, extension && index == 0))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// `ref int count`, `params string[] names`, `int retries = 3`.
    fn parameter_display(&self, parameter: SymbolId, this: bool) -> String {
        let symbols = self.compilation().symbols();
        let found = symbols.get(parameter);
        let mut shown = String::new();
        if this {
            shown.push_str("this ");
        }
        if let Some(detail) = found.as_parameter() {
            shown.push_str(match detail.ref_kind {
                RefKind::None => "",
                RefKind::Ref => "ref ",
                RefKind::Out => "out ",
                RefKind::In => "in ",
            });
            if detail.is_params {
                shown.push_str("params ");
            }
        }
        let ty = self.model.type_of_symbol(parameter);
        let ty = match ty {
            Type::ByRef(inner) => *inner,
            other => other,
        };
        shown.push_str(&ty.display(symbols));
        shown.push(' ');
        shown.push_str(&found.name);
        if found
            .as_parameter()
            .is_some_and(|detail| detail.has_default)
            && let Some(value) = self.written_or_constant(parameter)
        {
            shown.push_str(" = ");
            shown.push_str(&value);
        }
        shown
    }

    /// The value a constant, an enum member or an optional parameter was
    /// given: the text written where there is some, the value otherwise.
    fn written_or_constant(&self, symbol: SymbolId) -> Option<String> {
        let compilation = self.compilation();
        if !compilation.is_from_metadata(symbol)
            && let Some(node) = compilation.declaration_node(symbol)
            && let Some(written) = initializer_text(&node)
        {
            return Some(written);
        }
        self.constant_of(symbol)
    }

    /// A constant's value, as C# writes it.
    fn constant_of(&self, symbol: SymbolId) -> Option<String> {
        let compilation = self.compilation();
        let found = compilation.symbols().get(symbol);
        let binder = self.model.binder();
        let value = match found.kind {
            SymbolKind::Field => compilation
                .metadata_constant(symbol)
                .cloned()
                .or_else(|| binder.constant_value(symbol)),
            SymbolKind::Parameter
                if found
                    .as_parameter()
                    .is_some_and(|parameter| parameter.has_default) =>
            {
                binder.parameter_default(symbol)
            }
            _ => None,
        }?;
        Some(constant_text(&value))
    }

    /// `T is int`: what a generic type's or method's type parameters stand
    /// for where `token` uses it.
    fn type_parameter_map(&mut self, symbol: SymbolId, token: &SyntaxToken) -> Vec<String> {
        let symbols = self.compilation().symbols();
        self.type_arguments_at(symbol, token)
            .into_iter()
            .map(|(parameter, argument)| {
                format!(
                    "{} is {}",
                    symbols.get(parameter).name,
                    super::display_type(self.compilation(), &argument)
                )
            })
            .collect()
    }

    /// What the type parameters `symbol` is written with stand for where
    /// `token` uses it: a generic type's own, named with its arguments
    /// (`List<int>`); those of the type a member is declared in, as the
    /// receiver has them (`Key` of an `IGrouping<int, Item>`), the receiver's
    /// base types included; and a generic method's, as the call inferred
    /// them. A type parameter that stands for itself or for nothing known is
    /// left out.
    pub(super) fn type_arguments_at(
        &mut self,
        symbol: SymbolId,
        token: &SyntaxToken,
    ) -> Vec<(SymbolId, Type)> {
        let symbols = self.compilation().symbols();
        let found = symbols.get(symbol);
        let mut pairs: Vec<(SymbolId, Type)> = Vec::new();
        let parent = token.parent().clone();

        // A generic type named with its arguments: `List<int>`.
        if found.kind == SymbolKind::NamedType
            && parent.kind() == SyntaxKind::GenericName
            && let Type::Named {
                symbol: named,
                type_arguments,
            } = self.model.type_of_syntax(&parent)
            && named == symbol
            && let Some(detail) = found.as_named_type()
        {
            pairs.extend(detail.type_parameters.iter().copied().zip(type_arguments));
        }

        // A member reached through a constructed receiver: `list.Count` on
        // a `List<int>`, or on a class that derives from one.
        if matches!(
            found.kind,
            SymbolKind::Method | SymbolKind::Property | SymbolKind::Field | SymbolKind::Event
        ) && let Some(container) = found.container
            && let Some(access) = parent.parent().filter(|access| {
                matches!(
                    access.kind(),
                    SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression
                )
            })
            && access.children().last().as_ref() == Some(&parent)
            && let Some(receiver) = receiver_of(access)
        {
            let receiver = self.type_of(&receiver);
            pairs.extend(self.arguments_through(&receiver, container));
        }

        // A generic method's own, as the call inferred them.
        if let Some(method) = found.as_method()
            && !method.type_parameters.is_empty()
            && let Some(call) = parent.ancestors().find(|ancestor| {
                ancestor.kind() == SyntaxKind::InvocationExpression
                    && ancestor
                        .children()
                        .next()
                        .is_some_and(|callee| callee.span().contains_span(token.span()))
            })
            && let Some(body) = self.body_for(&call)
        {
            let span = call.span();
            if let Some(expression) = find_expression(&body, &|expression| {
                expression.span == span
                    && matches!(&expression.kind, BoundExpressionKind::Call { method, .. } if *method == symbol)
            }) && let BoundExpressionKind::Call { type_arguments, .. } = &expression.kind
            {
                pairs.extend(
                    method
                        .type_parameters
                        .iter()
                        .copied()
                        .zip(type_arguments.iter().cloned()),
                );
            }
        }
        pairs.retain(|(parameter, argument)| {
            !argument.is_error() && *argument != Type::TypeParameter(*parameter)
        });
        pairs
    }

    /// The type arguments `container`'s type parameters have on a receiver
    /// of type `receiver`: its own, or those its base types give it on the
    /// way up — `Add` on a `class Items : List<Item>` adds an `Item`.
    pub(super) fn arguments_through(
        &self,
        receiver: &Type,
        container: SymbolId,
    ) -> Vec<(SymbolId, Type)> {
        let symbols = self.compilation().symbols();
        let mut queue = vec![receiver.clone()];
        let mut seen = std::collections::HashSet::new();
        while let Some(ty) = queue.pop() {
            // A type parameter is seen through its constraints.
            if let Type::TypeParameter(parameter) = ty {
                if seen.insert(parameter) {
                    queue.extend(self.model.base_types_of(parameter));
                }
                continue;
            }
            let Type::Named {
                symbol,
                type_arguments,
            } = ty
            else {
                continue;
            };
            if !seen.insert(symbol) {
                continue;
            }
            let parameters = symbols
                .get(symbol)
                .as_named_type()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default();
            let pairs: Vec<(SymbolId, Type)> = parameters.into_iter().zip(type_arguments).collect();
            if symbol == container {
                return pairs;
            }
            let arguments: std::collections::HashMap<SymbolId, Type> = pairs.into_iter().collect();
            queue.extend(
                self.model
                    .base_types_of(symbol)
                    .into_iter()
                    .map(|base| base.substitute(&arguments)),
            );
        }
        Vec::new()
    }

    /// What a local function reads of the method around it.
    fn local_function_captures(&mut self, function: SymbolId, token: &SyntaxToken) -> Vec<String> {
        let Some(body) = self.body_for(token.parent()) else {
            return Vec::new();
        };
        let Some(bound) = body
            .local_functions
            .iter()
            .find(|bound| bound.symbol == function)
        else {
            return Vec::new();
        };
        let symbols = self.compilation().symbols();
        captured_names(
            bound.captured.iter().filter_map(|local| {
                body.locals
                    .get(local.0 as usize)
                    .map(|local| local.name.clone())
            }),
            bound
                .captured_parameters
                .iter()
                .map(|&parameter| symbols.get(parameter).name.clone()),
            bound.captures_this,
        )
    }

    // MARK: - keywords

    /// `var`: the type it stands for.
    fn var_info(&mut self, token: &SyntaxToken) -> Option<QuickInfo> {
        let ty = self.var_type(token)?;
        Some(self.type_info(&ty))
    }

    /// The type a `var` stands for, with its type arguments: that of the
    /// variable it declares. None when `token` is no such `var`.
    pub(super) fn var_type(&mut self, token: &SyntaxToken) -> Option<Type> {
        if token.value_text() != "var" || !self.is_var(token) {
            return None;
        }
        let declaration = token.parent().parent()?.clone();
        let body = self.body_for(&declaration)?;
        declaration
            .descendant_tokens()
            .filter(|other| {
                other.kind() == SyntaxKind::IdentifierToken
                    && other.span().start() > token.span().start()
            })
            .find_map(|other| match body.symbol_at(other.span()) {
                Some(BoundSymbol::Local(local)) => body
                    .locals
                    .get(local.0 as usize)
                    .map(|local| local.ty.clone()),
                _ => body
                    .locals
                    .iter()
                    .find(|local| local.span == other.span())
                    .map(|local| local.ty.clone()),
            })
    }

    /// A type as the thing quick info is about: a named type's description
    /// and documentation, or how an array or a tuple reads.
    fn type_info(&mut self, ty: &Type) -> QuickInfo {
        match ty {
            Type::Named {
                symbol,
                type_arguments,
            } => {
                let mut info = self.symbol_info(*symbol, None);
                let symbols = self.compilation().symbols();
                if let Some(named) = symbols.get(*symbol).as_named_type() {
                    info.type_parameters = named
                        .type_parameters
                        .iter()
                        .zip(type_arguments)
                        .filter(|(_, argument)| !argument.is_error())
                        .map(|(&parameter, argument)| {
                            format!(
                                "{} is {}",
                                symbols.get(parameter).name,
                                argument.display(symbols)
                            )
                        })
                        .collect();
                }
                info
            }
            Type::TypeParameter(symbol) => self.symbol_info(*symbol, None),
            other => QuickInfo {
                description: other.display(self.compilation().symbols()),
                ..QuickInfo::default()
            },
        }
    }

    /// `nameof(count)`: the string it makes.
    fn nameof_info(&mut self, token: &SyntaxToken) -> Option<QuickInfo> {
        let call = token
            .parent()
            .ancestors()
            .find(|ancestor| ancestor.kind() == SyntaxKind::InvocationExpression)?;
        if call.children().next()?.text().trim() != "nameof" {
            return None;
        }
        let argument = call
            .child_of_kind(SyntaxKind::ArgumentList)?
            .child_of_kind(SyntaxKind::Argument)?;
        let last = argument
            .descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .last()?;
        let value = constant_text(&ConstantValue::String(last.value_text().to_string()));
        Some(QuickInfo {
            description: format!("string nameof({}) = {value}", argument.text().trim()),
            constant: Some(value),
            ..QuickInfo::default()
        })
    }

    /// The `new` of a `new()`: the constructor it calls.
    fn implicit_new_info(&mut self, token: &SyntaxToken) -> Option<QuickInfo> {
        let node = token.parent().clone();
        let body = self.body_for(&node)?;
        let span = node.span();
        let created = find_expression(&body, &|expression| {
            expression.span == span
                && matches!(expression.kind, BoundExpressionKind::ObjectCreation { .. })
        })?;
        match &created.kind {
            BoundExpressionKind::ObjectCreation {
                constructor: Some(constructor),
                ..
            } => Some(self.symbol_info(*constructor, None)),
            _ => {
                let ty = created.ty.clone();
                Some(self.type_info(&ty))
            }
        }
    }

    /// The `=>` of a lambda: its delegate type and what it captures.
    fn lambda_info(&mut self, token: &SyntaxToken) -> Option<QuickInfo> {
        let lambda = token.parent().clone();
        if !matches!(
            lambda.kind(),
            SyntaxKind::SimpleLambdaExpression
                | SyntaxKind::ParenthesizedLambdaExpression
                | SyntaxKind::AnonymousMethodExpression
        ) {
            return None;
        }
        let body = self.body_for(&lambda)?;
        let bound = body
            .lambdas
            .iter()
            .find(|bound| bound.span == lambda.span())?;
        let symbols = self.compilation().symbols();
        let description = body
            .type_at(lambda.span())
            .filter(|ty| !ty.is_error())
            .map_or_else(|| "lambda expression".to_string(), |ty| ty.display(symbols));
        let captures = captured_names(
            bound.captured.iter().filter_map(|local| {
                body.locals
                    .get(local.0 as usize)
                    .map(|local| local.name.clone())
            }),
            bound
                .captured_parameters
                .iter()
                .map(|&parameter| symbols.get(parameter).name.clone()),
            bound.captures_this,
        );
        Some(QuickInfo {
            description,
            captures,
            ..QuickInfo::default()
        })
    }

    /// An operator: the user-defined operator it calls, where it calls one.
    fn operator_info(&mut self, token: &SyntaxToken) -> Option<QuickInfo> {
        let expression = token.parent().clone();
        let body = self.body_for(&expression)?;
        let span = expression.span();
        let symbols = self.compilation().symbols();
        let call = find_expression(&body, &|found| {
            found.span == span
                && matches!(&found.kind, BoundExpressionKind::Call { method, .. }
                if symbols.get(*method).as_method().is_some_and(|method| {
                    matches!(method.method_kind, MethodKind::Operator | MethodKind::Conversion)
                }))
        })?;
        let BoundExpressionKind::Call { method, .. } = &call.kind else {
            return None;
        };
        let method = *method;
        Some(self.symbol_info(method, None))
    }
}

/// Whether the method named by `token` is called on something to the left
/// of a dot, as an extension method is when it looks like a member.
fn is_called_on_receiver(token: &SyntaxToken) -> bool {
    let mut node = token.parent().clone();
    if node.kind() == SyntaxKind::GenericName || node.kind() == SyntaxKind::IdentifierName {
        let Some(parent) = node.parent().cloned() else {
            return false;
        };
        node = parent;
    }
    node.kind() == SyntaxKind::SimpleMemberAccessExpression
        || node.kind() == SyntaxKind::MemberBindingExpression
}

fn is_operator_token(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::PlusToken
            | SyntaxKind::MinusToken
            | SyntaxKind::AsteriskToken
            | SyntaxKind::SlashToken
            | SyntaxKind::PercentToken
            | SyntaxKind::AmpersandToken
            | SyntaxKind::BarToken
            | SyntaxKind::CaretToken
            | SyntaxKind::ExclamationToken
            | SyntaxKind::TildeToken
            | SyntaxKind::EqualsEqualsToken
            | SyntaxKind::ExclamationEqualsToken
            | SyntaxKind::LessThanToken
            | SyntaxKind::GreaterThanToken
            | SyntaxKind::LessThanEqualsToken
            | SyntaxKind::GreaterThanEqualsToken
            | SyntaxKind::LessThanLessThanToken
            | SyntaxKind::GreaterThanGreaterThanToken
    )
}

/// `op_Addition` as the operator it is written as.
fn operator_text(name: &str) -> &str {
    match name {
        "op_Addition" | "op_UnaryPlus" => "+",
        "op_Subtraction" | "op_UnaryNegation" => "-",
        "op_Multiply" => "*",
        "op_Division" => "/",
        "op_Modulus" => "%",
        "op_BitwiseAnd" => "&",
        "op_BitwiseOr" => "|",
        "op_ExclusiveOr" => "^",
        "op_LogicalNot" => "!",
        "op_OnesComplement" => "~",
        "op_Equality" => "==",
        "op_Inequality" => "!=",
        "op_LessThan" => "<",
        "op_GreaterThan" => ">",
        "op_LessThanOrEqual" => "<=",
        "op_GreaterThanOrEqual" => ">=",
        "op_LeftShift" => "<<",
        "op_RightShift" => ">>",
        "op_UnsignedRightShift" => ">>>",
        "op_Increment" | "op_IncrementAssignment" => "++",
        "op_Decrement" | "op_DecrementAssignment" => "--",
        "op_AdditionAssignment" => "+=",
        "op_SubtractionAssignment" => "-=",
        "op_MultiplicationAssignment" => "*=",
        "op_DivisionAssignment" => "/=",
        "op_ModulusAssignment" => "%=",
        "op_BitwiseAndAssignment" => "&=",
        "op_BitwiseOrAssignment" => "|=",
        "op_ExclusiveOrAssignment" => "^=",
        "op_LeftShiftAssignment" => "<<=",
        "op_RightShiftAssignment" => ">>=",
        "op_UnsignedRightShiftAssignment" => ">>>=",
        "op_True" => "true",
        "op_False" => "false",
        other => other,
    }
}

/// The text after `=` in a declaration: a constant's, an enum member's, an
/// optional parameter's.
fn initializer_text(node: &SyntaxNode) -> Option<String> {
    let clause = node.child_of_kind(SyntaxKind::EqualsValueClause)?;
    let value = clause.children().last()?;
    let text = value.text();
    let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
    (!text.is_empty()).then_some(text)
}

/// A constant as C# writes it.
fn constant_text(value: &ConstantValue) -> String {
    match value {
        ConstantValue::Null => "null".to_string(),
        ConstantValue::Boolean(value) => value.to_string(),
        ConstantValue::Char(value) => format!("'{}'", value.escape_default()),
        ConstantValue::Int32(value) => value.to_string(),
        ConstantValue::UInt32(value) => value.to_string(),
        ConstantValue::Int64(value) => value.to_string(),
        ConstantValue::UInt64(value) => value.to_string(),
        ConstantValue::Single(value) => format!("{value}f"),
        ConstantValue::Double(value) => value.to_string(),
        ConstantValue::String(value) => {
            let mut out = String::from("\"");
            for c in value.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    '\r' => out.push_str("\\r"),
                    '\t' => out.push_str("\\t"),
                    other => out.push(other),
                }
            }
            out.push('"');
            out
        }
    }
}

/// The text of `<tag name="name">` in a documentation comment.
fn tagged(xml: &str, tag: &str, name: &str) -> Option<String> {
    let open = format!("<{tag} name=\"{name}\"");
    let start = xml.find(&open)?;
    let rest = &xml[start..];
    let body_start = rest.find('>')? + 1;
    let close = rest.find(&format!("</{tag}>"))?;
    (close >= body_start).then(|| plain(&rest[body_start..close]))
}

/// The types each `<exception cref="...">` names.
fn exceptions(xml: &str) -> Vec<String> {
    let mut found = Vec::new();
    let mut rest = xml;
    while let Some(start) = rest.find("<exception cref=\"") {
        rest = &rest[start + "<exception cref=\"".len()..];
        let Some(quote) = rest.find('"') else { break };
        let cref = &rest[..quote];
        let name = cref.split_once(':').map_or(cref, |(_, name)| name);
        let name = name.rsplit('.').next().unwrap_or(name);
        found.push(name.to_string());
        rest = &rest[quote..];
    }
    found
}

/// Captured variables in the order Roslyn lists them: locals and
/// parameters by name, `this` first where it is read.
fn captured_names(
    locals: impl Iterator<Item = String>,
    parameters: impl Iterator<Item = String>,
    this: bool,
) -> Vec<String> {
    let mut names: Vec<String> = parameters.chain(locals).collect();
    names.sort();
    names.dedup();
    if this {
        names.insert(0, "this".to_string());
    }
    names
}

/// What a member access is on: `list` in `list.Count`, and in
/// `list?.Count` the expression before the `?`.
pub(super) fn receiver_of(access: &SyntaxNode) -> Option<SyntaxNode> {
    if access.kind() == SyntaxKind::MemberBindingExpression {
        return access
            .ancestors()
            .find(|ancestor| ancestor.kind() == SyntaxKind::ConditionalAccessExpression)
            .and_then(|conditional| conditional.children().next());
    }
    access.children().next()
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::tests::{at, compile};
    use super::*;

    fn info(text: &str, marker: &str, into: usize) -> QuickInfo {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        semantic
            .quick_info(Path::new("/p/C.cs"), at(text, marker, into), None)
            .unwrap_or_else(|| panic!("quick info at {marker}"))
    }

    fn description(text: &str, marker: &str, into: usize) -> String {
        info(text, marker, into).description
    }

    /// A `switch` whose arms are a typed delegate and a lambda is that
    /// delegate, as `?:` would be, and the lambda is bound against it.
    #[test]
    fn a_lambda_beside_a_typed_switch_arm_takes_its_type() {
        let text = "class Item { public int Value; }\n\
                    class C { void M(int n) {\n\
                      var pick = n switch { 0 => (System.Func<Item, int>)(first => first.Value), _ => other => other.Value * 2 };\n\
                    } }\n";
        assert_eq!(
            description(text, "first.Value", 0),
            "(parameter) Item first"
        );
        assert_eq!(
            description(text, "other.Value", 0),
            "(parameter) Item other"
        );
        assert_eq!(
            info(text, "var pick", 0).type_parameters,
            vec!["T is Item".to_string(), "TResult is int".to_string()]
        );
    }

    /// A lambda given to a call that does not resolve is still bound for
    /// the editor: its parameter is there, typed as nothing known, and a
    /// lambda inside it whose own call resolves has its types.
    #[test]
    fn a_lambda_of_a_call_that_does_not_resolve_has_its_parameters() {
        let text = "class Item { public int Value; }\n\
                    delegate bool Test(Item item);\n\
                    class Items { public Item Find(Test test) => null; }\n\
                    class C { Items items; void M() {\n\
                      Missing.Run(first => first.Go());\n\
                      Missing.Run(() => items.Find(inner => inner.Value > 0));\n\
                      missing.Changed += (sender, args) => { };\n\
                    } }\n";
        assert_eq!(description(text, "first.Go", 0), "(parameter) ? first");
        assert_eq!(
            description(text, "inner.Value", 0),
            "(parameter) Item inner"
        );
        assert_eq!(description(text, "sender,", 0), "(parameter) ? sender");
    }

    /// A lambda named as an argument after others that have to be worked
    /// out first, in the order written, goes to its parameter all the same:
    /// what stores them ahead of the call is not the lambda.
    #[test]
    fn a_lambda_named_after_arguments_stored_ahead_takes_its_parameter() {
        let text = "using System;\n\
                    class Item { public int Value; }\n\
                    class C {\n\
                      static int Get() => 1;\n\
                      static void Run(Action<Item> each, int a, int b) { }\n\
                      void M() { Run(b: Get(), a: Get(), each: item => item.Value.ToString()); }\n\
                    }\n";
        assert_eq!(description(text, "item.Value", 0), "(parameter) Item item");
    }

    /// Only an `out var` takes the type of the parameter it is passed to: a
    /// variable whose type is not known stays so wherever it is passed.    /// Only an `out var` takes the type of the parameter it is passed to: a
    /// variable whose type is not known stays so wherever it is passed.
    #[test]
    fn a_variable_of_unknown_type_is_not_typed_by_the_call_it_is_passed_to() {
        let text = "class C { static void Show(bool flag) { } static void Make(out int made) { made = 1; } void M() { var value = Missing(); Show(value); Make(out var made); } }\n";
        assert_eq!(description(text, "value);", 0), "(local variable) ? value");
        assert_eq!(description(text, "made);", 0), "(local variable) int made");
    }

    const GAME: &str = "using System;\nusing System.Collections.Generic;\n\
        namespace Game {\n\
        enum Color { Red, Green = 4 }\n\
        class Box<T> { public T Item; public int Count { get; private set; } public T this[int index] { get { return Item; } } }\n\
        static class Ext { public static int Twice(this int value, int times = 2) => value * times; }\n\
        /// <summary>A player.</summary>\n\
        class Player {\n\
          public const int Max = 4 * 10;\n\
          private int health;\n\
          public event Action Died;\n\
          /// <summary>Heals the player.</summary>\n\
          /// <param name=\"amount\">How much.</param>\n\
          /// <returns>The new health.</returns>\n\
          /// <remarks>Never above <see cref=\"Max\"/>.</remarks>\n\
          /// <exception cref=\"T:System.ArgumentException\">When negative.</exception>\n\
          public int Heal(int amount, ref int total, params int[] extra) { return health; }\n\
          public Player(string name) { }\n\
          static T Pick<T>(T a, T b) => a;\n\
          void Run(List<string> names, Box<int> box) {\n\
            var count = names.Count;\n\
            const int limit = 3;\n\
            int total = 0;\n\
            Heal(limit, ref total);\n\
            var picked = Pick(1, 2);\n\
            var n = box.Count + box[0] + 5.Twice();\n\
            Func<int, int> add = x => x + count;\n\
            int Local(int y) => y + health;\n\
            var c = Color.Green;\n\
            var s = nameof(health);\n\
          }\n\
        }\n\
        }\n";

    #[test]
    fn locals_parameters_and_constants() {
        assert_eq!(
            description(GAME, "count = names", 0),
            "(local variable) int count"
        );
        assert_eq!(
            description(GAME, "limit = 3", 0),
            "(local constant) int limit = 3"
        );
        assert_eq!(description(GAME, "x + count", 0), "(parameter) int x");
        assert_eq!(
            description(GAME, "names.Count", 0),
            "(parameter) List<string> names"
        );
        assert_eq!(
            description(GAME, "Max = 4", 0),
            "(constant) int Player.Max = 4 * 10"
        );
        assert_eq!(info(GAME, "Max = 4", 0).constant.as_deref(), Some("40"));
        assert_eq!(
            description(GAME, "health;\n", 0),
            "(field) int Player.health"
        );
        assert_eq!(description(GAME, "Green;", 0), "Color.Green = 4");
        assert_eq!(description(GAME, "Red,", 0), "Color.Red = 0");
    }

    #[test]
    fn members_are_written_out_with_their_container() {
        assert_eq!(
            description(GAME, "Count;\n", 0),
            "(property) int List<T>.Count { get; }"
        );
        assert_eq!(
            description(GAME, "Count +", 0),
            "(property) int Box<T>.Count { get; set; }"
        );
        assert_eq!(
            description(GAME, "Heal(limit", 0),
            "int Player.Heal(int amount, ref int total, params int[] extra)"
        );
        assert_eq!(
            description(GAME, "Player(string", 0),
            "Player.Player(string name)"
        );
        assert_eq!(description(GAME, "Died", 0), "event Action Player.Died");
        assert_eq!(
            description(GAME, "this[int", 0),
            "T Box<T>.this[int index] { get; }"
        );
        assert_eq!(
            description(GAME, "Twice()", 0),
            "(extension) int int.Twice(int times = 2)"
        );
        assert_eq!(
            description(GAME, "Twice(this", 0),
            "(extension) int Ext.Twice(this int value, int times = 2)"
        );
        assert_eq!(
            description(GAME, "Local(int", 0),
            "(local function) int Local(int y)"
        );
    }

    #[test]
    fn types_namespaces_and_type_parameters() {
        assert_eq!(description(GAME, "Player {", 0), "class Game.Player");
        assert_eq!(description(GAME, "Color {", 0), "enum Game.Color");
        assert_eq!(description(GAME, "Game {", 0), "namespace Game");
        assert_eq!(
            description(GAME, "List<string>", 0),
            "class System.Collections.Generic.List<T>"
        );
        assert_eq!(
            info(GAME, "List<string>", 0).type_parameters,
            vec!["T is string"]
        );
        assert_eq!(description(GAME, "T Item", 0), "T in Box<T>");
        assert_eq!(description(GAME, "T a", 0), "T in Player.Pick<T>");
        assert_eq!(
            description(GAME, "Action Died", 0),
            "delegate void System.Action()"
        );
    }

    #[test]
    fn keywords_that_stand_for_something() {
        let var = info(GAME, "var count", 0);
        assert_eq!(var.description, "struct System.Int32");
        assert_eq!(var.span, TextSpan::new(at(GAME, "var count", 0), 3));
        assert_eq!(description(GAME, "int total = 0", 0), "struct System.Int32");
        let nameof = info(GAME, "nameof", 0);
        assert_eq!(nameof.constant.as_deref(), Some("\"health\""));
        assert_eq!(nameof.description, "string nameof(health) = \"health\"");
        assert_eq!(description(GAME, "var c =", 0), "enum Game.Color");
    }

    #[test]
    fn documentation_sections() {
        let heal = info(GAME, "Heal(limit", 0);
        assert_eq!(heal.summary, "Heals the player.");
        assert_eq!(
            heal.parameters,
            vec![("amount".to_string(), "How much.".to_string())]
        );
        assert_eq!(heal.returns, "The new health.");
        assert_eq!(heal.remarks, "Never above Max.");
        assert_eq!(heal.exceptions, vec!["ArgumentException"]);
        // A parameter's own line of its method's comment.
        assert_eq!(info(GAME, "amount,", 0).summary, "How much.");
        // A type's comment, through `var`.
        let text = "/// <summary>A point.</summary>\nclass Point { }\nclass C { void M() { var p = new Point(); } }\n";
        assert_eq!(info(text, "var p", 0).summary, "A point.");
    }

    #[test]
    fn type_arguments_at_the_use() {
        assert_eq!(info(GAME, "Pick(1", 0).type_parameters, vec!["T is int"]);
        assert_eq!(description(GAME, "Pick(1", 0), "T Player.Pick<T>(T a, T b)");
        assert_eq!(info(GAME, "Count +", 0).type_parameters, vec!["T is int"]);
    }

    #[test]
    fn captures_of_lambdas_and_local_functions() {
        let lambda = info(GAME, "=> x + count", 0);
        assert_eq!(lambda.captures, vec!["count"]);
        assert_eq!(lambda.description, "Func<int, int>");
        let local = info(GAME, "Local(int", 0);
        assert_eq!(local.captures, vec!["this"]);
    }

    #[test]
    fn awaitable_methods_and_user_defined_operators() {
        let text = "namespace System.Threading.Tasks {\n\
                      public class Awaiter<T> { public bool IsCompleted => true; public T GetResult() => default; }\n\
                      public class Task<T> { public Awaiter<T> GetAwaiter() => null; }\n\
                    }\n\
                    namespace Game {\n\
                      using System.Threading.Tasks;\n\
                      struct Money { public static Money operator +(Money a, Money b) => a; public static implicit operator int(Money m) => 0; }\n\
                      class C {\n\
                        Task<int> LoadAsync() => null;\n\
                        void M(Money a, Money b) { var t = LoadAsync(); var sum = a + b; }\n\
                      }\n\
                    }\n";
        assert_eq!(
            description(text, "LoadAsync();", 0),
            "(awaitable) Task<int> C.LoadAsync()"
        );
        assert_eq!(
            description(text, "+ b", 0),
            "Money Money.operator +(Money a, Money b)"
        );
        assert_eq!(
            description(text, "implicit", 0),
            "Money.implicit operator int(Money m)"
        );
    }

    #[test]
    fn literals_and_plain_keywords_have_nothing() {
        let semantic = compile(&[("C.cs", GAME)], false).expect("compiled");
        for (marker, into) in [("3;\n", 0), ("return health", 0), ("\"amount\"", 1)] {
            assert!(
                semantic
                    .quick_info(Path::new("/p/C.cs"), at(GAME, marker, into), None)
                    .is_none(),
                "{marker}"
            );
        }
    }

    #[test]
    fn unsaved_text_is_described_as_typed() {
        let compiled = "class C { void M() { } }\n";
        let semantic = compile(&[("C.cs", compiled)], false).expect("compiled");
        let typed = "class C { void M() { var word = \"a\"; var n = word.Length; } }\n";
        let found = semantic
            .quick_info(Path::new("/p/C.cs"), at(typed, "word.", 0), Some(typed))
            .expect("typed");
        assert_eq!(found.description, "(local variable) string word");
        let found = semantic
            .quick_info(Path::new("/p/C.cs"), at(typed, "Length", 0), Some(typed))
            .expect("typed");
        assert_eq!(found.description, "(property) int string.Length { get; }");
    }
}
