//! Prints the bound tree of every method body in a file.
//!
//! ```sh
//! cargo run --example bound -- Program.cs
//! cargo run --example bound -- Program.cs --references $FW
//! ```
//!
//! With `--references`, the assemblies of that directory are what the file
//! is bound against, as the `build` example does; without, only the corlib
//! model the binder carries.

use rustlyn_semantics::{
    BoundBody, BoundExpression, BoundExpressionKind, BoundPattern, BoundPatternKind,
    BoundStatement, BoundStatementKind, BoundSwitchLabel, Compilation, SemanticModel, SymbolKind,
};
use rustlyn_syntax::{SyntaxKind, parse};
use rustlyn_text::SourceText;

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    let path = arguments
        .get(1)
        .cloned()
        .expect("usage: bound <file.cs> [--references <dir>]");
    let text = std::fs::read_to_string(&path).expect("the file should be readable");
    let trees = vec![parse(SourceText::new(path, text))];
    let references: Vec<Vec<u8>> = arguments
        .iter()
        .position(|argument| argument == "--references")
        .and_then(|at| arguments.get(at + 1))
        .map(|directory| {
            let mut paths: Vec<_> = std::fs::read_dir(directory)
                .expect("the references directory should be readable")
                .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                .filter(|path| path.extension().is_some_and(|extension| extension == "dll"))
                .collect();
            paths.sort();
            paths
                .iter()
                .filter_map(|path| std::fs::read(path).ok())
                .collect()
        })
        .unwrap_or_default();
    let images: Vec<&[u8]> = references.iter().map(Vec::as_slice).collect();
    // The file is the tree after the corlib model, where there is one.
    let (compilation, tree) = if images.is_empty() {
        (Compilation::create(trees), 1)
    } else {
        (Compilation::create_with_references(trees, &images), 0)
    };
    let model = SemanticModel::new(&compilation, tree);

    for node in compilation.source_trees()[0].root().descendants() {
        if !matches!(
            node.kind(),
            SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::PropertyDeclaration
                | SyntaxKind::VariableDeclarator
        ) || (node.kind() == SyntaxKind::VariableDeclarator
            && node.child_of_kind(SyntaxKind::EqualsValueClause).is_none())
        {
            continue;
        }
        let name = compilation.declared_symbol(tree, node.span()).map_or_else(
            || "<unnamed>".to_string(),
            |symbol| compilation.symbols().qualified_name(symbol),
        );
        let Some(body) = model.bound_body_containing(&node) else {
            continue;
        };
        println!("{name}");
        for (index, local) in body.locals.iter().enumerate() {
            println!(
                "  local {index}: {}{} {}",
                if local.by_ref { "ref " } else { "" },
                local.ty.display(compilation.symbols()),
                local.name
            );
        }
        for statement in &body.statements {
            print_statement(&compilation, &body, statement, 1);
        }
        println!();
    }
}

fn indent(depth: usize) -> String {
    "  ".repeat(depth)
}

fn print_statement(
    compilation: &Compilation,
    body: &BoundBody,
    statement: &BoundStatement,
    depth: usize,
) {
    let pad = indent(depth);
    match &statement.kind {
        BoundStatementKind::Block(statements) => {
            println!("{pad}Block");
            for inner in statements {
                print_statement(compilation, body, inner, depth + 1);
            }
        }
        BoundStatementKind::LocalDeclaration { local, initializer } => {
            println!("{pad}Local {} = ", body.locals[local.0 as usize].name);
            if let Some(value) = initializer {
                print_expression(compilation, body, value, depth + 1);
            }
        }
        BoundStatementKind::Expression(value) => {
            println!("{pad}Expression");
            print_expression(compilation, body, value, depth + 1);
        }
        BoundStatementKind::If {
            condition,
            consequence,
            alternative,
        } => {
            println!("{pad}If");
            print_expression(compilation, body, condition, depth + 1);
            print_statement(compilation, body, consequence, depth + 1);
            if let Some(alternative) = alternative {
                println!("{pad}Else");
                print_statement(compilation, body, alternative, depth + 1);
            }
        }
        BoundStatementKind::While {
            condition,
            body: inner,
        } => {
            println!("{pad}While");
            print_expression(compilation, body, condition, depth + 1);
            print_statement(compilation, body, inner, depth + 1);
        }
        BoundStatementKind::DoWhile {
            body: inner,
            condition,
        } => {
            println!("{pad}DoWhile");
            print_statement(compilation, body, inner, depth + 1);
            print_expression(compilation, body, condition, depth + 1);
        }
        BoundStatementKind::For {
            initializers,
            condition,
            incrementors,
            body: inner,
        } => {
            println!("{pad}For");
            for initializer in initializers {
                print_statement(compilation, body, initializer, depth + 1);
            }
            if let Some(condition) = condition {
                print_expression(compilation, body, condition, depth + 1);
            }
            for incrementor in incrementors {
                print_expression(compilation, body, incrementor, depth + 1);
            }
            print_statement(compilation, body, inner, depth + 1);
        }
        BoundStatementKind::ForEach {
            local,
            collection,
            body: inner,
            enumeration,
            walk: _,
            dimensions: _,
        } => {
            let how = if enumeration.is_some() {
                " (enumerator)"
            } else {
                ""
            };
            println!("{pad}ForEach {}{how}", body.locals[local.0 as usize].name);
            print_expression(compilation, body, collection, depth + 1);
            print_statement(compilation, body, inner, depth + 1);
        }
        BoundStatementKind::Switch {
            governing,
            sections,
        } => {
            println!("{pad}Switch");
            print_expression(compilation, body, governing, depth + 1);
            for section in sections {
                for label in &section.labels {
                    match label {
                        BoundSwitchLabel::Default => println!("{pad}  Default"),
                        BoundSwitchLabel::Case(case) => {
                            print!("{pad}  Case ");
                            print_pattern(compilation, body, &case.pattern);
                            println!();
                            if let Some(when) = &case.when {
                                print_expression(compilation, body, when, depth + 2);
                            }
                        }
                    }
                }
                for statement in &section.statements {
                    print_statement(compilation, body, statement, depth + 2);
                }
            }
        }
        BoundStatementKind::Return(value) => {
            println!("{pad}Return");
            if let Some(value) = value {
                print_expression(compilation, body, value, depth + 1);
            }
        }
        BoundStatementKind::Throw(value) => {
            println!("{pad}Throw");
            if let Some(value) = value {
                print_expression(compilation, body, value, depth + 1);
            }
        }
        other => println!("{pad}{other:?}"),
    }
}

fn print_expression(
    compilation: &Compilation,
    body: &BoundBody,
    expression: &BoundExpression,
    depth: usize,
) {
    let pad = indent(depth);
    let ty = expression.ty.display(compilation.symbols());
    let name = |symbol| {
        let symbols = compilation.symbols();
        if symbols.get(symbol).kind == SymbolKind::Parameter {
            symbols.get(symbol).name.clone()
        } else {
            symbols.qualified_name(symbol)
        }
    };

    match &expression.kind {
        BoundExpressionKind::Literal(value) => println!("{pad}Literal {value:?} : {ty}"),
        BoundExpressionKind::Local(local) => {
            println!("{pad}Local {} : {ty}", body.locals[local.0 as usize].name);
        }
        BoundExpressionKind::Parameter(symbol) => {
            println!("{pad}Parameter {} : {ty}", name(*symbol));
        }
        BoundExpressionKind::This => println!("{pad}This : {ty}"),
        BoundExpressionKind::Base => println!("{pad}Base : {ty}"),
        BoundExpressionKind::TypeExpression(symbol) => {
            println!("{pad}Type {}", name(*symbol));
        }
        BoundExpressionKind::Field { receiver, field } => {
            println!("{pad}Field {} : {ty}", name(*field));
            if let Some(receiver) = receiver {
                print_expression(compilation, body, receiver, depth + 1);
            }
        }
        BoundExpressionKind::Property { receiver, property } => {
            println!("{pad}Property {} : {ty}", name(*property));
            if let Some(receiver) = receiver {
                print_expression(compilation, body, receiver, depth + 1);
            }
        }
        BoundExpressionKind::UnboundLambda(_) => {
            println!("{pad}UnboundLambda");
        }
        BoundExpressionKind::Lambda(index) => {
            let Some(lambda) = body.lambdas.get(*index) else {
                println!("{pad}Lambda <missing>");
                return;
            };
            let names: Vec<&str> = lambda
                .parameters
                .iter()
                .map(|local| body.locals[local.0 as usize].name.as_str())
                .collect();
            let mut takes: Vec<String> = lambda
                .captured
                .iter()
                .map(|local| body.locals[local.0 as usize].name.clone())
                .collect();
            if lambda.captures_this {
                takes.push("this".to_string());
            }
            let capture = if takes.is_empty() {
                String::new()
            } else {
                format!(" captures {}", takes.join(", "))
            };
            println!("{pad}Lambda ({}) : {ty}{capture}", names.join(", "));
            print_statement(compilation, body, &lambda.body, depth + 1);
        }
        BoundExpressionKind::MethodGroup {
            receiver,
            candidates,
        } => {
            let names: Vec<String> = candidates.iter().map(|id| name(*id)).collect();
            println!("{pad}MethodGroup {}", names.join(" | "));
            if let Some(receiver) = receiver {
                print_expression(compilation, body, receiver, depth + 1);
            }
        }
        BoundExpressionKind::DelegateCreation {
            method,
            receiver,
            virtual_dispatch,
            ..
        } => {
            let how = if *virtual_dispatch {
                "ldvirtftn"
            } else {
                "ldftn"
            };
            println!("{pad}DelegateCreation {how} {} : {ty}", name(*method));
            if let Some(receiver) = receiver {
                print_expression(compilation, body, receiver, depth + 1);
            }
        }
        BoundExpressionKind::Call {
            receiver,
            method,
            type_arguments,
            arguments,
            virtual_call,
        } => {
            let how = if *virtual_call { "callvirt" } else { "call" };
            let generic = if type_arguments.is_empty() {
                String::new()
            } else {
                let names: Vec<String> = type_arguments
                    .iter()
                    .map(|argument| argument.display(compilation.symbols()))
                    .collect();
                format!("<{}>", names.join(", "))
            };
            println!("{pad}Call {how} {}{generic} : {ty}", name(*method));
            if let Some(receiver) = receiver {
                print_expression(compilation, body, receiver, depth + 1);
            }
            for argument in arguments {
                print_expression(compilation, body, argument, depth + 1);
            }
        }
        BoundExpressionKind::ObjectCreation {
            constructor,
            arguments,
            initializers,
        } => {
            let which = constructor.map_or_else(|| "<none>".to_string(), name);
            println!("{pad}New {which} : {ty}");
            for argument in arguments {
                print_expression(compilation, body, argument, depth + 1);
            }
            for initializer in initializers {
                print_expression(compilation, body, initializer, depth + 1);
            }
        }
        BoundExpressionKind::With {
            receiver,
            initializers,
        } => {
            println!("{pad}With : {ty}");
            print_expression(compilation, body, receiver, depth + 1);
            for initializer in initializers {
                print_expression(compilation, body, initializer, depth + 1);
            }
        }
        BoundExpressionKind::CreatedObject => println!("{pad}CreatedObject : {ty}"),
        BoundExpressionKind::ArrayCreation {
            lengths, elements, ..
        } => {
            println!("{pad}NewArray : {ty}");
            for length in lengths {
                print_expression(compilation, body, length, depth + 1);
            }
            for element in elements {
                print_expression(compilation, body, element, depth + 1);
            }
        }
        BoundExpressionKind::ArrayAccess { array, indices } => {
            println!("{pad}ArrayAccess : {ty}");
            print_expression(compilation, body, array, depth + 1);
            for index in indices {
                print_expression(compilation, body, index, depth + 1);
            }
        }
        BoundExpressionKind::ArrayLength { array } => {
            println!("{pad}ArrayLength : {ty}");
            print_expression(compilation, body, array, depth + 1);
        }
        BoundExpressionKind::IndexerAccess {
            receiver,
            indexer,
            arguments,
        } => {
            println!("{pad}Indexer {} : {ty}", name(*indexer));
            print_expression(compilation, body, receiver, depth + 1);
            for argument in arguments {
                print_expression(compilation, body, argument, depth + 1);
            }
        }
        BoundExpressionKind::Binary {
            operator,
            left,
            right,
        } => {
            println!("{pad}Binary {operator:?} : {ty}");
            print_expression(compilation, body, left, depth + 1);
            print_expression(compilation, body, right, depth + 1);
        }
        BoundExpressionKind::Unary { operator, operand } => {
            println!("{pad}Unary {operator:?} : {ty}");
            print_expression(compilation, body, operand, depth + 1);
        }
        BoundExpressionKind::Conditional {
            condition,
            consequence,
            alternative,
        } => {
            println!("{pad}Conditional : {ty}");
            print_expression(compilation, body, condition, depth + 1);
            print_expression(compilation, body, consequence, depth + 1);
            print_expression(compilation, body, alternative, depth + 1);
        }
        BoundExpressionKind::Assignment { target, value } => {
            println!("{pad}Assign : {ty}");
            print_expression(compilation, body, target, depth + 1);
            print_expression(compilation, body, value, depth + 1);
        }
        BoundExpressionKind::CompoundAssignment {
            target,
            operator,
            value,
        } => {
            println!("{pad}CompoundAssign {operator:?} : {ty}");
            print_expression(compilation, body, target, depth + 1);
            print_expression(compilation, body, value, depth + 1);
        }
        BoundExpressionKind::Increment {
            target,
            operator,
            prefix,
            ..
        } => {
            println!("{pad}Increment {operator:?} prefix={prefix} : {ty}");
            print_expression(compilation, body, target, depth + 1);
        }
        BoundExpressionKind::Conversion {
            operand,
            conversion,
            ..
        } => {
            println!("{pad}Conversion {conversion:?} : {ty}");
            print_expression(compilation, body, operand, depth + 1);
        }
        BoundExpressionKind::InterpolatedString(parts) => {
            println!("{pad}Interpolated : {ty}");
            for part in parts {
                print_expression(compilation, body, part, depth + 1);
            }
        }
        BoundExpressionKind::StringInsert {
            value,
            alignment,
            format,
        } => {
            let clauses = rustlyn_semantics::composite_clauses(*alignment, format.as_deref());
            println!("{pad}Insert {clauses} : {ty}");
            print_expression(compilation, body, value, depth + 1);
        }
        BoundExpressionKind::IsPattern { operand, pattern } => {
            print!("{pad}IsPattern ");
            print_pattern(compilation, body, pattern);
            println!(" : {ty}");
            print_expression(compilation, body, operand, depth + 1);
        }
        BoundExpressionKind::Switch { governing, arms } => {
            println!("{pad}Switch : {ty}");
            print_expression(compilation, body, governing, depth + 1);
            for arm in arms {
                print!("{pad}  Arm ");
                print_pattern(compilation, body, &arm.pattern);
                println!();
                if let Some(when) = &arm.when {
                    print_expression(compilation, body, when, depth + 2);
                }
                print_expression(compilation, body, &arm.value, depth + 2);
            }
        }
        BoundExpressionKind::TypeTest { operand, target } => {
            println!(
                "{pad}TypeTest {} : {ty}",
                target.display(compilation.symbols())
            );
            print_expression(compilation, body, operand, depth + 1);
        }
        BoundExpressionKind::TryCast { operand, target } => {
            println!(
                "{pad}TryCast {} : {ty}",
                target.display(compilation.symbols())
            );
            print_expression(compilation, body, operand, depth + 1);
        }
        // A deconstruction is one of these, its steps in the order they run.
        BoundExpressionKind::Sequence(steps) => {
            println!("{pad}Sequence : {ty}");
            for step in steps {
                print_expression(compilation, body, step, depth + 1);
            }
        }
        BoundExpressionKind::TupleCreation(elements) => {
            println!("{pad}Tuple : {ty}");
            for element in elements {
                print_expression(compilation, body, element, depth + 1);
            }
        }
        BoundExpressionKind::RefArgument { kind, operand } => {
            println!("{pad}{kind:?} : {ty}");
            print_expression(compilation, body, operand, depth + 1);
        }
        BoundExpressionKind::Default(_) => println!("{pad}Default : {ty}"),
        other => println!("{pad}{other:?} : {ty}"),
    }
}

/// A pattern, on one line: they nest but never go deep.
fn print_pattern(compilation: &Compilation, body: &BoundBody, pattern: &BoundPattern) {
    let symbols = compilation.symbols();
    match &pattern.kind {
        BoundPatternKind::Discard => print!("_"),
        BoundPatternKind::Var { local } => {
            print!("var {}", body.locals[local.0 as usize].name);
        }
        BoundPatternKind::VarDeconstruct { local, .. } => {
            print!("var (..) into {}", body.locals[local.0 as usize].name);
        }
        BoundPatternKind::Type(ty) => print!("{}", ty.display(symbols)),
        BoundPatternKind::Declaration { ty, local } => {
            print!("{}", ty.display(symbols));
            if let Some(local) = local {
                print!(" {}", body.locals[local.0 as usize].name);
            }
        }
        BoundPatternKind::Constant(value) => match value.constant() {
            Some(constant) => print!("{constant:?}"),
            None => print!("<constant>"),
        },
        BoundPatternKind::Relational { operator, .. } => print!("{operator:?} _"),
        BoundPatternKind::SpanString { .. } => print!("<span == string>"),
        BoundPatternKind::List(list) => {
            print!("[");
            for (at, element) in list.before.iter().enumerate() {
                if at > 0 {
                    print!(", ");
                }
                print_pattern(compilation, body, element);
            }
            if list.slice {
                print!("{}..", if list.before.is_empty() { "" } else { ", " });
                if let Some(slice) = &list.slice_pattern {
                    print_pattern(compilation, body, &slice.pattern);
                }
            }
            for element in &list.after {
                print!(", ");
                print_pattern(compilation, body, element);
            }
            print!("]");
        }
        BoundPatternKind::And(left, right) => {
            print_pattern(compilation, body, left);
            print!(" and ");
            print_pattern(compilation, body, right);
        }
        BoundPatternKind::Or(left, right) => {
            print_pattern(compilation, body, left);
            print!(" or ");
            print_pattern(compilation, body, right);
        }
        BoundPatternKind::Not(inner) => {
            print!("not ");
            print_pattern(compilation, body, inner);
        }
        BoundPatternKind::UnionCase { ty, inner, .. } => {
            print!("TryGetValue(out {}) and ", ty.display(symbols));
            print_pattern(compilation, body, inner);
        }
        BoundPatternKind::Recursive(recursive) => {
            if let Some(ty) = &recursive.ty {
                print!("{}", ty.display(symbols));
            }
            if !recursive.positional.is_empty() {
                print!("(");
                for (at, inner) in recursive.positional.iter().enumerate() {
                    if at > 0 {
                        print!(", ");
                    }
                    print_pattern(compilation, body, inner);
                }
                print!(")");
            }
            if !recursive.properties.is_empty() {
                print!(" {{ ");
                for (at, (member, inner)) in recursive.properties.iter().enumerate() {
                    if at > 0 {
                        print!(", ");
                    }
                    print!("{}: ", symbols.get(*member).name);
                    print_pattern(compilation, body, inner);
                }
                print!(" }}");
            }
            if let Some(local) = recursive.local {
                print!(" {}", body.locals[local.0 as usize].name);
            }
        }
        BoundPatternKind::Unsupported(kind) => print!("<{kind:?}>"),
    }
}
