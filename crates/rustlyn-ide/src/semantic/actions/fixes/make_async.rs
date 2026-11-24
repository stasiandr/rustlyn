//! Make method async: `await` in a method that is not `async`.
//!
//! The binder does not report this yet (Roslyn's CS4032 for a method with a
//! return type, CS4033 for a `void` one, CS4034 for a lambda), so the
//! provider sees it for itself: the cursor in an `await` whose nearest
//! enclosing method, local function or lambda has no `async`.
//!
//! As in Roslyn, `async` goes in front of the return type, which becomes a
//! task: `void` a `Task` — or stays `void`, the second choice, for an event
//! handler — and `T` a `Task<T>`; one that is a task already is kept. A
//! method whose return type changes and whose name does not end in `Async`
//! is renamed to, everywhere it is used, except `Main`. `Task` is written
//! as the `using`s allow, and `using System.Threading.Tasks;` added where
//! it is not imported.

use rustlyn_semantics::Type;
use rustlyn_syntax::SyntaxKind;

use super::super::{ActionKind, CodeAction, Context};
use super::support::{Namer, add_using};
use crate::edit::{TextEdit, WorkspaceEdit};

const TASKS: &str = "System.Threading.Tasks";

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.view.root.find_token(context.span.start()) else {
        return;
    };
    let Some(awaiting) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .take_while(|node| !is_function(node.kind()))
        .find(|node| node.kind() == SyntaxKind::AwaitExpression)
    else {
        return;
    };
    let Some(function) = awaiting.ancestors().find(|node| is_function(node.kind())) else {
        return;
    };
    if function
        .child_token_of_kind(SyntaxKind::AsyncKeyword)
        .is_some()
    {
        return;
    }
    if matches!(
        function.kind(),
        SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
    ) {
        let Some(first) = function.first_token() else {
            return;
        };
        found.push(context.local(
            "Make lambda expression async",
            ActionKind::QuickFix,
            Some("CS4034"),
            vec![TextEdit::insert(first.span().start(), "async ")],
        ));
        return;
    }
    let Some(returns) = function
        .children()
        .find(|child| child.kind().is_type_node())
    else {
        return;
    };
    let ty = context.view.model.type_of_syntax(&returns);
    let view = &*context.view;
    let namer = Namer::at(view, &function);
    let symbols = view.compilation().symbols();
    let is_void = matches!(ty, Type::Void) || returns.text().trim() == "void";
    let task_like = ty.symbol().is_some_and(|symbol| {
        let name = symbols.qualified_name(symbol);
        matches!(
            name.as_str(),
            "System.Threading.Tasks.Task"
                | "System.Threading.Tasks.Task`1"
                | "System.Threading.Tasks.ValueTask"
                | "System.Threading.Tasks.ValueTask`1"
        )
    });
    let code = if is_void { "CS4033" } else { "CS4032" };
    let imports_tasks = namer.imports(TASKS);
    let written = returns.text().trim().to_string();
    let new_type = if task_like {
        written
    } else if is_void {
        "Task".to_string()
    } else {
        format!("Task<{written}>")
    };

    let name_token = function
        .child_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken);
    let mut edit = WorkspaceEdit::default();
    edit.add(
        context.path.clone(),
        TextEdit::new(returns.span(), format!("async {new_type}")),
    );
    if !task_like
        && !imports_tasks
        && let Some(using) = add_using(&view.root, &context.text, TASKS)
    {
        edit.add(context.path.clone(), using);
    }
    // Renamed to `NameAsync` wherever it is called.
    if !task_like
        && let Some(name_token) = &name_token
        && !name_token.value_text().ends_with("Async")
        && name_token.value_text() != "Main"
        && let Some((_, places)) = view.semantic.references(
            &context.path,
            name_token.span().start(),
            Some(&context.text),
        )
    {
        let renamed = format!("{}Async", name_token.value_text());
        for (path, span) in places {
            edit.add(path, TextEdit::new(span, renamed.clone()));
        }
        // The declaration itself, found or not.
        edit.add(
            context.path.clone(),
            TextEdit::new(name_token.span(), renamed.clone()),
        );
    }
    found.push(CodeAction {
        title: "Make method async".to_string(),
        kind: ActionKind::QuickFix,
        fixes: Some(code.to_string()),
        edit,
    });
    if is_void {
        found.push(context.local(
            "Make method async (stay void)",
            ActionKind::QuickFix,
            Some(code),
            vec![TextEdit::insert(returns.span().start(), "async ")],
        ));
    }
}

fn is_function(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::MethodDeclaration
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
    )
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, fix_file, titles};

    const TASKS: &str = "namespace System.Threading.Tasks\n{\n    public class Task { public static Task Delay(int ms) => null; public System.Runtime.CompilerServices.TaskAwaiter GetAwaiter() => default; }\n    public class Task<T> : Task { }\n}\nnamespace System.Runtime.CompilerServices\n{\n    public interface INotifyCompletion { void OnCompleted(System.Action a); }\n    public struct TaskAwaiter : INotifyCompletion { public bool IsCompleted => true; public void GetResult() { } public void OnCompleted(System.Action a) { } }\n}\n";

    #[test]
    fn a_void_method_becomes_an_async_task_and_is_renamed() {
        let source = "using System.Threading.Tasks;\n\nclass C\n{\n    void Load()\n    {\n        $$await Task.Delay(1);\n    }\n\n    void Run() => Load();\n}\n";
        assert_eq!(
            fix(&[source, TASKS], "Make method async"),
            "using System.Threading.Tasks;\n\nclass C\n{\n    async Task LoadAsync()\n    {\n        await Task.Delay(1);\n    }\n\n    void Run() => LoadAsync();\n}\n"
        );
        assert_eq!(
            fix(&[source, TASKS], "Make method async (stay void)"),
            "using System.Threading.Tasks;\n\nclass C\n{\n    async void Load()\n    {\n        await Task.Delay(1);\n    }\n\n    void Run() => Load();\n}\n"
        );
    }

    #[test]
    fn a_value_becomes_a_task_of_it_and_the_namespace_is_imported() {
        let source = "class C\n{\n    public static int Count()\n    {\n        await System.Threading.Tasks.Task.$$Delay(1);\n        return 1;\n    }\n}\n";
        assert_eq!(
            fix(&[source, TASKS], "Make method async"),
            "using System.Threading.Tasks;\n\nclass C\n{\n    public static async Task<int> CountAsync()\n    {\n        await System.Threading.Tasks.Task.Delay(1);\n        return 1;\n    }\n}\n"
        );
        assert!(!titles(&[source, TASKS]).contains(&"Make method async (stay void)".to_string()));
    }

    #[test]
    fn callers_in_other_files_follow_the_rename() {
        let source = "using System.Threading.Tasks;\n\npublic class C\n{\n    public void Save()\n    {\n        $$await Task.Delay(1);\n    }\n}\n";
        let caller = "class D\n{\n    void M(C c) => c.Save();\n}\n";
        assert_eq!(
            fix_file(&[source, TASKS, caller], "Make method async", "C.cs"),
            "class D\n{\n    void M(C c) => c.SaveAsync();\n}\n"
        );
    }

    #[test]
    fn an_async_method_or_lambda_is_left_alone() {
        let source = "using System.Threading.Tasks;\n\nclass C\n{\n    async Task Load()\n    {\n        $$await Task.Delay(1);\n    }\n}\n";
        assert!(
            !titles(&[source, TASKS])
                .iter()
                .any(|title| title.starts_with("Make"))
        );
        let lambda = "using System;\nusing System.Threading.Tasks;\n\nclass C\n{\n    void M()\n    {\n        Action a = () => { $$await Task.Delay(1); };\n    }\n}\n";
        assert_eq!(
            fix(&[lambda, TASKS], "Make lambda expression async"),
            "using System;\nusing System.Threading.Tasks;\n\nclass C\n{\n    void M()\n    {\n        Action a = async () => { await Task.Delay(1); };\n    }\n}\n"
        );
    }
}
