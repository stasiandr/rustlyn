//! The code snippets Roslyn ships with, by their shortcuts: `cw` writes
//! `Console.WriteLine();`, `prop` a property, `for` a counted loop. Each is
//! offered only where what it writes can go — statements where a statement
//! starts, members in a type — with the cursor placed where the first
//! thing to fill in is.

use rustlyn_syntax::SyntaxKind as K;

use super::context::{Code, Site, is_type_declaration};
use super::{Completion, CompletionKind, indentation_at, newline_of};

/// A snippet: its shortcut, what it is, and its lines. `$` marks the
/// cursor; `{name}` is the enclosing type's name.
struct Snippet {
    shortcut: &'static str,
    title: &'static str,
    lines: &'static [&'static str],
}

const STATEMENTS: &[Snippet] = &[
    Snippet {
        shortcut: "cw",
        title: "Console.WriteLine",
        lines: &["Console.WriteLine($);"],
    },
    Snippet {
        shortcut: "if",
        title: "if statement",
        lines: &["if ($)", "{", "}"],
    },
    Snippet {
        shortcut: "for",
        title: "for loop",
        lines: &["for (int i = 0; i < $; i++)", "{", "}"],
    },
    Snippet {
        shortcut: "forr",
        title: "reverse for loop",
        lines: &["for (int i = $ - 1; i >= 0; i--)", "{", "}"],
    },
    Snippet {
        shortcut: "foreach",
        title: "foreach loop",
        lines: &["foreach (var item in $)", "{", "}"],
    },
    Snippet {
        shortcut: "while",
        title: "while loop",
        lines: &["while ($)", "{", "}"],
    },
    Snippet {
        shortcut: "do",
        title: "do...while loop",
        lines: &["do", "{", "    $", "} while (true);"],
    },
    Snippet {
        shortcut: "try",
        title: "try catch",
        lines: &[
            "try",
            "{",
            "    $",
            "}",
            "catch (Exception)",
            "{",
            "    throw;",
            "}",
        ],
    },
    Snippet {
        shortcut: "tryf",
        title: "try finally",
        lines: &["try", "{", "    $", "}", "finally", "{", "}"],
    },
    Snippet {
        shortcut: "lock",
        title: "lock statement",
        lines: &["lock ($)", "{", "}"],
    },
    Snippet {
        shortcut: "using",
        title: "using statement",
        lines: &["using ($)", "{", "}"],
    },
    Snippet {
        shortcut: "switch",
        title: "switch statement",
        lines: &["switch ($)", "{", "    default:", "        break;", "}"],
    },
];

const MEMBERS: &[Snippet] = &[
    Snippet {
        shortcut: "prop",
        title: "auto-implemented property",
        lines: &["public $int MyProperty { get; set; }"],
    },
    Snippet {
        shortcut: "propg",
        title: "auto-implemented property with a private setter",
        lines: &["public $int MyProperty { get; private set; }"],
    },
    Snippet {
        shortcut: "propfull",
        title: "property with a backing field",
        lines: &[
            "private int myVar;",
            "",
            "public int MyProperty",
            "{",
            "    get { return myVar; }",
            "    set { myVar = value; }",
            "}",
            "$",
        ],
    },
    Snippet {
        shortcut: "ctor",
        title: "constructor",
        lines: &["public {name}()", "{", "    $", "}"],
    },
    Snippet {
        shortcut: "svm",
        title: "static void Main",
        lines: &["static void Main(string[] args)", "{", "    $", "}"],
    },
    Snippet {
        shortcut: "sim",
        title: "static int Main",
        lines: &[
            "static int Main(string[] args)",
            "{",
            "    $",
            "    return 0;",
            "}",
        ],
    },
    Snippet {
        shortcut: "equals",
        title: "Equals and GetHashCode",
        lines: &[
            "public override bool Equals(object obj)",
            "{",
            "    $return base.Equals(obj);",
            "}",
            "",
            "public override int GetHashCode()",
            "{",
            "    return base.GetHashCode();",
            "}",
        ],
    },
];

const TYPES: &[Snippet] = &[
    Snippet {
        shortcut: "class",
        title: "class",
        lines: &["class $MyClass", "{", "}"],
    },
    Snippet {
        shortcut: "struct",
        title: "struct",
        lines: &["struct $MyStruct", "{", "}"],
    },
    Snippet {
        shortcut: "interface",
        title: "interface",
        lines: &["interface $IInterface", "{", "}"],
    },
    Snippet {
        shortcut: "enum",
        title: "enum",
        lines: &["enum $MyEnum", "{", "}"],
    },
    Snippet {
        shortcut: "record",
        title: "record",
        lines: &["record $MyRecord();"],
    },
];

pub(super) fn complete(code: &Code, text: &str, site: &Site, items: &mut Vec<Completion>) {
    if !code.modifiers.is_empty() {
        return;
    }
    let mut offered: Vec<&Snippet> = Vec::new();
    if code.statement {
        offered.extend(STATEMENTS);
    }
    let type_name = site.target.as_ref().and_then(|target| {
        target
            .parent()
            .ancestors()
            .chain(std::iter::once(target.parent().clone()))
            .find(|node| is_type_declaration(node.kind()))
            .and_then(|declaration| declaration.child_token_of_kind(K::IdentifierToken))
            .map(|name| name.text().to_string())
    });
    if code.member {
        offered.extend(
            MEMBERS
                .iter()
                .filter(|snippet| snippet.shortcut != "ctor" || type_name.is_some()),
        );
    }
    if code.member || code.type_declaration {
        offered.extend(TYPES);
    }
    if offered.is_empty() {
        return;
    }
    let indent = indentation_at(text, site.start);
    let newline = newline_of(text);
    for snippet in offered {
        let mut out = String::new();
        let mut caret = None;
        for (index, line) in snippet.lines.iter().enumerate() {
            if index > 0 {
                out.push_str(newline);
                if !line.is_empty() {
                    out.push_str(indent);
                }
            }
            let line = line.replace("{name}", type_name.as_deref().unwrap_or_default());
            match line.find('$') {
                Some(at) => {
                    out.push_str(&line[..at]);
                    caret = Some(out.len() as u32);
                    out.push_str(&line[at + 1..]);
                }
                None => out.push_str(&line),
            }
        }
        items.push(Completion {
            label: snippet.shortcut.to_string(),
            kind: CompletionKind::Snippet,
            detail: format!("{} (snippet)", snippet.title),
            rank: 31,
            insert_text: Some(out),
            is_snippet: true,
            caret,
            ..Completion::default()
        });
    }
}
