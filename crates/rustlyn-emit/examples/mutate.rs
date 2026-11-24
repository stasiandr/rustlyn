//! Makes one edit to a C# file of the kind a person makes while working on
//! a game: a log line, a number or a string changed, a method, field,
//! nested type or local function added and used, a condition turned round,
//! spacing and a comment, or a save in the middle of typing. For fuzzing
//! hot patches (`tools/unity/fuzz.py`).
//!
//! ```text
//! mutate <file> <seed> [kind] [--define "A;B"]
//! ```
//!
//! The edited text goes to standard output, and one line to standard error
//! says what was done: `kind<TAB>type<TAB>member<TAB>expect`, where `expect`
//! is `patch` (the edit changes code that runs), `maybe` (it may: what it
//! adds or takes away nothing may use), `spacing` (it changes
//! nothing that runs: the member is not to be in the patch) or `broken` (the
//! file does not compile). With no place for the kind in the file, it exits
//! with 2.

use rustlyn_syntax::{ParseOptions, SyntaxKind, SyntaxNode, parse_with};
use rustlyn_text::SourceText;

const KINDS: &[&str] = &[
    "log",
    "number",
    "string",
    "method",
    "instance-method",
    "field",
    "static-field",
    "nested",
    "nested-generic",
    "lambda",
    "local-function",
    "condition",
    "early-return",
    "property",
    "enum-member",
    "spacing",
    "broken",
    "coroutine",
    "async",
    "duplicate",
    "switch",
    "linq",
    "tuple",
    "try",
    "foreach",
    "pattern",
    "interpolation",
    "add-parameter",
    "remove-method",
    "lambda-body",
    "constructor",
];

struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// A member's body the edit goes into, and what it is in.
#[allow(dead_code)]
struct Body {
    block: SyntaxNode,
    member: SyntaxNode,
    owner: SyntaxNode,
    is_static: bool,
    in_struct: bool,
    readonly: bool,
    returns_void: bool,
    iterator: bool,
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let (Some(path), Some(seed)) = (
        arguments.first(),
        arguments.get(1).and_then(|seed| seed.parse::<u64>().ok()),
    ) else {
        eprintln!("usage: mutate <file> <seed> [kind] [--define A;B]");
        std::process::exit(1);
    };
    let define: Vec<String> = arguments
        .iter()
        .position(|argument| argument == "--define")
        .and_then(|at| arguments.get(at + 1))
        .map(|defines| defines.split(';').map(str::to_string).collect())
        .unwrap_or_default();
    let wanted = arguments
        .get(2)
        .filter(|kind| !kind.starts_with("--"))
        .cloned();
    let text = std::fs::read_to_string(path).unwrap_or_else(|error| {
        eprintln!("{path}: {error}");
        std::process::exit(1);
    });
    let tree = parse_with(
        SourceText::new(path.as_str(), text.clone()),
        &ParseOptions::with_symbols(define),
    );
    let mut random = Random(seed.wrapping_mul(2654435761).wrapping_add(17));
    random.next();
    let kind = wanted.unwrap_or_else(|| KINDS[random.below(KINDS.len())].to_string());
    let bodies = bodies(&tree.root());
    match edit(&text, &tree.root(), &bodies, &kind, seed, &mut random) {
        Some((edited, owner, member, expect)) => {
            print!("{edited}");
            eprintln!("{kind}\t{owner}\t{member}\t{expect}");
        }
        None => {
            eprintln!("{kind}\t-\t-\tnone");
            std::process::exit(2);
        }
    }
}

fn has_token(node: &SyntaxNode, kind: SyntaxKind) -> bool {
    node.child_tokens()
        .any(|token| token.kind() == kind || token.contextual_kind() == kind)
}

/// Whether a declaration has a modifier: its own tokens, or a list of them.
fn has_modifier(node: &SyntaxNode, kind: SyntaxKind) -> bool {
    has_token(node, kind)
        || node
            .children()
            .filter(|child| !matches!(child.kind(), SyntaxKind::Block | SyntaxKind::ParameterList))
            .take_while(|child| child.kind() != SyntaxKind::Block)
            .any(|child| {
                format!("{:?}", child.kind()).contains("Modifier") && has_token(&child, kind)
            })
}

fn type_name(owner: &SyntaxNode) -> String {
    let mut names: Vec<String> = owner
        .ancestors()
        .chain(std::iter::once(owner.clone()))
        .filter(|node| {
            matches!(
                node.kind(),
                SyntaxKind::ClassDeclaration | SyntaxKind::StructDeclaration
            )
        })
        .filter_map(|node| {
            node.child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.text().to_string())
        })
        .collect();
    // `ancestors` runs outward: the outermost type comes last.
    let own = names.pop();
    names.reverse();
    names.extend(own);
    names.dedup();
    names.join(".")
}

fn member_name(member: &SyntaxNode) -> String {
    let named = if matches!(
        member.kind(),
        SyntaxKind::GetAccessorDeclaration | SyntaxKind::SetAccessorDeclaration
    ) {
        member
            .ancestors()
            .find(|node| node.kind() == SyntaxKind::PropertyDeclaration)
    } else {
        Some(member.clone())
    };
    match member.kind() {
        SyntaxKind::ConstructorDeclaration => {
            if has_modifier(member, SyntaxKind::StaticKeyword) {
                ".cctor".into()
            } else {
                ".ctor".into()
            }
        }
        SyntaxKind::GetAccessorDeclaration | SyntaxKind::SetAccessorDeclaration => {
            let prefix = if member.kind() == SyntaxKind::GetAccessorDeclaration {
                "get_"
            } else {
                "set_"
            };
            let name = named
                .and_then(|property| property.child_token_of_kind(SyntaxKind::IdentifierToken))
                .map(|token| token.text().to_string())
                .unwrap_or_default();
            format!("{prefix}{name}")
        }
        _ => named
            .and_then(|node| node.child_token_of_kind(SyntaxKind::IdentifierToken))
            .map(|token| token.text().to_string())
            .unwrap_or_default(),
    }
}

fn bodies(root: &SyntaxNode) -> Vec<Body> {
    let mut found = Vec::new();
    for member in root.descendants() {
        if !matches!(
            member.kind(),
            SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::GetAccessorDeclaration
                | SyntaxKind::SetAccessorDeclaration
        ) {
            continue;
        }
        let Some(block) = member.child_of_kind(SyntaxKind::Block) else {
            continue;
        };
        // Inside a local function or a lambda is a body of its own, and an
        // interface's or a record's members are left alone.
        let Some(owner) = member.ancestors().find(|node| {
            matches!(
                node.kind(),
                SyntaxKind::ClassDeclaration
                    | SyntaxKind::StructDeclaration
                    | SyntaxKind::InterfaceDeclaration
                    | SyntaxKind::RecordDeclaration
            )
        }) else {
            continue;
        };
        if !matches!(
            owner.kind(),
            SyntaxKind::ClassDeclaration | SyntaxKind::StructDeclaration
        ) {
            continue;
        }
        let declaration = if matches!(
            member.kind(),
            SyntaxKind::GetAccessorDeclaration | SyntaxKind::SetAccessorDeclaration
        ) {
            member
                .ancestors()
                .find(|node| {
                    matches!(
                        node.kind(),
                        SyntaxKind::PropertyDeclaration | SyntaxKind::IndexerDeclaration
                    )
                })
                .unwrap_or_else(|| member.clone())
        } else {
            member.clone()
        };
        let is_static = has_modifier(&declaration, SyntaxKind::StaticKeyword);
        let in_struct = owner.kind() == SyntaxKind::StructDeclaration;
        let readonly = in_struct
            && (has_modifier(&owner, SyntaxKind::ReadOnlyKeyword)
                || has_modifier(&declaration, SyntaxKind::ReadOnlyKeyword)
                || member.kind() == SyntaxKind::GetAccessorDeclaration);
        let returns_void = match member.kind() {
            SyntaxKind::MethodDeclaration => member
                .children()
                .take_while(|child| child.kind() != SyntaxKind::ParameterList)
                .any(|child| child.text().trim() == "void"),
            SyntaxKind::ConstructorDeclaration | SyntaxKind::SetAccessorDeclaration => true,
            _ => false,
        };
        let iterator = block
            .descendant_tokens()
            .any(|token| token.text() == "yield");
        found.push(Body {
            block,
            member,
            owner,
            is_static,
            in_struct,
            readonly,
            returns_void,
            iterator,
        });
    }
    found
}

/// Where a statement goes at the start of a body: after its `{`.
fn after_brace(block: &SyntaxNode) -> usize {
    block
        .child_token_of_kind(SyntaxKind::OpenBraceToken)
        .map_or(block.span().start() as usize + 1, |token| {
            token.span().end() as usize
        })
}

fn splice(text: &str, at: usize, inserted: &str) -> String {
    format!("{}{}{}", &text[..at], inserted, &text[at..])
}

fn replace(text: &str, from: usize, to: usize, with: &str) -> String {
    format!("{}{}{}", &text[..from], with, &text[to..])
}

type Edit = (String, String, String, &'static str);

fn edit(
    text: &str,
    root: &SyntaxNode,
    bodies: &[Body],
    kind: &str,
    seed: u64,
    random: &mut Random,
) -> Option<Edit> {
    let pick = |random: &mut Random, keep: &dyn Fn(&Body) -> bool| -> Option<usize> {
        let fitting: Vec<usize> = (0..bodies.len())
            .filter(|&index| keep(&bodies[index]))
            .collect();
        (!fitting.is_empty()).then(|| fitting[random.below(fitting.len())])
    };
    let log = |what: &str| format!("\n            global::UnityEngine.Debug.Log({what});");
    let named = |body: &Body| (type_name(&body.owner), member_name(&body.member));
    let type_brace = |body: &Body| after_brace_of_type(&body.owner);
    match kind {
        "log" => {
            let body = &bodies[pick(random, &|_| true)?];
            let (owner, member) = named(body);
            Some((
                splice(
                    text,
                    after_brace(&body.block),
                    &log(&format!("\"fuzz {seed}\"")),
                ),
                owner,
                member,
                "patch",
            ))
        }
        // A line in a constructor: chained to its base's or another of its
        // own, as most of a game's are.
        "constructor" => {
            let body = &bodies[pick(random, &|body| {
                body.member.kind() == SyntaxKind::ConstructorDeclaration
            })?];
            let (owner, member) = named(body);
            Some((
                splice(
                    text,
                    after_brace(&body.block),
                    &log(&format!("\"fuzz {seed}\"")),
                ),
                owner,
                member,
                "patch",
            ))
        }
        "spacing" => {
            let body = &bodies[pick(random, &|_| true)?];
            let (owner, member) = named(body);
            Some((
                splice(
                    text,
                    after_brace(&body.block),
                    &format!("\n\n            // fuzz {seed}: a note   \n"),
                ),
                owner,
                member,
                "spacing",
            ))
        }
        "broken" => {
            let body = &bodies[pick(random, &|body| {
                body.block
                    .descendant_tokens()
                    .any(|token| token.kind() == SyntaxKind::SemicolonToken)
            })?];
            let (owner, member) = named(body);
            let semicolons: Vec<_> = body
                .block
                .descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::SemicolonToken && !token.is_missing())
                .collect();
            let token = &semicolons[random.below(semicolons.len())];
            Some((
                replace(
                    text,
                    token.span().start() as usize,
                    token.span().end() as usize,
                    "",
                ),
                owner,
                member,
                "broken",
            ))
        }
        "number" | "string" => {
            let excluded: Vec<(u32, u32)> = root
                .descendants()
                .filter(|node| {
                    matches!(
                        node.kind(),
                        SyntaxKind::CaseSwitchLabel
                            | SyntaxKind::CasePatternSwitchLabel
                            | SyntaxKind::AttributeList
                            | SyntaxKind::SwitchExpressionArm
                            | SyntaxKind::InterpolatedStringExpression
                    ) || format!("{:?}", node.kind()).contains("Pattern")
                        || (node.kind() == SyntaxKind::LocalDeclarationStatement
                            && has_token(node, SyntaxKind::ConstKeyword))
                })
                .map(|node| (node.span().start(), node.span().end()))
                .collect();
            let mut candidates = Vec::new();
            for (index, body) in bodies.iter().enumerate() {
                for token in body.block.descendant_tokens() {
                    let at = token.span().start();
                    if excluded.iter().any(|&(from, to)| from <= at && at < to) {
                        continue;
                    }
                    let fits = if kind == "number" {
                        token.kind() == SyntaxKind::NumericLiteralToken
                            && token.text().chars().all(|c| c.is_ascii_digit())
                            && token.text().parse::<u32>().is_ok_and(|value| value < 120)
                    } else {
                        token.kind() == SyntaxKind::StringLiteralToken
                            && token.text().starts_with('"')
                    };
                    if fits {
                        candidates.push((index, token));
                    }
                }
            }
            if candidates.is_empty() {
                return None;
            }
            let (index, token) = &candidates[random.below(candidates.len())];
            let (owner, member) = named(&bodies[*index]);
            let with = if kind == "number" {
                (token.text().parse::<u32>().ok()? + 1).to_string()
            } else {
                format!("{} fuzz\"", &token.text()[..token.text().len() - 1])
            };
            Some((
                replace(
                    text,
                    token.span().start() as usize,
                    token.span().end() as usize,
                    &with,
                ),
                owner,
                member,
                "patch",
            ))
        }
        "method" | "instance-method" => {
            let instance = kind == "instance-method";
            let body = &bodies[pick(random, &|body| !instance || !body.is_static)?];
            let (owner, member) = named(body);
            let name = format!("Fuzz{seed}");
            let added = if instance {
                format!(
                    "\n        private int {name}(int value) => value * 2 + GetHashCode() % 3;\n"
                )
            } else {
                format!(
                    "\n        private static int {name}(int value)\n        {{\n            return value * 2 + 1;\n        }}\n"
                )
            };
            let first = splice(text, after_brace(&body.block), &log(&format!("{name}(3)")));
            Some((
                splice(&first, type_brace(body), &added),
                owner,
                member,
                "patch",
            ))
        }
        "field" | "static-field" => {
            let instance = kind == "field";
            let body = &bodies[pick(random, &|body| {
                if instance {
                    !body.is_static && !body.in_struct && !is_static_type(&body.owner)
                } else {
                    true
                }
            })?];
            let (owner, member) = named(body);
            let name = format!("fuzzField{seed}");
            let added = if instance {
                format!("\n        private int {name} = 7;\n")
            } else {
                format!("\n        private static int {name} = 7;\n")
            };
            let first = splice(
                text,
                after_brace(&body.block),
                &format!("\n            {name}++;{}", log(&name)),
            );
            Some((
                splice(&first, type_brace(body), &added),
                owner,
                member,
                "patch",
            ))
        }
        "nested" | "nested-generic" => {
            let body = &bodies[pick(random, &|_| true)?];
            let (owner, member) = named(body);
            let (declared, used) = if kind == "nested" {
                (
                    format!(
                        "\n        private class FuzzBox{seed}\n        {{\n            public int Value = 5;\n        }}\n"
                    ),
                    format!("new FuzzBox{seed}().Value"),
                )
            } else {
                (
                    format!(
                        "\n        private class FuzzBox{seed}<T>\n        {{\n            public T Value;\n            public FuzzBox{seed}(T value) {{ Value = value; }}\n        }}\n"
                    ),
                    format!("new FuzzBox{seed}<int>(3).Value"),
                )
            };
            let first = splice(text, after_brace(&body.block), &log(&used));
            Some((
                splice(&first, type_brace(body), &declared),
                owner,
                member,
                "patch",
            ))
        }
        "lambda" => {
            let body = &bodies[pick(random, &|_| true)?];
            let (owner, member) = named(body);
            let inserted = format!(
                "\n            System.Func<int, int> fuzzF{seed} = v => v + 1;{}",
                log(&format!("fuzzF{seed}(1)"))
            );
            Some((
                splice(text, after_brace(&body.block), &inserted),
                owner,
                member,
                "patch",
            ))
        }
        "local-function" => {
            let body = &bodies[pick(random, &|_| true)?];
            let (owner, member) = named(body);
            let inserted = format!(
                "\n            static int FuzzLocal{seed}(int v) => v * 3;{}",
                log(&format!("FuzzLocal{seed}(2)"))
            );
            Some((
                splice(text, after_brace(&body.block), &inserted),
                owner,
                member,
                "patch",
            ))
        }
        "early-return" => {
            let body = &bodies[pick(random, &|body| {
                body.returns_void
                    && !body.iterator
                    && body.member.kind() != SyntaxKind::ConstructorDeclaration
            })?];
            let (owner, member) = named(body);
            let inserted = "\n            if (global::UnityEngine.Time.frameCount < 0) return;";
            Some((
                splice(text, after_brace(&body.block), inserted),
                owner,
                member,
                "patch",
            ))
        }
        "condition" => {
            let mut candidates = Vec::new();
            for (index, body) in bodies.iter().enumerate() {
                for statement in body
                    .block
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::IfStatement)
                {
                    // The condition: what is between the statement's parentheses.
                    let Some(condition) = statement.children().next() else {
                        continue;
                    };
                    let written = condition.text();
                    if written.contains(" is ")
                        || written.contains("out ")
                        || written.contains("is{")
                        || written.contains("is null")
                        || condition.span().is_empty()
                    {
                        continue;
                    }
                    candidates.push((index, condition));
                }
            }
            if candidates.is_empty() {
                return None;
            }
            let (index, condition) = &candidates[random.below(candidates.len())];
            let (owner, member) = named(&bodies[*index]);
            let span = condition.span();
            let with = format!("!({})", condition.text());
            Some((
                replace(text, span.start() as usize, span.end() as usize, &with),
                owner,
                member,
                "patch",
            ))
        }
        "property" => {
            let body = &bodies[pick(random, &|_| true)?];
            let (owner, member) = named(body);
            let added = format!("\n        private static int FuzzProperty{seed} => 4;\n");
            let first = splice(
                text,
                after_brace(&body.block),
                &log(&format!("FuzzProperty{seed}")),
            );
            Some((
                splice(&first, type_brace(body), &added),
                owner,
                member,
                "patch",
            ))
        }
        "enum-member" => {
            let enums: Vec<SyntaxNode> = root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::EnumDeclaration)
                .filter(|node| {
                    node.descendants()
                        .any(|child| child.kind() == SyntaxKind::EnumMemberDeclaration)
                })
                .collect();
            if enums.is_empty() {
                return None;
            }
            let declaration = &enums[random.below(enums.len())];
            let last = declaration
                .descendants()
                .filter(|child| child.kind() == SyntaxKind::EnumMemberDeclaration)
                .last()?;
            let name = declaration
                .child_token_of_kind(SyntaxKind::IdentifierToken)?
                .text()
                .to_string();
            let at = last.span().end() as usize;
            // After the last member, and its comma if it has one.
            let rest = &text[at..];
            let comma = rest.trim_start().starts_with(',');
            let at = if comma { at + rest.find(',')? + 1 } else { at };
            let inserted = if comma {
                format!("\n        Fuzz{seed},")
            } else {
                format!(",\n        Fuzz{seed}")
            };
            Some((
                splice(text, at, &inserted),
                name,
                format!("Fuzz{seed}"),
                "maybe",
            ))
        }
        "coroutine" | "async" => {
            let body = &bodies[pick(random, &|_| true)?];
            let (owner, member) = named(body);
            let (added, used) = if kind == "coroutine" {
                (
                    format!(
                        "\n        private static System.Collections.IEnumerator FuzzRoutine{seed}()\n        {{\n            yield return null;\n            global::UnityEngine.Debug.Log(\"routine {seed}\");\n        }}\n"
                    ),
                    format!(
                        "\n            {{ var fuzzR{seed} = FuzzRoutine{seed}(); fuzzR{seed}.MoveNext(); fuzzR{seed}.MoveNext(); }}"
                    ),
                )
            } else {
                (
                    format!(
                        "\n        private static async System.Threading.Tasks.Task<int> FuzzAsync{seed}(int v)\n        {{\n            await System.Threading.Tasks.Task.Yield();\n            return v + 1;\n        }}\n"
                    ),
                    format!("\n            _ = FuzzAsync{seed}(1);"),
                )
            };
            let first = splice(text, after_brace(&body.block), &used);
            Some((
                splice(&first, type_brace(body), &added),
                owner,
                member,
                "patch",
            ))
        }
        "switch" | "linq" | "tuple" | "try" | "foreach" | "pattern" | "interpolation" => {
            let body = &bodies[pick(random, &|_| true)?];
            let (owner, member) = named(body);
            let log1 = |what: &str| format!("global::UnityEngine.Debug.Log({what});");
            let inserted = match kind {
                "switch" => format!(
                    "\n            switch (global::UnityEngine.Time.frameCount % 3)\n            {{\n                case 0: {} break;\n                case 1: {} break;\n                default: break;\n            }}",
                    log1("\"zero\""),
                    log1(&format!("\"one {seed}\""))
                ),
                "linq" => format!(
                    "\n            {}",
                    log1("System.Linq.Enumerable.Sum(new[] { 1, 2, 3 }, v => v * 2)")
                ),
                "tuple" => format!(
                    "\n            var (fuzzA{seed}, fuzzB{seed}) = (1, \"x\");\n            {}",
                    log1(&format!("fuzzA{seed} + fuzzB{seed}"))
                ),
                "try" => format!(
                    "\n            try {{ {} }} catch (System.Exception fuzzE{seed}) {{ {} }} finally {{ {} }}",
                    log1("\"try\""),
                    log1(&format!("fuzzE{seed}.Message")),
                    log1("\"finally\"")
                ),
                "foreach" => format!(
                    "\n            foreach (var fuzzV{seed} in new[] {{ 1, 2 }}) {}",
                    log1(&format!("fuzzV{seed}"))
                ),
                "pattern" => format!(
                    "\n            object fuzzO{seed} = {seed};\n            if (fuzzO{seed} is int fuzzI{seed} && fuzzI{seed} > 0) {}",
                    log1(&format!("fuzzI{seed}"))
                ),
                _ => format!(
                    "\n            {}",
                    log1(&format!(
                        "$\"fuzz {seed} {{global::UnityEngine.Time.frameCount}}\""
                    ))
                ),
            };
            Some((
                splice(text, after_brace(&body.block), &inserted),
                owner,
                member,
                "patch",
            ))
        }
        "duplicate" | "add-parameter" | "remove-method" => {
            let methods: Vec<&Body> = bodies
                .iter()
                .filter(|body| body.member.kind() == SyntaxKind::MethodDeclaration)
                .filter(|body| {
                    let member = &body.member;
                    ![
                        SyntaxKind::OverrideKeyword,
                        SyntaxKind::AbstractKeyword,
                        SyntaxKind::ExternKeyword,
                        SyntaxKind::PartialKeyword,
                    ]
                    .iter()
                    .any(|&keyword| has_modifier(member, keyword))
                        && member
                            .child_of_kind(SyntaxKind::ExplicitInterfaceSpecifier)
                            .is_none()
                })
                .filter(|body| {
                    kind == "duplicate"
                        || (!has_modifier(&body.owner, SyntaxKind::PartialKeyword)
                            && member_is_private(&body.member)
                            && body
                                .member
                                .child_of_kind(SyntaxKind::TypeParameterList)
                                .is_none())
                })
                .filter(|body| {
                    if kind != "remove-method" {
                        return true;
                    }
                    let name = member_name(&body.member);
                    root.descendant_tokens()
                        .filter(|token| token.text() == name)
                        .count()
                        == 1
                })
                .filter(|body| {
                    kind != "add-parameter"
                        || body
                            .member
                            .child_of_kind(SyntaxKind::ParameterList)
                            .is_some_and(|list| {
                                !list.text().contains("params ") && !list.text().contains("this ")
                            })
                })
                .collect();
            if methods.is_empty() {
                return None;
            }
            let body = methods[random.below(methods.len())];
            let (owner, member) = named(body);
            let node = &body.member;
            match kind {
                "duplicate" => {
                    let identifier = node.child_token_of_kind(SyntaxKind::IdentifierToken)?;
                    let start = node.span().start() as usize;
                    let whole = &text[start..node.span().end() as usize];
                    let at = identifier.span().start() as usize - start;
                    let copy = format!(
                        "{}{}FuzzCopy{seed}{}",
                        &whole[..at],
                        identifier.text(),
                        &whole[at + identifier.text().len()..]
                    );
                    Some((
                        splice(
                            text,
                            node.span().end() as usize,
                            &format!("\n\n        {copy}"),
                        ),
                        owner,
                        format!("{member}FuzzCopy{seed}"),
                        "maybe",
                    ))
                }
                "add-parameter" => {
                    let list = node.child_of_kind(SyntaxKind::ParameterList)?;
                    let close = list.span().end() as usize - 1;
                    let empty = list.children().next().is_none();
                    let inserted = if empty {
                        format!("int fuzzP{seed} = 0")
                    } else {
                        format!(", int fuzzP{seed} = 0")
                    };
                    Some((splice(text, close, &inserted), owner, member, "patch"))
                }
                _ => Some((
                    replace(
                        text,
                        node.span().start() as usize,
                        node.span().end() as usize,
                        "",
                    ),
                    owner,
                    member,
                    "maybe",
                )),
            }
        }
        "lambda-body" => {
            let mut candidates = Vec::new();
            for (index, body) in bodies.iter().enumerate() {
                for lambda in body.block.descendants().filter(|node| {
                    matches!(
                        node.kind(),
                        SyntaxKind::SimpleLambdaExpression
                            | SyntaxKind::ParenthesizedLambdaExpression
                            | SyntaxKind::AnonymousMethodExpression
                    )
                }) {
                    if let Some(block) = lambda.child_of_kind(SyntaxKind::Block) {
                        candidates.push((index, block));
                    }
                }
            }
            if candidates.is_empty() {
                return None;
            }
            let (index, block) = &candidates[random.below(candidates.len())];
            let (owner, member) = named(&bodies[*index]);
            Some((
                splice(
                    text,
                    after_brace(block),
                    &log(&format!("\"lambda {seed}\"")),
                ),
                owner,
                member,
                "patch",
            ))
        }
        _ => None,
    }
}

/// Private: said so, or saying nothing of who may call it.
fn member_is_private(member: &SyntaxNode) -> bool {
    has_modifier(member, SyntaxKind::PrivateKeyword)
        || ![
            SyntaxKind::PublicKeyword,
            SyntaxKind::ProtectedKeyword,
            SyntaxKind::InternalKeyword,
        ]
        .iter()
        .any(|&keyword| has_modifier(member, keyword))
}

fn is_static_type(owner: &SyntaxNode) -> bool {
    has_modifier(owner, SyntaxKind::StaticKeyword)
}

fn after_brace_of_type(owner: &SyntaxNode) -> usize {
    owner
        .child_token_of_kind(SyntaxKind::OpenBraceToken)
        .map_or(owner.span().start() as usize, |token| {
            token.span().end() as usize
        })
}
