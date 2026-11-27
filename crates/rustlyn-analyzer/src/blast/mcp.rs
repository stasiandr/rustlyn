//! `rustlyn-blast --mcp`: a Model Context Protocol server on stdin/stdout,
//! so that an agent asks for the blast radius of its own change before
//! handing it over. JSON-RPC 2.0, one message per line. A compiler session
//! per project lives between calls: a second question about the same
//! project does not compile it from scratch.
//!
//! A [`Host`] adds what it knows: its own steps and arguments, its wording.

use std::collections::HashMap;
use std::io::{BufRead, Write};

use rustlyn_ide::Session;
use rustlyn_ide::formats::json::{Format, Json, object};

use super::compiler_risks::CompilerRisks;
use super::report::{English, Report, Request, Wording, analyze, json_text};
use super::walk::Limits;
use super::{BlastStep, Extensions, project, setup};

/// The tool's name.
pub const TOOL: &str = "blast_radius";

/// What a host adds to the server.
pub trait Host {
    /// The server's name, for `initialize`.
    fn name(&self) -> &str {
        "rustlyn-blast"
    }

    /// The cache folder's tool name: see [`setup::cache_dir`].
    fn cache_tool(&self) -> &str {
        "rustlyn-blast"
    }

    /// Extra tool arguments: (name, JSON type, description).
    fn arguments(&self) -> Vec<(&'static str, &'static str, &'static str)> {
        Vec::new()
    }

    /// The values `format` may have; a host that renders the report in
    /// other ways names them here.
    fn formats(&self) -> Vec<&'static str> {
        vec!["json", "text"]
    }

    /// The host's steps for one call.
    fn steps(&self, _root: &str, _arguments: &Json) -> Vec<Box<dyn BlastStep>> {
        Vec::new()
    }

    /// The report as the tool's answer: JSON, or the tree with
    /// `"format": "text"`.
    fn render(&self, report: &Report, arguments: &Json) -> String {
        let wording: &dyn Wording = &English;
        if arguments.str("format") == Some("text") {
            report.text_with(wording)
        } else {
            json_text(&report.json_with(wording))
        }
    }
}

/// No host: Rustlyn alone.
#[derive(Debug, Clone, Copy, Default)]
pub struct Plain;

impl Host for Plain {}

/// What the server keeps between calls.
pub struct Server {
    sessions: HashMap<String, Session>,
    host: Box<dyn Host>,
}

impl std::fmt::Debug for Server {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Server")
            .field("sessions", &self.sessions.keys().collect::<Vec<_>>())
            .field("host", &self.host.name())
            .finish()
    }
}

impl Default for Server {
    fn default() -> Self {
        Self::new(Box::new(Plain))
    }
}

impl Server {
    #[must_use]
    pub fn new(host: Box<dyn Host>) -> Self {
        Self {
            sessions: HashMap::new(),
            host,
        }
    }

    /// Reads requests until the input ends.
    pub fn serve(&mut self, input: impl BufRead, mut output: impl Write) {
        for line in input.lines() {
            let Ok(line) = line else {
                break;
            };
            if line.trim().is_empty() {
                continue;
            }
            if let Some(reply) = self.handle(&line) {
                let _ = writeln!(output, "{}", reply.to_text_with(Format::COMPACT));
                let _ = output.flush();
            }
        }
    }

    /// The answer to one message; none to a notification. A batch (a JSON
    /// array of messages) is answered with an array of the answers to those
    /// that have one, and not at all when none has (JSON-RPC 2.0, §6).
    pub fn handle(&mut self, line: &str) -> Option<Json> {
        let Some(message) = Json::parse(line.as_bytes()) else {
            return Some(error(Json::Null, -32700, "not JSON"));
        };
        let Json::Array(batch) = message else {
            return self.handle_message(&message);
        };
        if batch.is_empty() {
            return Some(error(Json::Null, -32600, "an empty batch"));
        }
        let replies: Vec<Json> = batch
            .iter()
            .filter_map(|message| self.handle_message(message))
            .collect();
        (!replies.is_empty()).then_some(Json::Array(replies))
    }

    /// The answer to one request or notification.
    fn handle_message(&mut self, message: &Json) -> Option<Json> {
        if !matches!(message, Json::Object(_)) {
            return Some(error(Json::Null, -32600, "not a request"));
        }
        let id = message.get("id").cloned();
        let method = message.str("method").unwrap_or_default().to_owned();
        let params = message.object_or_empty("params");
        let id = id?;
        let result = match method.as_str() {
            "initialize" => Ok(object(vec![
                (
                    "protocolVersion",
                    Json::String(
                        params
                            .str("protocolVersion")
                            .unwrap_or("2025-06-18")
                            .to_owned(),
                    ),
                ),
                ("capabilities", object(vec![("tools", object(vec![]))])),
                (
                    "serverInfo",
                    object(vec![
                        ("name", Json::String(self.host.name().to_owned())),
                        ("version", Json::String(env!("CARGO_PKG_VERSION").into())),
                    ]),
                ),
                (
                    "instructions",
                    Json::String(
                        "Blast radius for C# and Unity projects: call blast_radius with the project root before finishing an edit \
                         to see which methods, scenes and prefabs the change affects and which of them are risky."
                            .into(),
                    ),
                ),
            ])),
            "ping" => Ok(object(vec![])),
            "tools/list" => Ok(object(vec![("tools", Json::Array(vec![self.tool()]))])),
            "tools/call" => self.call(&params),
            _ => Err((-32601, format!("no method {method}"))),
        };
        Some(match result {
            Ok(result) => object(vec![
                ("jsonrpc", Json::String("2.0".into())),
                ("id", id),
                ("result", result),
            ]),
            Err((code, text)) => error(id, code, &text),
        })
    }

    fn call(&mut self, params: &Json) -> Result<Json, (i64, String)> {
        if params.str("name") != Some(TOOL) {
            return Err((
                -32602,
                format!("no tool {}", params.str("name").unwrap_or_default()),
            ));
        }
        let arguments = params.object_or_empty("arguments");
        Ok(match self.blast(&arguments) {
            Ok(text) => object(vec![("content", Json::Array(vec![text_content(text)]))]),
            Err(text) => object(vec![
                ("content", Json::Array(vec![text_content(text)])),
                ("isError", Json::Bool(true)),
            ]),
        })
    }

    /// An argument of a type the tool does not take, or a `format` it does
    /// not know, is refused: a call that asks for something else than it
    /// gets is not answered as if it had asked for the default.
    fn check(&self, arguments: &Json) -> Result<(), String> {
        let mut known: Vec<(&str, &str)> = vec![
            ("root", "string"),
            ("diff", "string"),
            ("base", "string"),
            ("staged", "boolean"),
            ("depth", "integer"),
            ("format", "string"),
        ];
        known.extend(self.host.arguments().into_iter().map(|(n, k, _)| (n, k)));
        for (name, kind) in known {
            let Some(value) = arguments.get(name) else {
                continue;
            };
            let fits = match kind {
                "string" => matches!(value, Json::String(_)),
                "boolean" => matches!(value, Json::Bool(_)),
                "integer" => value.as_int().is_some(),
                "number" => matches!(value, Json::Int(_) | Json::Float(_)),
                _ => true,
            };
            if !fits && !matches!(value, Json::Null) {
                let article = if kind.starts_with('i') { "an" } else { "a" };
                return Err(format!("{name} must be {article} {kind}"));
            }
        }
        if let Some(format) = arguments.str("format") {
            let formats = self.host.formats();
            if !formats.contains(&format) {
                return Err(format!(
                    "format must be {}, not {format:?}",
                    formats.join(" or ")
                ));
            }
        }
        Ok(())
    }

    fn blast(&mut self, arguments: &Json) -> Result<String, String> {
        self.check(arguments)?;
        let root = arguments
            .str("root")
            .ok_or("root is required: the project root")?;
        let root = setup::canonical_root(root);
        setup::existing_root(&root)?;
        let (patch, notes) = match arguments.str("diff") {
            Some(diff) => {
                setup::valid_patch(diff)?;
                (diff.to_owned(), Vec::new())
            }
            None => setup::git_patch_noted(
                &root,
                arguments.str("base"),
                arguments.bool("staged").unwrap_or(false),
            )?,
        };
        let mut limits = Limits::default();
        if let Some(depth) = arguments.int("depth") {
            limits.depth = depth.clamp(0, 20) as usize;
        }
        let mut request = Request::new(root.clone(), patch);
        request.limits = limits;
        request.notes = notes;
        let session = match self.sessions.remove(&root) {
            Some(session) => project::recompile(&root, session)?,
            None => project::compiled(&root, setup::cache_dir(self.host.cache_tool(), &root))?,
        };
        let steps = self.host.steps(&root, arguments);
        let model = CompilerRisks::new(&root, &session);
        let extensions = Extensions {
            steps: steps.iter().map(AsRef::as_ref).collect(),
            risks: vec![&model],
        };
        let report = analyze(&request, &session, &extensions);
        let text = self.host.render(&report, arguments);
        drop(extensions);
        drop(model);
        self.sessions.insert(root, session);
        Ok(text)
    }

    fn tool(&self) -> Json {
        let property = |kind: &str, text: &str| {
            object(vec![
                ("type", Json::String(kind.into())),
                ("description", Json::String(text.into())),
            ])
        };
        let mut properties = vec![
            (
                "root",
                property(
                    "string",
                    "Absolute path of the project root (the folder with Assets/ or the .sln).",
                ),
            ),
            (
                "diff",
                property(
                    "string",
                    "Unified diff to analyze, paths relative to root. Omit to use git.",
                ),
            ),
            (
                "base",
                property(
                    "string",
                    "Git revision to compare the working copy with. Default HEAD.",
                ),
            ),
            ("staged", property("boolean", "Only staged changes.")),
            (
                "depth",
                property(
                    "integer",
                    "How many steps to follow from the change. Default 4.",
                ),
            ),
            ("format", property("string", "json (default) or text.")),
        ];
        for (name, kind, text) in self.host.arguments() {
            properties.push((name, property(kind, text)));
        }
        object(vec![
            ("name", Json::String(TOOL.into())),
            (
                "description",
                Json::String(
                    "What a code change affects in a C#/Unity project: changed members, callers and readers up the chain, \
                     scenes and prefabs using the scripts, and risks (per-frame code, removed members still used, serialized \
                     fields set in assets, compile errors, failures and races the change adds). Without `diff` it takes the \
                     working copy against `base` (HEAD) from git, new untracked .cs files included."
                        .into(),
                ),
            ),
            (
                "inputSchema",
                object(vec![
                    ("type", Json::String("object".into())),
                    ("properties", object(properties)),
                    ("required", Json::Array(vec![Json::String("root".into())])),
                ]),
            ),
        ])
    }
}

fn text_content(text: String) -> Json {
    object(vec![
        ("type", Json::String("text".into())),
        ("text", Json::String(text)),
    ])
}

fn error(id: Json, code: i64, text: &str) -> Json {
    object(vec![
        ("jsonrpc", Json::String("2.0".into())),
        ("id", id),
        (
            "error",
            object(vec![
                ("code", Json::Int(code)),
                ("message", Json::String(text.into())),
            ]),
        ),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::testing::{Project, patch};

    #[test]
    fn the_tool_over_the_protocol() {
        let mut server = Server::default();
        let init = server
            .handle(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18"}}"#)
            .expect("reply");
        assert_eq!(
            init.object("result")
                .and_then(|r| r.object("serverInfo"))
                .and_then(|s| s.str("name")),
            Some("rustlyn-blast")
        );
        assert!(
            server
                .handle(r#"{"jsonrpc":"2.0","method":"notifications/initialized"}"#)
                .is_none(),
            "a notification gets no reply"
        );
        let list = server
            .handle(r#"{"jsonrpc":"2.0","id":2,"method":"tools/list"}"#)
            .expect("reply");
        assert_eq!(
            list.object("result")
                .and_then(|r| r.objects("tools"))
                .map(|t| t[0].str("name").map(str::to_owned)),
            Some(Some(TOOL.to_owned()))
        );

        let old = "class A {\n    public void F() { }\n    void G() { F(); }\n}\n";
        let new = "class A {\n    public void F() { int x = 1; }\n    void G() { F(); }\n}\n";
        let project = Project::new("mcp", &[("A.cs", new)]);
        let call = object(vec![
            ("jsonrpc", Json::String("2.0".into())),
            ("id", Json::Int(3)),
            ("method", Json::String("tools/call".into())),
            (
                "params",
                object(vec![
                    ("name", Json::String(TOOL.into())),
                    (
                        "arguments",
                        object(vec![
                            ("root", Json::String(project.root())),
                            ("diff", Json::String(patch("A.cs", old, new))),
                        ]),
                    ),
                ]),
            ),
        ]);
        let reply = server.handle(&call.to_text()).expect("reply");
        let result = reply.object("result").expect("result");
        assert!(result.bool("isError").is_none(), "{}", reply.to_text());
        let text = result.objects("content").expect("content")[0]
            .str("text")
            .expect("text")
            .to_owned();
        let report = Json::parse(text.as_bytes()).expect("report JSON");
        let keys: Vec<&str> = report
            .objects("nodes")
            .expect("nodes")
            .iter()
            .filter_map(|n| n.str("key"))
            .collect();
        assert_eq!(keys, vec!["A.F()", "A.G()"]);
        // The second call is on the same session.
        assert!(server.handle(&call.to_text()).is_some());
    }

    /// A batch (an array of requests) is answered with an array of the
    /// answers to those that have one; one of notifications only is not
    /// answered, an empty one is a request that is not valid.
    #[test]
    fn a_batch_is_answered_with_an_array() {
        let mut server = Server::default();
        let batch = r#"[
            {"jsonrpc":"2.0","id":1,"method":"ping"},
            {"jsonrpc":"2.0","method":"notifications/initialized"},
            {"jsonrpc":"2.0","id":"two","method":"tools/list"},
            7
        ]"#;
        let reply = server.handle(batch).expect("an answer");
        let Json::Array(replies) = &reply else {
            panic!("an array: {}", reply.to_text());
        };
        assert_eq!(replies.len(), 3, "{}", reply.to_text());
        assert_eq!(replies[0].int("id"), Some(1));
        assert_eq!(replies[1].str("id"), Some("two"));
        assert!(replies[1].object("result").is_some());
        assert_eq!(
            replies[2].object("error").and_then(|e| e.int("code")),
            Some(-32600),
            "an element that is not a request is invalid"
        );
        assert!(
            server
                .handle(r#"[{"jsonrpc":"2.0","method":"notifications/initialized"}]"#)
                .is_none()
        );
        let empty = server.handle("[]").expect("an answer");
        assert_eq!(
            empty.object("error").and_then(|e| e.int("code")),
            Some(-32600)
        );
    }

    /// A root that is not there and a diff that is not a diff are errors,
    /// not a project with no changes.
    #[test]
    fn bad_input_is_an_error_result() {
        let mut server = Server::default();
        let project = Project::new("bad", &[("A.cs", "class A { }\n")]);
        let ask = |server: &mut Server, root: &str, diff: &str| {
            let call = object(vec![
                ("jsonrpc", Json::String("2.0".into())),
                ("id", Json::Int(1)),
                ("method", Json::String("tools/call".into())),
                (
                    "params",
                    object(vec![
                        ("name", Json::String(TOOL.into())),
                        (
                            "arguments",
                            object(vec![
                                ("root", Json::String(root.into())),
                                ("diff", Json::String(diff.into())),
                            ]),
                        ),
                    ]),
                ),
            ]);
            let reply = server.handle(&call.to_text()).expect("reply");
            let result = reply.object("result").expect("result");
            (
                result.bool("isError") == Some(true),
                result.objects("content").expect("content")[0]
                    .str("text")
                    .expect("text")
                    .to_owned(),
            )
        };
        let (failed, text) = ask(&mut server, "/nowhere/at/all", "");
        assert!(failed, "{text}");
        assert!(text.contains("not a folder"), "{text}");
        let (failed, text) = ask(&mut server, &project.root(), "this is not a diff\n");
        assert!(failed, "{text}");
        assert!(text.contains("not a unified diff"), "{text}");
    }

    fn call_with(server: &mut Server, arguments: Json) -> Json {
        let call = object(vec![
            ("jsonrpc", Json::String("2.0".into())),
            ("id", Json::Int(9)),
            ("method", Json::String("tools/call".into())),
            (
                "params",
                object(vec![
                    ("name", Json::String(TOOL.into())),
                    ("arguments", arguments),
                ]),
            ),
        ]);
        server.handle(&call.to_text()).expect("reply")
    }

    /// An argument of the wrong type, or a `format` the tool does not have,
    /// is an error result that names it: not a call with the default.
    #[test]
    fn a_wrong_argument_is_an_error_naming_it() {
        let mut server = Server::default();
        let project = Project::new("mcp-args", &[("A.cs", "class A { }\n")]);
        let mut bad = |extra: (&str, Json)| {
            let reply = call_with(
                &mut server,
                object(vec![("root", Json::String(project.root())), extra]),
            );
            let result = reply.object("result").expect("result").clone();
            let text = result.objects("content").expect("content")[0]
                .str("text")
                .expect("text")
                .to_owned();
            (result.bool("isError"), text)
        };
        for (extra, name) in [
            (("depth", Json::String("x".into())), "depth"),
            (("depth", Json::Bool(true)), "depth"),
            (("depth", Json::Float(1.5)), "depth"),
            (("format", Json::String("xml".into())), "format"),
            (("format", Json::Int(3)), "format"),
            (("staged", Json::String("yes".into())), "staged"),
            (("base", Json::Int(1)), "base"),
            (("diff", Json::Bool(false)), "diff"),
        ] {
            let (is_error, text) = bad(extra);
            assert_eq!(is_error, Some(true), "{name}: {text}");
            assert!(text.starts_with(name), "{name}: {text}");
        }
        // What is right is not refused: the tool's own types, and `null`.
        let diff = patch("A.cs", "class A { }\n", "class A { int x; }\n");
        project.write("A.cs", "class A { int x; }\n");
        for extra in [
            ("format", Json::String("text".into())),
            ("format", Json::String("json".into())),
            ("depth", Json::Int(2)),
            ("depth", Json::Null),
            ("staged", Json::Bool(false)),
        ] {
            let reply = call_with(
                &mut server,
                object(vec![
                    ("root", Json::String(project.root())),
                    ("diff", Json::String(diff.clone())),
                    extra,
                ]),
            );
            let result = reply.object("result").expect("result");
            assert!(result.bool("isError").is_none(), "{}", reply.to_text());
        }
    }
}
