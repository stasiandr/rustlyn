//! What the value graph says, as data: notes on places, titles and
//! subtitles of nodes, why an expansion found nothing. [`Wording`] turns
//! them into text — English by default ([`English`]); a host words them in
//! its own language.

use super::graph::NodeKind;
use super::origin::Kind;
use super::text::last_component;

/// A note on a place or a node: how the value gets there, or why the graph
/// shows it so.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Note {
    /// `(x, y) = (1, 2)`.
    Deconstruction,
    /// `Inc(ref x)`: a method changes the value.
    ByRef,
    /// `list.Add(x)`, `map[k] = x`: put into a collection by this method.
    AddsTo(String),
    /// `x += 1`: the old value is part of the new one.
    Compound,
    /// `Read(out x)`: the call puts the value.
    OutArgument,
    /// The declaration of a constant.
    Constant,
    /// An initial value in the declaration.
    Initial,
    /// What a getter returns.
    GetterReturns,
    /// A parameter of a lambda.
    LambdaParameter,
    /// An element of a `foreach` loop.
    ForeachItem,
    /// A pattern variable: `x is T name`.
    PatternCheck,
    /// A parameter of this local function.
    LocalFunctionParameter(String),
    /// An ECS component is set or updated: `stash.Set(e)`.
    ComponentSet,
    /// An ECS component is added: `stash.Add(e)`.
    ComponentAdd,
    /// An ECS component is removed: `stash.Remove(e)`.
    ComponentRemove,
    /// What a method returns.
    Returns,
    /// Calls of a base member this one overrides or implements.
    ThroughBase(String),
    /// Raises this event.
    RaisesEvent(String),
    /// Calls this method.
    Calls(String),
    /// A parameter's default value; this many calls do not pass it.
    DefaultFor(usize),
    /// The same line of code is in this many more places (the first few
    /// titles).
    SameIn { count: usize, titles: String },
    /// Places that did not fit into the graph.
    DidNotFit,
    /// A source whose data lines were not found.
    NotFoundWhereSet,
    /// The code only sets a default; the data sets the value.
    OnlyDefault,
    /// The data sets the value, and the code changes it.
    AlsoChangedByCode,
    /// The name is the key of an element access.
    ElementKey,
    /// The name is an argument of this call.
    ArgumentOf(String),
    /// Through these locals: `dmg ← mult`.
    Through(Vec<String>),
    /// The compiler did not know the name; a field of that name was found.
    ByName,
    /// The linked project must be open to go on.
    OpenToContinue(String),
    /// The linked project's type has no such field.
    NoField {
        project: String,
        type_name: String,
        field: String,
    },
    /// A host's note, already in the host's language.
    Text(String),
}

/// Why the graph went no further than a name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Unknown {
    /// The compiler did not recognize the name.
    NotRecognized,
    /// A lambda's parameter, given by code the graph does not follow.
    LambdaParameter,
    /// A local whose value cannot be told.
    Local,
}

/// Why an expansion found nothing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Failure {
    /// The project has no linked project to look for senders in.
    NoPeer,
    /// The graph goes on through this project's compiler, which is not open.
    OpenProject(String),
    NoComponentChanges,
    NoArrivals,
    NoReturn,
    NoCallers,
    NoWrites,
}

/// A node's title.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Title {
    /// A name: `Pawn.Health`, `Get()`, `5`.
    Name(String),
    /// "N more places".
    More(usize),
    /// A message arrives.
    Arrival(String),
    /// Crossing to the linked project with a message type.
    Bridge(String),
    /// An ECS filter.
    Filter(String),
}

/// Where a source lives, for its subtitle.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Place {
    /// A project, by its root.
    Project(String),
    /// An assembly or a package, by name.
    Library(String),
}

/// A node's subtitle.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Subtitle {
    /// The project, by its root.
    Project(String),
    /// A call, in this project.
    Call(String),
    /// A parameter of this method.
    Parameter(String),
    /// An ECS component, in this project.
    Component(String),
    Source {
        kind: Kind,
        place: Place,
    },
    /// A place in code: the project, the file's name, the line (zero-based).
    Site {
        project: String,
        file: String,
        line: usize,
    },
    /// The titles of the first places behind a "more" node.
    More(Vec<String>),
    /// A loop over a receiver of a message type.
    Arrival {
        receiver: String,
        message: String,
    },
    /// Comes from the linked project.
    Bridge(String),
    /// The components an ECS filter takes and leaves out.
    Filter {
        with: Vec<String>,
        without: Vec<String>,
    },
    Unknown(Unknown),
}

/// Words for the value graph. Every method has an English default.
pub trait Wording {
    /// A project's short name.
    fn project(&self, root: &str) -> String {
        last_component(root).to_owned()
    }

    /// A kind of source.
    fn kind(&self, kind: Kind) -> String {
        kind.label().to_owned()
    }

    /// Where a value the code does not write comes from, as a phrase.
    fn phrase(&self, kind: Kind) -> String {
        match kind {
            Kind::Config => "from a config".to_owned(),
            Kind::Json => "from JSON".to_owned(),
            Kind::Database => "from the database".to_owned(),
            Kind::Injection => "from dependency injection".to_owned(),
            Kind::Inspector => "from the Unity inspector".to_owned(),
            kind => self.kind(kind),
        }
    }

    fn note(&self, note: &Note) -> String {
        match note {
            Note::Deconstruction => "tuple deconstruction".to_owned(),
            Note::ByRef => "changes it through ref".to_owned(),
            Note::AddsTo(method) => format!("puts into a collection: {method}"),
            Note::Compound => "changes the old value".to_owned(),
            Note::OutArgument => "out in a call".to_owned(),
            Note::Constant => "constant".to_owned(),
            Note::Initial => "initial value".to_owned(),
            Note::GetterReturns => "the getter returns".to_owned(),
            Note::LambdaParameter => "lambda parameter".to_owned(),
            Note::ForeachItem => "foreach element".to_owned(),
            Note::PatternCheck => "is check".to_owned(),
            Note::LocalFunctionParameter(function) => format!("parameter of {function}"),
            Note::ComponentSet => "Set — the component appears or is updated".to_owned(),
            Note::ComponentAdd => "Add — the component appears".to_owned(),
            Note::ComponentRemove => "Remove — the component is removed".to_owned(),
            Note::Returns => "returns".to_owned(),
            Note::ThroughBase(base) => format!("through {base}"),
            Note::RaisesEvent(event) => format!("raises the event {event}"),
            Note::Calls(method) => format!("calls {method}"),
            Note::DefaultFor(count) => format!("default — calls without the argument: {count}"),
            Note::SameIn { count, titles } => format!("the same in {count} more: {titles}"),
            Note::DidNotFit => "did not fit into the graph".to_owned(),
            Note::NotFoundWhereSet => "where it is set was not found".to_owned(),
            Note::OnlyDefault => "the code sets only a default".to_owned(),
            Note::AlsoChangedByCode => "and the code changes it".to_owned(),
            Note::ElementKey => "element key".to_owned(),
            Note::ArgumentOf(call) => format!("argument of {call}"),
            Note::Through(locals) => format!("through {}", locals.join(" ← ")),
            Note::ByName => "found by name — may be inexact".to_owned(),
            Note::OpenToContinue(project) => {
                format!("open {} to go further", self.project(project))
            }
            Note::NoField {
                project,
                type_name,
                field,
            } => format!(
                "{type_name} in {} has no field {field}",
                self.project(project)
            ),
            Note::Text(text) => text.clone(),
        }
    }

    /// Notes one after another, `None` when there are none.
    fn notes(&self, notes: &[Note]) -> Option<String> {
        (!notes.is_empty()).then(|| {
            notes
                .iter()
                .map(|n| self.note(n))
                .collect::<Vec<_>>()
                .join(" · ")
        })
    }

    fn unknown(&self, reason: Unknown) -> String {
        match reason {
            Unknown::NotRecognized => "the compiler did not recognize the name",
            Unknown::LambdaParameter => "lambda parameter",
            Unknown::Local => "a local — where its value comes from cannot be told",
        }
        .to_owned()
    }

    fn failure(&self, failure: &Failure) -> String {
        match failure {
            Failure::NoPeer => "the project has no linked project — no senders to find".to_owned(),
            Failure::OpenProject(root) => format!(
                "open {} — the graph follows its compiler",
                self.project(root)
            ),
            Failure::NoComponentChanges => {
                "no Set, Add or Remove of this component was found".to_owned()
            }
            Failure::NoArrivals => "no sends were found".to_owned(),
            Failure::NoReturn => {
                "no return was found — a method without a body or from an assembly".to_owned()
            }
            Failure::NoCallers => {
                "no calls were found — the engine or reflection calls the method".to_owned()
            }
            Failure::NoWrites => {
                "no writes were found — the value is set in the declaration or through reflection"
                    .to_owned()
            }
        }
    }

    fn title(&self, title: &Title) -> String {
        match title {
            Title::Name(name) => name.clone(),
            Title::More(count) => format!(
                "{count} more {}",
                if *count == 1 { "place" } else { "places" }
            ),
            Title::Arrival(message) => format!("{message} arrives"),
            Title::Bridge(type_name) => format!("Network: {type_name}"),
            Title::Filter(name) => format!("Filter {name}"),
        }
    }

    fn subtitle(&self, subtitle: &Subtitle) -> String {
        match subtitle {
            Subtitle::Project(root) => self.project(root),
            Subtitle::Call(root) => format!("call · {}", self.project(root)),
            Subtitle::Parameter(method) => format!("parameter of {method}"),
            Subtitle::Component(root) => format!("component · {}", self.project(root)),
            Subtitle::Source { kind, place } => match place {
                Place::Project(root) => format!("{} · {}", self.kind(*kind), self.project(root)),
                Place::Library(name) => format!("{} · {name}", self.kind(*kind)),
            },
            Subtitle::Site {
                project,
                file,
                line,
            } => format!("{} · {file}:{}", self.project(project), line + 1),
            Subtitle::More(titles) => titles.join(", "),
            Subtitle::Arrival { receiver, message } => format!("loop over {receiver}<{message}>"),
            Subtitle::Bridge(root) => format!("comes from {}", self.project(root)),
            Subtitle::Filter { with, without } => {
                let mut parts = vec![with.join(", ")];
                if !without.is_empty() {
                    parts.push(format!("without {}", without.join(", ")));
                }
                parts
                    .into_iter()
                    .filter(|p| !p.is_empty())
                    .collect::<Vec<_>>()
                    .join(" · ")
            }
            Subtitle::Unknown(reason) => self.unknown(*reason),
        }
    }

    /// What the text tree says of a node it printed above.
    fn seen(&self) -> String {
        "(see above)".to_owned()
    }

    /// The kind of a node, as the text tree and `--json` name it.
    fn node_kind(&self, kind: &NodeKind) -> String {
        match kind {
            NodeKind::Value(_) => "value".to_owned(),
            NodeKind::Component(_) => "component".to_owned(),
            NodeKind::Site => "code".to_owned(),
            NodeKind::Condition => "condition".to_owned(),
            NodeKind::Arrival(_) => "arrival".to_owned(),
            NodeKind::Network => "network".to_owned(),
            NodeKind::Call(_) => "call".to_owned(),
            NodeKind::Parameter { .. } => "parameter".to_owned(),
            NodeKind::Source(origin, _) => format!("source: {}", self.kind(origin.kind)),
            NodeKind::Data => "data".to_owned(),
            NodeKind::More => "more".to_owned(),
            NodeKind::Unknown => "unknown".to_owned(),
        }
    }
}

/// The default words.
#[derive(Debug, Clone, Copy, Default)]
pub struct English;

impl Wording for English {}
