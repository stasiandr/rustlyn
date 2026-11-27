//! Which of what a change reaches is risky, and why. Reasons come from the
//! walk itself (a removed member still mentioned, a signature changed while
//! it has users, a wide fan-in), from Unity (called every frame, called by
//! the engine), and from the models a report is given ([`RiskModel`]) —
//! the compiler's failability and diagnostics among them. Steps add their
//! own ([`super::Finding::risks`]).

use std::collections::HashMap;
use std::fmt;

use rustlyn_ide::outline::DeclarationKind;
use rustlyn_ide::semantic::unity;

use super::changes::How;
use super::walk::{Impact, Node};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Level {
    Low,
    Medium,
    High,
}

impl Level {
    /// The stable English code.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Low => "low",
            Self::Medium => "medium",
            Self::High => "high",
        }
    }
}

/// How sure failability is that a failure happens.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Certainty {
    /// Every time the code reaches the place.
    Always,
    /// For some values of its inputs.
    Possible,
    /// The values of the inputs are unknown.
    Unknown,
}

/// Why a node is risky. Each has a stable English code ([`Reason::code`])
/// and an English sentence (`Display`); a host words them in its language
/// from the fields. New reasons may appear: match with a fallback to
/// `Display`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Reason {
    /// Removed, while its name still appears in `users` places.
    RemovedStillUsed { users: usize },
    /// The declaration changed and `users` places use it.
    SignatureWithUsers { users: usize },
    /// A type's header changed and `users` places use it.
    TypeHeaderWithUsers { users: usize },
    /// Called or mentioned in `count` places.
    WideFanIn { count: usize },
    /// Unity calls it every frame.
    PerFrame,
    /// Unity calls it; there are no calls in the code.
    UnityMessage,
    /// The field's value is set in `asset`: a rename or a type change
    /// without `[FormerlySerializedAs]` loses it.
    SerializedField { asset: String },
    /// The change is in code the project's build leaves out (an `#if` that
    /// is off): the compiler does not see it, so no caller of it is known and
    /// nothing checks it.
    NotBuilt,
    /// The field's value is set in `asset`, and the change leaves what is
    /// stored there alone: a default or an attribute changed, and instances
    /// there keep the value they have.
    SerializedValueKept { asset: String },
    /// A `UnityEvent` in `asset` calls the method by name.
    UnityEvent { asset: String },
    /// A compile error the change introduced.
    CompileError { code: String, message: String },
    /// A finding of the thread analyzers (`RLN1001`–`RLN1003`) the change
    /// introduced.
    Threads { code: String, message: String },
    /// Where and under what conditions the member fails.
    Failability {
        certainty: Certainty,
        exception: String,
        message: Option<String>,
        conditions: Vec<String>,
        /// The last call on the way to the failure.
        via: Option<String>,
    },
    /// A reason from a host's step or model, with its own code and its text
    /// already worded.
    Other { code: String, text: String },
}

impl Reason {
    /// The stable English code: `removed_still_used`, `per_frame`…
    #[must_use]
    pub fn code(&self) -> &str {
        match self {
            Self::RemovedStillUsed { .. } => "removed_still_used",
            Self::SignatureWithUsers { .. } => "signature_with_users",
            Self::TypeHeaderWithUsers { .. } => "type_header_with_users",
            Self::WideFanIn { .. } => "wide_fan_in",
            Self::PerFrame => "per_frame",
            Self::UnityMessage => "unity_message",
            Self::NotBuilt => "not_built",
            Self::SerializedField { .. } => "serialized_field",
            Self::SerializedValueKept { .. } => "serialized_value_kept",
            Self::UnityEvent { .. } => "unity_event",
            Self::CompileError { .. } => "compile_error",
            Self::Threads { .. } => "threads",
            Self::Failability { .. } => "failability",
            Self::Other { code, .. } => code,
        }
    }
}

impl fmt::Display for Reason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RemovedStillUsed { users } => write!(
                f,
                "removed, but its name still appears in {users} places: the build or the behaviour will break"
            ),
            Self::SignatureWithUsers { users } => {
                write!(f, "the declaration changed and {users} places use it")
            }
            Self::TypeHeaderWithUsers { users } => {
                write!(f, "the type's header changed and {users} places use it")
            }
            Self::WideFanIn { count } => write!(f, "called or mentioned in {count} places"),
            Self::PerFrame => {
                f.write_str("Unity calls it every frame: an error or slow code shows at once")
            }
            Self::UnityMessage => f.write_str("Unity calls it; there are no calls in the code"),
            Self::SerializedField { asset } => write!(
                f,
                "the field's value is set in {asset}: a rename or a type change without [FormerlySerializedAs] loses it"
            ),
            Self::NotBuilt => f.write_str(
                "in code this build leaves out (an #if that is off): no callers are known, and the compiler checks nothing here",
            ),
            Self::SerializedValueKept { asset } => write!(
                f,
                "the field's value is set in {asset}: serialized instances keep their own value, not the new default"
            ),
            Self::UnityEvent { asset } => {
                write!(f, "{asset} calls it by name from a UnityEvent")
            }
            Self::CompileError { code, message } => {
                write!(f, "compile error {code}: {message}")
            }
            Self::Threads { code, message } => write!(f, "{code}: {message}"),
            Self::Failability {
                certainty,
                exception,
                message,
                conditions,
                via,
            } => {
                let when = match certainty {
                    Certainty::Always => "always fails once it gets there",
                    Certainty::Possible => "may fail",
                    Certainty::Unknown => "may fail — the values of its inputs are unknown",
                };
                write!(f, "{when}: {exception}")?;
                if let Some(message) = message {
                    write!(f, " \"{message}\"")?;
                }
                if !conditions.is_empty() {
                    write!(f, " when {}", conditions.join(" and "))?;
                }
                if let Some(via) = via {
                    write!(f, " (via {via})")?;
                }
                Ok(())
            }
            Self::Other { text, .. } => f.write_str(text),
        }
    }
}

/// One reason for risk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Risk {
    pub level: Level,
    pub reason: Reason,
    /// Where, when it is one place: relative path and line from zero.
    pub at: Option<(String, usize)>,
}

impl Risk {
    #[must_use]
    pub const fn new(level: Level, reason: Reason) -> Self {
        Self {
            level,
            reason,
            at: None,
        }
    }

    /// The same, at one place.
    #[must_use]
    pub fn at(mut self, path: impl Into<String>, line: usize) -> Self {
        self.at = Some((path.into(), line));
        self
    }

    /// The stable English code of its reason.
    #[must_use]
    pub fn code(&self) -> &str {
        self.reason.code()
    }
}

/// A model of risk for members — failability, for one: where and under
/// what conditions a member fails.
pub trait RiskModel: Sync {
    /// Once per report, before the nodes: what is expensive can be computed
    /// at once and on several threads.
    fn prepare(&self, _context: &Context<'_>) {}

    /// The reasons for one node.
    fn risks(&self, node: &Node, context: &Context<'_>) -> Vec<Risk>;
}

/// What a model may know about the report besides the node.
#[derive(Debug, Clone, Copy)]
pub struct Context<'a> {
    pub impact: &'a Impact,
    /// The changed files' text before the change, by their new path.
    pub old_texts: &'a HashMap<String, String>,
}

/// How many calls make a wide fan-in.
const WIDE: usize = 10;

/// The reasons for risk of each node of the walk, in node order: the walk's
/// own and Unity's, then each model's.
#[must_use]
pub fn assess(
    impact: &Impact,
    models: &[&dyn RiskModel],
    old_texts: &HashMap<String, String>,
) -> Vec<Vec<Risk>> {
    let context = Context { impact, old_texts };
    for model in models {
        model.prepare(&context);
    }
    let mut all: Vec<Vec<Risk>> = vec![Vec::new(); impact.nodes.len()];
    for (index, node) in impact.nodes.iter().enumerate() {
        let risks = &mut all[index];
        let member = &node.member;
        let name = member.short_name();
        let users = impact
            .nodes
            .iter()
            .filter(|n| n.edges.iter().any(|e| e.from == index))
            .count();
        match node.change {
            Some(How::Removed) if users > 0 => {
                risks.push(Risk::new(Level::High, Reason::RemovedStillUsed { users }))
            }
            Some(How::Signature) if users > 0 && !member.is_type() => {
                let level = if users >= WIDE {
                    Level::High
                } else {
                    Level::Medium
                };
                risks.push(Risk::new(level, Reason::SignatureWithUsers { users }));
            }
            Some(How::Signature) if member.is_type() && users > 0 => {
                risks.push(Risk::new(
                    Level::Medium,
                    Reason::TypeHeaderWithUsers { users },
                ));
            }
            _ => {}
        }
        if node.inactive {
            risks.push(Risk::new(Level::Medium, Reason::NotBuilt));
        }
        if node.fan_in >= WIDE && node.depth <= 1 {
            risks.push(Risk::new(
                Level::Medium,
                Reason::WideFanIn { count: node.fan_in },
            ));
        }
        if member.kind == DeclarationKind::Method {
            if unity::is_per_frame(name) {
                risks.push(Risk::new(Level::Medium, Reason::PerFrame));
            } else if unity::is_message(name) {
                risks.push(Risk::new(Level::Low, Reason::UnityMessage));
            }
        }
        for model in models {
            risks.extend(model.risks(node, &context));
        }
    }
    all
}
