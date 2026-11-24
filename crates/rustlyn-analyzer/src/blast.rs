//! Blast radius: what a change to the code reaches, and which of it is
//! risky.
//!
//! The input is a patch ([`diff`]). Its lines land on the structure of the
//! files ([`changes`]): which members changed and how — body, signature,
//! added, removed. Then a forward walk over the compiler ([`walk`]), the value
//! graph turned around: who calls what changed, who reads what it writes,
//! who uses a changed type. Steps add what the code alone does not show —
//! the built-in one finds the Unity scenes and prefabs the touched scripts
//! sit in ([`assets`]); a host adds its own through [`BlastStep`]. Every
//! node gets its reasons for risk ([`risk`], [`compiler_risks`], and any
//! [`RiskModel`] a host adds). The report is JSON for agents and a tree for
//! people ([`report`]); [`mcp`] serves it to agents over the Model Context
//! Protocol.
//!
//! Risks are structured ([`risk::Reason`]) with stable English codes, so a
//! host can word them in its own language ([`report::Wording`]).

pub mod assets;
pub mod changes;
pub mod compiler_risks;
pub mod diff;
pub mod mcp;
pub mod project;
pub mod report;
pub mod risk;
pub mod setup;
pub mod walk;

mod ask;

#[cfg(test)]
mod testing;

use std::collections::HashMap;

use rustlyn_ide::Session;
use rustlyn_ide::formats::json::Json;

pub use report::{Report, Request, Wording, analyze};
pub use risk::{Context, Level, Reason, Risk, RiskModel};
pub use walk::{Impact, Limits, Node};

/// What a host plugs into a report: steps that find more than the walk
/// does, and models that add reasons for risk.
#[derive(Default)]
pub struct Extensions<'a> {
    /// Run after the walk, before the built-in Unity step, in this order.
    pub steps: Vec<&'a dyn BlastStep>,
    /// Asked about every node, after the built-in reasons.
    pub risks: Vec<&'a dyn RiskModel>,
}

impl std::fmt::Debug for Extensions<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Extensions")
            .field(
                "steps",
                &self.steps.iter().map(|s| s.name()).collect::<Vec<_>>(),
            )
            .field("risks", &self.risks.len())
            .finish()
    }
}

/// What a step may know besides the walk.
#[derive(Debug, Clone, Copy)]
pub struct StepContext<'a> {
    /// The project root; paths in the walk are relative to it.
    pub root: &'a str,
    /// The compiled project.
    pub session: &'a Session,
    /// The changed files' text before the change, by their new path.
    pub old_texts: &'a HashMap<String, String>,
}

/// A step of the report beyond the walk: something the change reaches that
/// the compiler does not see — an asset that references a script, the other
/// end of a network protocol.
pub trait BlastStep: Sync {
    /// The step's key in the report: its findings are listed under it in
    /// the JSON and counted under it in the summary. Lowercase English,
    /// stable: `assets`.
    fn name(&self) -> &'static str;

    /// What the step finds for the walk's nodes.
    fn run(&self, cx: &StepContext<'_>, impact: &Impact) -> Vec<Finding>;
}

/// One thing a step found.
#[derive(Debug, Clone, PartialEq)]
pub struct Finding {
    /// Its entry in the report's JSON, under the step's name.
    pub json: Json,
    /// For the text tree: a heading line, then detail lines (indented by
    /// the report).
    pub text: Vec<String>,
    /// The nodes of the walk it concerns.
    pub nodes: Vec<usize>,
    /// Reasons for risk it adds to nodes: (node, risk).
    pub risks: Vec<(usize, Risk)>,
}

/// What one step found.
#[derive(Debug, Clone, PartialEq)]
pub struct StepFindings {
    pub step: &'static str,
    pub findings: Vec<Finding>,
}
