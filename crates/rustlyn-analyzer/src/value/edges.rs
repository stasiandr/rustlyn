//! What a host adds to the value graph that the code alone does not show:
//! values that cross to a linked project as messages, values that come
//! from the host's own data (config files), and the loops that run when a
//! message arrives. A host implements [`EdgeProvider`] and puts it on its
//! projects ([`super::Project::edges`]); every method has a default that
//! adds nothing.

use std::collections::HashSet;

use super::analysis::{Context, Decl, Site, Trigger};
use super::compiler::Declaration;
use super::flow;
use super::origin::ValueOrigin;

/// What is known of a field or property whose origin is asked.
#[derive(Debug, Clone, Copy)]
pub struct Member<'a> {
    pub declaration: &'a Decl,
    /// Its attributes, by their last name part, without `Attribute`.
    pub attributes: &'a HashSet<String>,
    /// The attributes of the type that holds it.
    pub owner_attributes: &'a HashSet<String>,
    /// The declaration's text before the name: attributes, modifiers, type.
    pub head: &'a str,
}

/// A host's edges of the value graph. Called on the thread that runs an
/// expansion, with the project's [`Context`] to ask the compiler through.
pub trait EdgeProvider: Send + Sync {
    /// The types (by short name) whose fields continue in the linked
    /// project: a field of such a type that this project only receives —
    /// no writes but its reader's — is followed to the same field there.
    fn bridged_types(&self, cx: &Context) -> HashSet<String> {
        let _ = cx;
        HashSet::new()
    }

    /// Whether a write to `value` inside `method` only reads it off the
    /// wire, in the type's own reader. Such writes are not where the value
    /// comes from for a bridged type.
    fn is_read_site(&self, cx: &Context, value: &Decl, method: Option<&Declaration>) -> bool {
        let _ = (cx, value, method);
        false
    }

    /// Where a field's value comes from when it is the host's data (a
    /// config model's key). Asked before the built-in JSON, dependency
    /// injection and Unity inspector rules.
    fn origin(&self, cx: &Context, member: &Member<'_>) -> Option<ValueOrigin> {
        let _ = (cx, member);
        None
    }

    /// A call whose value is an origin of its own: loading a whole config
    /// by its key, rather than the loader's code.
    fn call_origin(&self, cx: &Context, call: &flow::Source, units: &[u16]) -> Option<ValueOrigin> {
        let _ = (cx, call, units);
        None
    }

    /// What makes a loop over the field `name` run, and the UTF-16 offset in
    /// `units` of what says so: a receiver of a message type.
    fn trigger(&self, cx: &Context, units: &[u16], name: &str) -> Option<(Trigger, usize)> {
        let _ = (cx, units, name);
        None
    }

    /// Where the message `message` is sent in this project: the places an
    /// arrival of it in the linked project expands into.
    fn arrivals(&self, cx: &Context, message: &str) -> Vec<Site> {
        let _ = (cx, message);
        Vec::new()
    }

    /// The lines of data where a value of the host's origin is set (a
    /// config's JSON). `None`: not this provider's origin.
    fn where_set(&self, cx: &Context, origin: &ValueOrigin, value: &Decl) -> Option<Vec<Site>> {
        let _ = (cx, origin, value);
        None
    }
}
