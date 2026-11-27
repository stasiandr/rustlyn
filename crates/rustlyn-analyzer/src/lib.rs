//! Whole-project analyses on top of `rustlyn-ide`.
//!
//! `rustlyn-ide` answers the questions an editor asks about the file on
//! screen, in the time a keystroke allows. The questions here are about the
//! whole project and take longer: which assets reference this one, which
//! packages the projects ask for and whether a restore found them, what a
//! change to the code reaches. They run in the background, read the disk
//! directly and are free to spend seconds.
//!
//! * [`diff`] — unified diffs as git and code review services print them,
//!   and a line diff of two texts.
//! * [`unity`] — a Unity project without Unity: asset GUIDs from `.meta`
//!   files, the serialized scene and prefab format, and where an asset is
//!   used.
//! * [`nuget`] — packages: versions, `NuGet.Config`, the packages each
//!   project references, whether they were restored, and v3 feeds over a
//!   [`nuget::http::Transport`] the caller supplies.
//! * [`blast`] — the blast radius of a change: what it reaches through
//!   the compiler and the assets, and which of it is risky; hosts plug in
//!   their own steps and risk models. The `rustlyn-blast` binary serves it
//!   from a terminal and over the Model Context Protocol.
//! * [`reach`] — does a change lead to a given set of APIs: the cone of
//!   own code that leads to them through calls, fields and ECS components,
//!   and a change judged against it. The `rustlyn-reach` binary serves it
//!   from a terminal.
//! * [`value`] — the value graph: where a value comes from, through the
//!   places that write it, to its sources; hosts add their own edges.
//! * [`fail`] — how a member can fail, when and whether it can happen, in
//!   words; the `rustlyn-fail` binary prints it from a terminal.
//! * [`deep`] — a pool of threads with a deep stack, for the compiler's
//!   recursion over deeply nested code.
//!
//! Positions in the public API are byte offsets and zero-based line numbers
//! of the UTF-8 text unless an item says otherwise. Results are structured
//! (enums and stable English codes), so a front end can word them in any
//! language. There is no networking here and no dependency outside Rustlyn:
//! requests are built and answers interpreted, and the caller sends them.

pub mod blast;
pub mod cli;
pub mod deep;
pub mod diff;
pub mod fail;
pub mod nuget;
pub mod reach;
pub mod unity;
pub mod value;
