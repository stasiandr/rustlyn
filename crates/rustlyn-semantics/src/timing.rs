//! How long each phase of a compile takes, for whoever is making it faster.
//!
//! `RUSTLYN_TIMINGS=1` in the environment prints one line per phase to
//! standard error as the phase ends; without it a phase costs one load of a
//! flag that is read once.

use std::sync::OnceLock;
use std::time::Instant;

/// A phase being timed: it reports when dropped.
#[derive(Debug)]
pub struct Phase {
    name: &'static str,
    started: Option<Instant>,
}

/// Starts timing a phase, which ends where the value is dropped.
#[must_use]
pub fn phase(name: &'static str) -> Phase {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    let enabled = *ENABLED.get_or_init(|| std::env::var_os("RUSTLYN_TIMINGS").is_some());
    Phase {
        name,
        started: enabled.then(Instant::now),
    }
}

impl Drop for Phase {
    fn drop(&mut self) {
        if let Some(started) = self.started {
            eprintln!("{:>10.3} s  {}", started.elapsed().as_secs_f64(), self.name);
        }
    }
}
