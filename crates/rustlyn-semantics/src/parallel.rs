//! Work spread over every core, with the answers in the order asked.
//!
//! Parsing a file and binding a body are independent of every other file and
//! body once the declarations are done, and each takes long enough that
//! handing them out one at a time costs nothing next to the work: a thread
//! takes the next item when it is done with the last, so one large file does
//! not hold up a share of small ones.

use std::sync::atomic::{AtomicUsize, Ordering};

/// How much stack a thread that binds or emits gets. Both recurse as deep
/// as the tree they are given, which the parser lets go 12,288 levels deep
/// (`MAX_DEPTH` in rustlyn-syntax). An unoptimized build takes up to 40 KB
/// of stack for a level (`bind_expression_core` alone has a frame of 29
/// KB): 480 MB for the deepest tree of the worst shape, and twice that is
/// reserved. An optimized build takes a fraction of it, and a 32-bit
/// address space has no room for a gigabyte, so only a 64-bit debug build
/// asks for it. This is only reserved, not touched; where even that much
/// cannot be reserved, a thread takes the largest stack that can be.
pub const STACK: usize = if cfg!(all(debug_assertions, target_pointer_width = "64")) {
    1 << 30
} else {
    256 << 20
};

/// How much stack a thread that only parses gets: the parser recurses as
/// deep as the source nests, which it limits to 1,024 levels, and takes a
/// few megabytes of an unoptimized build's stack for them.
pub(crate) const PARSE_STACK: usize = 256 << 20;

/// How many threads work is spread over: one per core, or what
/// `RUSTLYN_THREADS` says — `1` makes a compile run on one, as it did before
/// any of it was spread out.
#[must_use]
pub fn threads() -> usize {
    static THREADS: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *THREADS.get_or_init(|| {
        std::env::var("RUSTLYN_THREADS")
            .ok()
            .and_then(|value| value.parse().ok())
            .filter(|&count| count > 0)
            .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, usize::from))
    })
}

thread_local! {
    /// Whether this thread was started with [`STACK`].
    static DEEP: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// `f` run on a stack as deep as a worker's: on this thread if it is one,
/// on a thread started for it otherwise, while this one waits.
///
/// Binding and emitting recurse as deep as the source nests — the parser
/// lets a tree go a few thousand levels deep — and whoever asks for them
/// may be on a main thread's eight megabytes, or one. A compile of one
/// file does all of its work where it was asked for, so it is asked for
/// here.
///
/// # Panics
///
/// Panics where `f` does.
pub fn deep<R: Send>(f: impl FnOnce() -> R + Send) -> R {
    if DEEP.get() {
        return f();
    }
    // The work is handed over once, to whichever thread starts.
    let work = std::sync::Mutex::new(Some(f));
    let run = || {
        let f = work
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take()
            .expect("the work is taken once");
        f()
    };
    let done = std::thread::scope(|scope| {
        let started = spawn_scoped(scope, STACK, || {
            || {
                DEEP.set(true);
                run()
            }
        });
        started.map(|thread| {
            thread
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
        })
    });
    // No thread at all: the work is done here, as deep as this stack goes.
    done.unwrap_or_else(run)
}

/// The stack sizes to try for a thread, from `largest` down: half of it and
/// half again, to 16 MB. Where memory is limited a gigabyte may not be
/// there to reserve for each core, and a thread with less still compiles
/// everything but the deepest trees.
///
/// Where the process may only have so much address space (`ulimit -v`),
/// the stacks of all the workers together start at a quarter of it: taken
/// whole, they would leave the heap nothing to grow into.
fn stacks(largest: usize) -> impl Iterator<Item = usize> {
    let largest = address_space().map_or(largest, |limit| {
        largest.min(limit / 4 / threads().max(1)).max(16 << 20)
    });
    std::iter::successors(Some(largest), |size| Some(size / 2)).take_while(|size| *size >= 16 << 20)
}

/// How much address space the process may have, where that is limited and
/// the system says so (`/proc/self/limits`, on Linux).
fn address_space() -> Option<usize> {
    static LIMIT: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
    *LIMIT.get_or_init(|| {
        let limits = std::fs::read_to_string("/proc/self/limits").ok()?;
        let line = limits
            .lines()
            .find_map(|line| line.strip_prefix("Max address space"))?;
        // The soft limit, in bytes, or `unlimited`.
        line.split_whitespace().next()?.parse().ok()
    })
}

/// A thread in `scope` running what `work` makes, on the largest stack
/// there is room for from `largest` down, or `None` where none can be
/// started. `work` is asked again for each size tried.
pub fn spawn_scoped<'scope, T, F>(
    scope: &'scope std::thread::Scope<'scope, '_>,
    largest: usize,
    work: impl Fn() -> F,
) -> Option<std::thread::ScopedJoinHandle<'scope, T>>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    stacks(largest).find_map(|size| {
        std::thread::Builder::new()
            .stack_size(size)
            .spawn_scoped(scope, work())
            .ok()
    })
}

/// `f` applied to every item, on as many threads as there are cores, the
/// results in the order of the items.
///
/// # Panics
///
/// Panics where `f` does.
pub fn map<T, R, F>(items: &[T], f: F) -> Vec<R>
where
    T: Sync,
    R: Send,
    F: Fn(&T) -> R + Sync,
{
    let threads = threads().min(items.len());
    if threads <= 1 {
        return items.iter().map(f).collect();
    }
    let next = AtomicUsize::new(0);
    // What a worker does: the next item, until there is none.
    let work = || {
        let mut done = Vec::new();
        loop {
            let index = next.fetch_add(1, Ordering::Relaxed);
            let Some(item) = items.get(index) else {
                break;
            };
            done.push((index, f(item)));
        }
        done
    };
    let done: Vec<Vec<(usize, R)>> = std::thread::scope(|scope| {
        // Each worker takes the largest stack there is room for; one that
        // cannot be started at all is done without, and the items it would
        // have taken go to the others.
        let workers: Vec<_> = (0..threads)
            .map_while(|_| {
                spawn_scoped(scope, STACK, || {
                    || {
                        DEEP.set(true);
                        work()
                    }
                })
            })
            .collect();
        // Not one thread: the work is done here, as `deep` would have it.
        let here = workers.is_empty().then(|| deep(work));
        workers
            .into_iter()
            .map(|worker| {
                worker
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
            .chain(here)
            .collect()
    });
    let mut slots: Vec<Option<R>> = std::iter::repeat_with(|| None).take(items.len()).collect();
    for (index, result) in done.into_iter().flatten() {
        slots[index] = Some(result);
    }
    slots
        .into_iter()
        .map(|slot| slot.expect("every item should have been done"))
        .collect()
}
