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
/// asks for it. This is only reserved, not touched.
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
/// Panics where `f` does, or where a thread cannot be started.
pub fn deep<R: Send>(f: impl FnOnce() -> R + Send) -> R {
    if DEEP.get() {
        return f();
    }
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(scope, || {
                DEEP.set(true);
                f()
            })
            .expect("a thread with a deep stack should start")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// `f` applied to every item, on as many threads as there are cores, the
/// results in the order of the items.
///
/// # Panics
///
/// Panics where `f` does, or where a thread cannot be started.
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
    let done: Vec<Vec<(usize, R)>> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                std::thread::Builder::new()
                    .stack_size(STACK)
                    .spawn_scoped(scope, || {
                        DEEP.set(true);
                        let mut done = Vec::new();
                        loop {
                            let index = next.fetch_add(1, Ordering::Relaxed);
                            let Some(item) = items.get(index) else {
                                break;
                            };
                            done.push((index, f(item)));
                        }
                        done
                    })
                    .expect("a worker thread should start")
            })
            .collect();
        workers
            .into_iter()
            .map(|worker| {
                worker
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
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
