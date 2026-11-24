//! Threads with a deep stack, for calls into the compiler.
//!
//! The compiler recurses exactly as deep as the code it reads: a long string
//! concatenation, an enum member whose value is written in terms of others —
//! and the binder has large frames. The threads an application's thread pool
//! hands out often have half a megabyte of stack, which real projects
//! overflow, and an overflow takes down the whole process rather than one
//! answer. [`run`] moves the call to a thread with a 64 MB stack while the
//! caller waits, as it would have waited anyway.
//!
//! Threads are not made per call: a finished one waits for the next job, and
//! a new one appears only when all are busy, so simultaneous questions do not
//! queue behind one another. The stack is only reserved; memory is taken for
//! what is actually used.

use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::Mutex;
use std::sync::mpsc::{Receiver, SyncSender, sync_channel};

/// The stack size of a worker thread.
pub const SIZE: usize = 64 << 20;

/// How many idle threads to keep; the rest end.
const SPARE: usize = 4;

/// A job with its lifetime already erased (see `run`), and the signal that it
/// ran and was released.
type Job = (Box<dyn FnOnce() + Send + 'static>, SyncSender<()>);

/// Idle threads, each waiting for a job on its own channel.
static IDLE: Mutex<Vec<SyncSender<Job>>> = Mutex::new(Vec::new());

thread_local! {
    /// This thread is one of ours, with a deep stack.
    static DEEP: Cell<bool> = const { Cell::new(false) };
}

/// Runs `body` on a thread with a deep stack and returns its answer; on such
/// a thread already, right here. A panic in `body` reaches the caller as if
/// `body` had run on its thread.
pub fn run<T: Send>(body: impl FnOnce() -> T + Send) -> T {
    if deep_enough() {
        return body();
    }
    let mut result: Option<std::thread::Result<T>> = None;
    {
        let slot = Slot(&raw mut result);
        // The caller's priority: a background compile must not compete with
        // a completion someone is waiting for at the keyboard.
        let qos = qos::current();
        let job: Box<dyn FnOnce() + Send + '_> = Box::new(move || {
            qos::adopt(qos);
            let answer = catch_unwind(AssertUnwindSafe(body));
            // Through the method only: the closure has to capture the whole
            // `Slot`, not its one field (a raw pointer is not `Send`).
            unsafe { slot.put(answer) };
        });
        // The lifetime is erased: the job borrows the caller's stack, but
        // `perform` returns only after the thread has run and released it.
        let job: Box<dyn FnOnce() + Send + 'static> = unsafe { std::mem::transmute(job) };
        perform(job);
    }
    match result {
        Some(Ok(answer)) => answer,
        Some(Err(panic)) => resume_unwind(panic),
        // Whether on a worker or here, the job has run by now.
        None => unreachable!("a deep-stack job returned no answer"),
    }
}

/// Where the worker puts the answer: a place on the stack of the caller, who
/// waits.
struct Slot<T>(*mut Option<std::thread::Result<T>>);

unsafe impl<T: Send> Send for Slot<T> {}

impl<T> Slot<T> {
    /// Puts the answer. The caller is waiting and does not touch the place
    /// meanwhile.
    unsafe fn put(self, answer: std::thread::Result<T>) {
        unsafe { *self.0 = Some(answer) };
    }
}

/// Whether this thread's stack is deep: one of ours, or another with as deep
/// a stack.
fn deep_enough() -> bool {
    DEEP.with(Cell::get) || qos::stack_size().is_some_and(|size| size >= SIZE)
}

/// Hands `job` to a thread and waits until it has run and released it.
fn perform(job: Box<dyn FnOnce() + Send + 'static>) {
    let (done, finished) = sync_channel::<()>(1);
    let mut job = Some((job, done));
    // An idle thread may have just ended; then the next one.
    loop {
        let worker = IDLE.lock().unwrap_or_else(|e| e.into_inner()).pop();
        let Some(worker) = worker else { break };
        match worker.send(job.take().expect("the job is still here")) {
            Ok(()) => break,
            Err(returned) => job = Some(returned.0),
        }
    }
    if let Some(job) = job {
        let (jobs, inbox) = sync_channel::<Job>(1);
        let own = jobs.clone();
        let spawned = std::thread::Builder::new()
            .name("rustlyn.deep".into())
            .stack_size(SIZE)
            .spawn(move || work(own, inbox));
        if spawned.is_err() {
            // No thread to be had: run it here. A shallow stack beats no
            // answer.
            let (body, done) = job;
            body();
            let _ = done.send(());
        } else if let Err(returned) = jobs.send(job) {
            // The thread was just made and is waiting; if it is not, it died
            // before starting. Then here.
            let (body, done) = returned.0;
            body();
            let _ = done.send(());
        }
    }
    let _ = finished.recv();
}

/// A worker: runs jobs for as long as it stays in the pool.
fn work(own: SyncSender<Job>, inbox: Receiver<Job>) {
    DEEP.with(|deep| deep.set(true));
    while let Ok((body, done)) = inbox.recv() {
        body();
        // Into the pool first, then the signal: the caller may come right
        // back with the next question, and this thread is already waiting.
        let stays = {
            let mut idle = IDLE.lock().unwrap_or_else(|e| e.into_inner());
            let stays = idle.len() < SPARE;
            if stays {
                idle.push(own.clone());
            }
            stays
        };
        let _ = done.send(());
        if !stays {
            return;
        }
    }
}

/// A thread's priority and stack size: through libSystem on macOS; on other
/// systems they can be neither read nor carried over.
mod qos {
    #[cfg(target_os = "macos")]
    unsafe extern "C" {
        fn qos_class_self() -> u32;
        fn pthread_set_qos_class_self_np(qos: u32, relative_priority: i32) -> i32;
        fn pthread_self() -> usize;
        fn pthread_get_stacksize_np(thread: usize) -> usize;
    }

    #[cfg(target_os = "macos")]
    pub(super) fn current() -> u32 {
        unsafe { qos_class_self() }
    }

    #[cfg(target_os = "macos")]
    pub(super) fn adopt(qos: u32) {
        unsafe { pthread_set_qos_class_self_np(qos, 0) };
    }

    #[cfg(target_os = "macos")]
    pub(super) fn stack_size() -> Option<usize> {
        Some(unsafe { pthread_get_stacksize_np(pthread_self()) })
    }

    #[cfg(not(target_os = "macos"))]
    pub(super) fn current() -> u32 {
        0
    }

    #[cfg(not(target_os = "macos"))]
    pub(super) fn adopt(_qos: u32) {}

    #[cfg(not(target_os = "macos"))]
    pub(super) fn stack_size() -> Option<usize> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn answers_on_a_deep_stack() {
        let answer = run(|| (deep_enough(), 6 * 7));
        assert_eq!(
            answer,
            (true, 42),
            "the body runs on a deep stack and answers"
        );
        let nested = run(|| run(|| 1) + 1);
        assert_eq!(nested, 2, "already deep: runs right there");
    }

    #[test]
    fn a_panic_reaches_the_caller() {
        let caught = std::panic::catch_unwind(|| run(|| panic!("inside")));
        assert!(caught.is_err());
        assert_eq!(run(|| 5), 5, "the pool still works after a panic");
    }
}
