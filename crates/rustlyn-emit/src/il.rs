//! IL instructions and the method bodies they make up.
//!
//! An instruction stream is built against labels rather than offsets, because
//! the size of a branch depends on the distance it covers and the distance
//! depends on the sizes in between. So the layout is found rather than
//! computed: every branch starts out long, and the ones whose target is within
//! a byte are shrunk until no more can be, because shrinking one branch can
//! bring another into range. Starting long and shrinking terminates; starting
//! short and growing does not obviously.
//!
//! `.maxstack` is computed rather than guessed. The runtime rejects a body
//! whose declared stack depth is too small, and a body that merely looks
//! plausible is exactly the kind of thing that fails at a customer rather than
//! in a test.

use std::cell::RefCell;
use std::collections::HashMap;

/// A metadata token: the table it points into and the row inside it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub(crate) struct Token(pub(crate) u32);

impl Token {
    #[must_use]
    pub(crate) const fn new(table: u8, row: u32) -> Self {
        Self(((table as u32) << 24) | row)
    }
}

/// A position in an instruction stream, fixed up once the stream is laid out.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct Label(usize);

/// One IL instruction.
///
/// The set is what the emitter needs rather than the whole of ECMA-335 §III;
/// an opcode with no way to reach it would be untested.
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) enum Instruction {
    /// Nothing at all — a place for a label that must not coincide with the
    /// first instruction of a protected region.
    Nop,
    Pop,
    Dup,
    Ret,
    Throw,
    /// A bare `throw;` inside a `catch`: the exception carries on with the
    /// stack trace it already had, which `throw e;` would throw away.
    Rethrow,

    LoadArgument(u16),
    StoreArgument(u16),
    LoadArgumentAddress(u16),
    LoadLocal(u16),
    StoreLocal(u16),
    LoadLocalAddress(u16),

    LoadInt32(i32),
    LoadInt64(i64),
    LoadFloat32(f32),
    LoadFloat64(f64),
    LoadNull,
    LoadString(Token),

    Add,
    Subtract,
    Multiply,
    /// `add.ovf`, `sub.ovf`, `mul.ovf` and their `.un` forms: the same
    /// arithmetic, throwing where the result does not fit (`checked`).
    AddOvf,
    AddOvfUn,
    SubtractOvf,
    SubtractOvfUn,
    MultiplyOvf,
    MultiplyOvfUn,
    Divide,
    DivideUnsigned,
    Remainder,
    RemainderUnsigned,
    And,
    Or,
    Xor,
    ShiftLeft,
    ShiftRight,
    ShiftRightUnsigned,
    Negate,
    Not,

    CompareEqual,
    CompareGreater,
    CompareGreaterUnsigned,
    CompareLess,
    CompareLessUnsigned,

    ConvertI1,
    ConvertI2,
    ConvertI4,
    ConvertI8,
    ConvertR4,
    ConvertR8,
    ConvertU1,
    ConvertU2,
    ConvertU4,
    ConvertU8,
    /// `conv.ovf.*`: a narrowing that throws where the value does not fit,
    /// from a signed source; and from an unsigned one (`.un`).
    ConvertOvfI1,
    ConvertOvfI2,
    ConvertOvfI4,
    ConvertOvfI8,
    ConvertOvfU1,
    ConvertOvfU2,
    ConvertOvfU4,
    ConvertOvfU8,
    ConvertOvfI1Un,
    ConvertOvfI2Un,
    ConvertOvfI4Un,
    ConvertOvfI8Un,
    ConvertOvfU1Un,
    ConvertOvfU2Un,
    ConvertOvfU4Un,
    ConvertOvfU8Un,
    /// `conv.ovf.i`, `conv.ovf.u` and their `.un` forms: to a native
    /// integer, throwing where the value does not fit.
    ConvertOvfI,
    ConvertOvfU,
    ConvertOvfIUn,
    ConvertOvfUUn,
    /// `conv.r.un`: an unsigned integer to a float, which `conv.r8` alone
    /// would read as signed.
    ConvertRUnsigned,
    /// `conv.i` and `conv.u`: to a native integer, which is what a pointer is.
    ConvertI,
    ConvertU,
    /// `localloc`: memory on the stack, as many bytes as the top says.
    LocalAlloc,
    /// `arglist`: the `RuntimeArgumentHandle` of a varargs method's extra
    /// arguments.
    ArgList,

    Branch(Label),
    BranchIfFalse(Label),
    BranchIfTrue(Label),
    /// Leaves a protected region, emptying the evaluation stack on the way.
    Leave(Label),
    /// Ends a `finally` handler, returning to wherever the region was left.
    EndFinally,
    /// Ends an exception filter; the value on the stack says whether the
    /// handler beside it should run.
    EndFilter,

    Call(Token),
    CallVirtual(Token),
    /// `calli`: a call through the function pointer on top of the stack,
    /// with the `StandAloneSig` that says what it takes and gives back.
    CallIndirect(Token),
    NewObject(Token),
    LoadField(Token),
    StoreField(Token),
    LoadStaticField(Token),
    StoreStaticField(Token),
    LoadStaticFieldAddress(Token),

    /// Reads through a reference, in the width the type has.
    LoadIndirect(IndirectKind),
    /// Writes through one.
    StoreIndirect(IndirectKind),
    /// The address of an array element, for passing one by reference.
    LoadElementAddress(Token),
    /// The address of a field, and of a static field.
    LoadFieldAddress(Token),

    /// The address of a method, which is half of what a delegate is made of.
    LoadFunction(Token),
    /// The same, looked up on the run-time type of what is on the stack.
    LoadVirtualFunction(Token),
    /// `constrained.`, the prefix that makes `callvirt` work on a type
    /// parameter: the receiver is an address, and the runtime decides from the
    /// type argument whether to dereference it, box it, or call directly.
    Constrained(Token),
    /// `readonly.` before `ldelema`: the address will not be written
    /// through, so the runtime skips the check that the array's run-time
    /// element type is the static one — which a covariant array fails.
    Readonly,

    /// `sizeof`: how many bytes a type takes, which the runtime fills in.
    SizeOf(Token),
    /// `mkrefany`: a `TypedReference` out of an address and the type there.
    MakeRefAny(Token),
    /// `refanyval`: the address a `TypedReference` holds, checked against
    /// the type it is asked for.
    RefAnyValue(Token),
    /// `refanytype`: the type handle a `TypedReference` holds.
    RefAnyType,
    Box(Token),
    UnboxAny(Token),
    CastClass(Token),
    IsInstance(Token),
    LoadToken(Token),
    InitObject(Token),

    NewArray(Token),
    LoadLength,
    LoadElement(Token),
    StoreElement(Token),
    StoreElementRef,
    LoadElementI1,
    LoadElementU1,
    LoadElementI2,
    LoadElementU2,
    LoadElementI4,
    LoadElementU4,
    LoadElementI8,
    LoadElementR4,
    LoadElementR8,
    LoadElementRef,
    StoreElementI1,
    StoreElementI2,
    StoreElementI4,
    StoreElementI8,
    StoreElementR4,
    StoreElementR8,
}

impl Instruction {
    /// How the instruction changes the depth of the evaluation stack.
    ///
    /// A call is the one case this cannot answer alone: how much it pops and
    /// whether it pushes depend on the signature, so the emitter passes that
    /// in through [`InstructionStream::call_effect`].
    const fn stack_effect(self) -> i32 {
        match self {
            Self::Nop
            | Self::Branch(_)
            | Self::Leave(_)
            | Self::EndFinally
            | Self::Negate
            | Self::Not
            | Self::ConvertI1
            | Self::ConvertI2
            | Self::ConvertI4
            | Self::ConvertI8
            | Self::ConvertR4
            | Self::ConvertR8
            | Self::ConvertU1
            | Self::ConvertU2
            | Self::ConvertU4
            | Self::ConvertU8
            | Self::ConvertOvfI1
            | Self::ConvertOvfI2
            | Self::ConvertOvfI4
            | Self::ConvertOvfI8
            | Self::ConvertOvfU1
            | Self::ConvertOvfU2
            | Self::ConvertOvfU4
            | Self::ConvertOvfU8
            | Self::ConvertOvfI1Un
            | Self::ConvertOvfI2Un
            | Self::ConvertOvfI4Un
            | Self::ConvertOvfI8Un
            | Self::ConvertOvfU1Un
            | Self::ConvertOvfU2Un
            | Self::ConvertOvfU4Un
            | Self::ConvertOvfU8Un
            | Self::ConvertOvfI
            | Self::ConvertOvfU
            | Self::ConvertOvfIUn
            | Self::ConvertOvfUUn
            | Self::ConvertRUnsigned
            | Self::ConvertI
            | Self::ConvertU
            | Self::LocalAlloc
            | Self::MakeRefAny(_)
            | Self::RefAnyValue(_)
            | Self::RefAnyType
            | Self::Box(_)
            | Self::UnboxAny(_)
            | Self::CastClass(_)
            | Self::IsInstance(_)
            | Self::LoadLength
            | Self::NewArray(_)
            // `ldvirtftn` swaps the object for the pointer.
            | Self::LoadVirtualFunction(_)
            // A prefix touches nothing.
            | Self::Constrained(_)
            | Self::Readonly
            // `rethrow` takes nothing: the exception is the handler's.
            | Self::Rethrow
            | Self::LoadField(_) => 0,

            Self::Dup
            | Self::LoadArgument(_)
            | Self::LoadLocal(_)
            | Self::LoadLocalAddress(_)
            | Self::LoadInt32(_)
            | Self::LoadInt64(_)
            | Self::LoadFloat32(_)
            | Self::LoadFloat64(_)
            | Self::LoadNull
            | Self::LoadString(_)
            | Self::LoadStaticField(_)
            | Self::LoadStaticFieldAddress(_)
            | Self::LoadArgumentAddress(_)
            | Self::LoadFunction(_)
            | Self::SizeOf(_)
            | Self::ArgList
            | Self::LoadToken(_) => 1,

            // `ldind` swaps the address for the value; `ldflda` swaps the
            // object for the address.
            Self::LoadIndirect(_) | Self::LoadFieldAddress(_) => 0,
            // `stind` takes the address and the value; `ldelema` takes the
            // array and the index and gives back one address.
            Self::StoreIndirect(_) => -2,
            Self::LoadElementAddress(_) => -1,

            Self::Pop
            | Self::Ret
            | Self::Throw
            | Self::StoreArgument(_)
            | Self::StoreLocal(_)
            | Self::BranchIfFalse(_)
            | Self::BranchIfTrue(_)
            | Self::EndFilter
            | Self::StoreStaticField(_)
            | Self::InitObject(_) => -1,

            Self::Add
            | Self::Subtract
            | Self::Multiply
            | Self::AddOvf
            | Self::AddOvfUn
            | Self::SubtractOvf
            | Self::SubtractOvfUn
            | Self::MultiplyOvf
            | Self::MultiplyOvfUn
            | Self::Divide
            | Self::DivideUnsigned
            | Self::Remainder
            | Self::RemainderUnsigned
            | Self::And
            | Self::Or
            | Self::Xor
            | Self::ShiftLeft
            | Self::ShiftRight
            | Self::ShiftRightUnsigned
            | Self::CompareEqual
            | Self::CompareGreater
            | Self::CompareGreaterUnsigned
            | Self::CompareLess
            | Self::CompareLessUnsigned
            | Self::LoadElement(_)
            | Self::LoadElementI1
            | Self::LoadElementU1
            | Self::LoadElementI2
            | Self::LoadElementU2
            | Self::LoadElementI4
            | Self::LoadElementU4
            | Self::LoadElementI8
            | Self::LoadElementR4
            | Self::LoadElementR8
            | Self::LoadElementRef => -1,

            // `stfld` takes the object *and* the value, which is what makes it
            // different from `stsfld`.
            Self::StoreField(_) => -2,

            Self::StoreElement(_)
            | Self::StoreElementRef
            | Self::StoreElementI1
            | Self::StoreElementI2
            | Self::StoreElementI4
            | Self::StoreElementI8
            | Self::StoreElementR4
            | Self::StoreElementR8 => -3,

            // A call's effect depends on its signature, so it is supplied.
            Self::Call(_) | Self::CallVirtual(_) | Self::CallIndirect(_) | Self::NewObject(_) => 0,
        }
    }

    /// Whether control can fall through to the next instruction.
    const fn falls_through(self) -> bool {
        !matches!(
            self,
            Self::Branch(_)
                | Self::Leave(_)
                | Self::Ret
                | Self::Throw
                | Self::Rethrow
                | Self::EndFinally
                | Self::EndFilter
        )
    }
}

/// The width a value has when it is read or written through a reference.
///
/// `ldind`/`stind` come in one form per width, and picking the wrong one reads
/// or writes the wrong number of bytes — which is not an error anything
/// catches, so the choice is made from the type rather than guessed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum IndirectKind {
    I1,
    U1,
    I2,
    U2,
    I4,
    I8,
    R4,
    R8,
    /// A reference, which is what every class and array is.
    Ref,
    /// A value type, which is copied whole and needs its token.
    Object(Token),
}

/// An instruction being built, with the stack effect of a call attached.
#[derive(Clone, Copy, Debug)]
struct Entry {
    instruction: Instruction,
    /// Overrides [`Instruction::stack_effect`] where it cannot know.
    effect: i32,
}

/// What an exception handler does when its region throws.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum HandlerKind {
    /// `catch (T e)`, which runs when the exception is a `T`.
    Catch(Token),
    /// `catch (T e) when (c)`, whose filter decides; the label is where the
    /// filter's code starts.
    Filter(Label),
    /// `finally`, which runs however the region is left.
    Finally,
}

/// One protected region and the handler that guards it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ExceptionRegion {
    pub(crate) kind: HandlerKind,
    pub(crate) try_start: Label,
    pub(crate) try_end: Label,
    pub(crate) handler_start: Label,
    pub(crate) handler_end: Label,
}

/// An exception region with its labels resolved to byte offsets.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedRegion {
    kind: ResolvedKind,
    try_offset: u32,
    try_length: u32,
    handler_offset: u32,
    handler_length: u32,
}

#[derive(Clone, Copy, Debug)]
enum ResolvedKind {
    Catch(Token),
    Filter(u32),
    Finally,
}

/// A method body under construction.
#[derive(Clone, Debug, Default)]
pub(crate) struct InstructionStream {
    entries: Vec<Entry>,
    /// Where each label lands, as an index into `entries`. `None` until the
    /// label is marked.
    labels: Vec<Option<usize>>,
    regions: Vec<ExceptionRegion>,
    /// Places control can start from that no branch reaches: the first
    /// instruction, and the entry of every handler and filter, which the
    /// runtime enters with the exception already on the stack.
    entry_points: Vec<(Label, i32)>,
    /// The labels in the order they were marked, which `end_reachable` reads
    /// from where it left off.
    marks: Vec<Label>,
    /// What `end_reachable` has worked out so far.
    reach: RefCell<Reach>,
}

/// How far control gets through the instructions written so far.
///
/// More instructions and more marked labels only add ways to get from one
/// place to another, so what has been reached stays reached, and a question
/// about the end of the stream only has to follow what was added since the
/// last one, not start over from the first instruction.
#[derive(Clone, Debug, Default)]
struct Reach {
    /// Per instruction, and one more for the end: whether control gets there.
    reached: Vec<bool>,
    /// The instructions and entry points looked at already.
    seen_entries: usize,
    seen_entry_points: usize,
    seen_marks: usize,
    /// Per label: whether a branch that is reached, or a handler, is waiting
    /// for the label to be marked.
    awaited: Vec<bool>,
    started: bool,
}

impl Reach {
    fn reach(&mut self, at: usize, work: &mut Vec<usize>) {
        if !self.reached[at] {
            self.reached[at] = true;
            work.push(at);
        }
    }
}

impl InstructionStream {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn emit(&mut self, instruction: Instruction) {
        let effect = instruction.stack_effect();
        self.entries.push(Entry {
            instruction,
            effect,
        });
    }

    /// Emits a call, `newobj` included, with what it does to the stack.
    ///
    /// `pops` counts the arguments and the receiver; `pushes` is one unless
    /// the method returns `void`.
    pub(crate) fn call_effect(&mut self, instruction: Instruction, pops: usize, pushes: usize) {
        self.entries.push(Entry {
            instruction,
            effect: pushes as i32 - pops as i32,
        });
    }

    /// Reserves a label. It must be marked before the stream is laid out.
    pub(crate) fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() - 1)
    }

    /// Fixes a label at the current position.
    pub(crate) fn mark(&mut self, label: Label) {
        // `end_reachable` keeps what it has worked out, which holds only
        // while a label stays where it was first put.
        debug_assert!(self.labels[label.0].is_none(), "a label is marked once");
        self.labels[label.0] = Some(self.entries.len());
        self.marks.push(label);
    }

    /// Fixes at the current position the label a handler or a filter starts
    /// at, which the runtime enters with `pushed` values on the stack: the
    /// exception for a `catch` or a filter, nothing for a `finally`.
    ///
    /// Said before the handler's code is written, not after: nothing
    /// branches to a handler, so until it is known for an entry everything
    /// in it looks unreachable, and an `if` inside a `catch` that asks
    /// whether its first branch can run on into the second is told it
    /// cannot.
    pub(crate) fn mark_handler(&mut self, label: Label, pushed: i32) {
        self.mark(label);
        self.enter(label, pushed);
    }

    fn enter(&mut self, label: Label, pushed: i32) {
        if !self.entry_points.iter().any(|(known, _)| *known == label) {
            self.entry_points.push((label, pushed));
        }
    }

    /// Records a protected region and its handler.
    pub(crate) fn region(&mut self, region: ExceptionRegion) {
        // A handler and a filter are entered by the runtime rather than by a
        // branch, with the exception already pushed, so the stack depth they
        // start at has to be declared or `.maxstack` would come out too small.
        // `mark_handler` has said so already for a handler written the usual
        // way; this is for one that was not.
        match region.kind {
            HandlerKind::Catch(_) => self.enter(region.handler_start, 1),
            HandlerKind::Filter(filter) => {
                self.enter(filter, 1);
                self.enter(region.handler_start, 1);
            }
            HandlerKind::Finally => self.enter(region.handler_start, 0),
        }
        self.regions.push(region);
    }

    /// Whether the flow ends before the end of the stream, so a trailing
    /// `ret` would be unreachable.
    ///
    /// The end is reached by falling off the last instruction or by a branch
    /// to a label marked there — `try { ... } catch { ... }` as the last
    /// statement leaves to exactly there, and the method still needs a `ret`
    /// for the leave to land on. But only a branch that is itself reachable
    /// counts: the `br` an `if` writes past its `else` reaches nothing when
    /// the `if` branch returned, and a `ret` after it would be a return with
    /// nothing on the stack, which the verifier refuses.
    ///
    /// A label marked at the end that only dead code branches to still needs
    /// an instruction to land on, or the branch points past the method: the
    /// `ret` is written for it, and the dead branch is the thing to avoid.
    #[must_use]
    pub(crate) fn ends_flow(&self) -> bool {
        if self.end_reachable() {
            return false;
        }
        let end = Some(self.entries.len());
        !self.entries.iter().any(|entry| {
            branch_target(entry.instruction).is_some_and(|label| self.labels[label.0] == end)
        })
    }

    /// Whether the last instruction written can run on into whatever comes
    /// after it. The runtime refuses a method whose last instruction could
    /// — reachable or not — so the end needs something even after dead code.
    #[must_use]
    pub(crate) fn last_falls_through(&self) -> bool {
        self.entries
            .last()
            .is_none_or(|entry| entry.instruction.falls_through())
    }

    /// Whether the current end of the stream can be reached: by falling off
    /// the last instruction, or by a branch from something itself reachable
    /// to a label marked there. What comes next is dead code when it cannot,
    /// and the `br` an `if` writes past its `else` is left out then.
    #[must_use]
    pub(crate) fn end_reachable(&self) -> bool {
        let end = self.entries.len();
        let mut state = self.reach.borrow_mut();
        let state = &mut *state;
        state.reached.resize(end + 1, false);
        state.awaited.resize(self.labels.len(), false);
        let mut work: Vec<usize> = Vec::new();
        if !state.started {
            state.started = true;
            state.reach(0, &mut work);
        }
        // The old end was only a place to be; now an instruction follows it.
        if state.seen_entries < end && state.reached[state.seen_entries] {
            work.push(state.seen_entries);
        }
        // A handler is entered by the runtime, not by a branch.
        for (label, _) in &self.entry_points[state.seen_entry_points..] {
            match self.labels[label.0] {
                Some(at) => state.reach(at, &mut work),
                None => state.awaited[label.0] = true,
            }
        }
        for label in &self.marks[state.seen_marks..] {
            if state.awaited[label.0] {
                state.awaited[label.0] = false;
                let at = self.labels[label.0].expect("a marked label is placed");
                state.reach(at, &mut work);
            }
        }
        state.seen_entries = end;
        state.seen_entry_points = self.entry_points.len();
        state.seen_marks = self.marks.len();
        while let Some(at) = work.pop() {
            if at >= end {
                continue;
            }
            let instruction = self.entries[at].instruction;
            if let Some(target) = branch_target(instruction) {
                match self.labels[target.0] {
                    Some(to) => state.reach(to, &mut work),
                    None => state.awaited[target.0] = true,
                }
            }
            if instruction.falls_through() {
                state.reach(at + 1, &mut work);
            }
        }
        state.reached[end]
    }

    /// Encodes the stream, returning the bytes, the stack depth they need and
    /// the exception regions with their offsets filled in.
    #[must_use]
    pub(crate) fn finish(&self) -> (Vec<u8>, u16, Vec<ResolvedRegion>) {
        let (offsets, short) = self.layout();
        let mut code = Vec::new();
        for (index, entry) in self.entries.iter().enumerate() {
            let start = code.len();
            debug_assert_eq!(start, offsets[index] as usize);
            self.encode(entry.instruction, &offsets, start, short[index], &mut code);
        }

        let regions = self
            .regions
            .iter()
            .map(|region| {
                let try_offset = self.target(region.try_start, &offsets);
                let handler_offset = self.target(region.handler_start, &offsets);
                ResolvedRegion {
                    kind: match region.kind {
                        HandlerKind::Catch(token) => ResolvedKind::Catch(token),
                        HandlerKind::Filter(filter) => {
                            ResolvedKind::Filter(self.target(filter, &offsets))
                        }
                        HandlerKind::Finally => ResolvedKind::Finally,
                    },
                    try_offset,
                    try_length: self.target(region.try_end, &offsets) - try_offset,
                    handler_offset,
                    handler_length: self.target(region.handler_end, &offsets) - handler_offset,
                }
            })
            .collect();

        (code, self.max_stack(), regions)
    }

    /// The byte offset of each instruction, plus the total length at the end,
    /// and which branches came out short enough to use the two-byte form.
    ///
    /// A branch is long until it is shown not to need to be. Each pass marks
    /// the ones whose target is now within a signed byte and lays the stream
    /// out again; shrinking one branch can bring another into range, so it
    /// runs to a fixed point. It only ever shrinks, so it ends.
    fn layout(&self) -> (Vec<u32>, Vec<bool>) {
        let mut short = vec![false; self.entries.len()];
        loop {
            let offsets = self.offsets_with(&short);
            let mut changed = false;
            for (index, entry) in self.entries.iter().enumerate() {
                if short[index] {
                    continue;
                }
                let Some(label) = branch_target(entry.instruction) else {
                    continue;
                };
                let Some(target) = self.labels[label.0] else {
                    continue;
                };
                // The offset is measured from the instruction after the
                // branch, which the short form makes two bytes long.
                let next = i64::from(offsets[index]) + 2;
                let delta = i64::from(offsets[target]) - next;
                if i8::try_from(delta).is_ok() {
                    short[index] = true;
                    changed = true;
                }
            }
            if !changed {
                return (offsets, short);
            }
        }
    }

    fn offsets_with(&self, short: &[bool]) -> Vec<u32> {
        let mut offsets = Vec::with_capacity(self.entries.len() + 1);
        let mut position = 0u32;
        for (index, entry) in self.entries.iter().enumerate() {
            offsets.push(position);
            position += if short[index] {
                2
            } else {
                size_of_instruction(entry.instruction)
            };
        }
        offsets.push(position);
        offsets
    }

    fn target(&self, label: Label, offsets: &[u32]) -> u32 {
        let index = self.labels[label.0].expect("every label must be marked before layout");
        offsets[index]
    }

    fn encode(
        &self,
        instruction: Instruction,
        offsets: &[u32],
        start: usize,
        short: bool,
        code: &mut Vec<u8>,
    ) {
        use Instruction as I;

        // A branch offset counts from the instruction *after* the branch. Both
        // opcodes are passed rather than derived from one another: `br.s` sits
        // below `br` and the others below theirs, but `leave.s` sits *above*
        // `leave`, so arithmetic on the opcode would be wrong exactly once.
        let branch = |code: &mut Vec<u8>, long: u8, brief: u8, label: Label| {
            let width = if short { 2 } else { 5 };
            code.push(if short { brief } else { long });
            let next = start as i64 + width;
            let delta = i64::from(self.target(label, offsets)) - next;
            if short {
                code.push(delta as u8);
            } else {
                code.extend_from_slice(&(delta as i32).to_le_bytes());
            }
        };

        match instruction {
            I::LoadArgument(index) => match index {
                0..=3 => code.push(0x02 + index as u8),
                4..=255 => code.extend_from_slice(&[0x0E, index as u8]),
                _ => {
                    code.extend_from_slice(&[0xFE, 0x09]);
                    code.extend_from_slice(&index.to_le_bytes());
                }
            },
            I::StoreArgument(index) => {
                if index <= 255 {
                    code.extend_from_slice(&[0x10, index as u8]);
                } else {
                    code.extend_from_slice(&[0xFE, 0x0B]);
                    code.extend_from_slice(&index.to_le_bytes());
                }
            }
            I::LoadLocal(index) => match index {
                0..=3 => code.push(0x06 + index as u8),
                4..=255 => code.extend_from_slice(&[0x11, index as u8]),
                _ => {
                    code.extend_from_slice(&[0xFE, 0x0C]);
                    code.extend_from_slice(&index.to_le_bytes());
                }
            },
            I::StoreLocal(index) => match index {
                0..=3 => code.push(0x0A + index as u8),
                4..=255 => code.extend_from_slice(&[0x13, index as u8]),
                _ => {
                    code.extend_from_slice(&[0xFE, 0x0E]);
                    code.extend_from_slice(&index.to_le_bytes());
                }
            },
            I::LoadArgumentAddress(index) => {
                if index <= 255 {
                    code.extend_from_slice(&[0x0F, index as u8]);
                } else {
                    code.extend_from_slice(&[0xFE, 0x0A]);
                    code.extend_from_slice(&index.to_le_bytes());
                }
            }
            I::LoadLocalAddress(index) => {
                if index <= 255 {
                    code.extend_from_slice(&[0x12, index as u8]);
                } else {
                    code.extend_from_slice(&[0xFE, 0x0D]);
                    code.extend_from_slice(&index.to_le_bytes());
                }
            }
            I::LoadNull => code.push(0x14),
            I::LoadInt32(value) => match value {
                -1..=8 => code.push((0x16 + value) as u8),
                -128..=127 => code.extend_from_slice(&[0x1F, value as u8]),
                _ => {
                    code.push(0x20);
                    code.extend_from_slice(&value.to_le_bytes());
                }
            },
            I::LoadInt64(value) => {
                code.push(0x21);
                code.extend_from_slice(&value.to_le_bytes());
            }
            // Every NaN is written as the one the hardware makes of `0.0 /
            // 0.0`, as `csc` normalizes them: which NaN a constant folded to
            // is otherwise the compiler's accident, and code can see its bits.
            I::LoadFloat32(value) => {
                code.push(0x22);
                let bits = if value.is_nan() {
                    0xFFC0_0000
                } else {
                    value.to_bits()
                };
                code.extend_from_slice(&bits.to_le_bytes());
            }
            I::LoadFloat64(value) => {
                code.push(0x23);
                let bits = if value.is_nan() {
                    0xFFF8_0000_0000_0000
                } else {
                    value.to_bits()
                };
                code.extend_from_slice(&bits.to_le_bytes());
            }
            I::Nop => code.push(0x00),
            I::Dup => code.push(0x25),
            I::Pop => code.push(0x26),
            I::Call(token) => token_op(code, 0x28, token),
            I::CallIndirect(token) => token_op(code, 0x29, token),
            I::Ret => code.push(0x2A),
            I::Branch(label) => branch(code, 0x38, 0x2B, label),
            I::BranchIfFalse(label) => branch(code, 0x39, 0x2C, label),
            I::BranchIfTrue(label) => branch(code, 0x3A, 0x2D, label),
            I::Leave(label) => branch(code, 0xDD, 0xDE, label),
            I::EndFinally => code.push(0xDC),
            I::EndFilter => code.extend_from_slice(&[0xFE, 0x11]),
            I::Add => code.push(0x58),
            I::Subtract => code.push(0x59),
            I::Multiply => code.push(0x5A),
            I::Divide => code.push(0x5B),
            I::DivideUnsigned => code.push(0x5C),
            I::Remainder => code.push(0x5D),
            I::RemainderUnsigned => code.push(0x5E),
            I::And => code.push(0x5F),
            I::Or => code.push(0x60),
            I::Xor => code.push(0x61),
            I::ShiftLeft => code.push(0x62),
            I::ShiftRight => code.push(0x63),
            I::ShiftRightUnsigned => code.push(0x64),
            I::Negate => code.push(0x65),
            I::Not => code.push(0x66),
            I::ConvertI1 => code.push(0x67),
            I::ConvertI2 => code.push(0x68),
            I::ConvertI4 => code.push(0x69),
            I::ConvertI8 => code.push(0x6A),
            I::ConvertR4 => code.push(0x6B),
            I::ConvertR8 => code.push(0x6C),
            I::ConvertU4 => code.push(0x6D),
            I::ConvertU8 => code.push(0x6E),
            I::ConvertRUnsigned => code.push(0x76),
            I::AddOvf => code.push(0xD6),
            I::AddOvfUn => code.push(0xD7),
            I::MultiplyOvf => code.push(0xD8),
            I::MultiplyOvfUn => code.push(0xD9),
            I::SubtractOvf => code.push(0xDA),
            I::SubtractOvfUn => code.push(0xDB),
            I::ConvertOvfI1 => code.push(0xB3),
            I::ConvertOvfU1 => code.push(0xB4),
            I::ConvertOvfI2 => code.push(0xB5),
            I::ConvertOvfU2 => code.push(0xB6),
            I::ConvertOvfI4 => code.push(0xB7),
            I::ConvertOvfU4 => code.push(0xB8),
            I::ConvertOvfI8 => code.push(0xB9),
            I::ConvertOvfU8 => code.push(0xBA),
            I::ConvertOvfI1Un => code.push(0x82),
            I::ConvertOvfI2Un => code.push(0x83),
            I::ConvertOvfI4Un => code.push(0x84),
            I::ConvertOvfI8Un => code.push(0x85),
            I::ConvertOvfU1Un => code.push(0x86),
            I::ConvertOvfU2Un => code.push(0x87),
            I::ConvertOvfU4Un => code.push(0x88),
            I::ConvertOvfU8Un => code.push(0x89),
            I::ConvertOvfI => code.push(0xD4),
            I::ConvertOvfU => code.push(0xD5),
            I::ConvertOvfIUn => code.push(0x8A),
            I::ConvertOvfUUn => code.push(0x8B),
            I::ConvertI => code.push(0xD3),
            I::ConvertU => code.push(0xE0),
            I::LocalAlloc => code.extend_from_slice(&[0xFE, 0x0F]),
            I::ArgList => code.extend_from_slice(&[0xFE, 0x00]),
            I::MakeRefAny(token) => token_op(code, 0xC6, token),
            I::RefAnyValue(token) => token_op(code, 0xC2, token),
            I::RefAnyType => code.extend_from_slice(&[0xFE, 0x1D]),
            I::CallVirtual(token) => token_op(code, 0x6F, token),
            I::LoadString(token) => token_op(code, 0x72, token),
            I::NewObject(token) => token_op(code, 0x73, token),
            I::CastClass(token) => token_op(code, 0x74, token),
            I::IsInstance(token) => token_op(code, 0x75, token),
            I::UnboxAny(token) => token_op(code, 0xA5, token),
            I::SizeOf(token) => {
                code.extend_from_slice(&[0xFE, 0x1C]);
                code.extend_from_slice(&token.0.to_le_bytes());
            }
            I::Throw => code.push(0x7A),
            I::Rethrow => code.extend_from_slice(&[0xFE, 0x1A]),
            I::LoadField(token) => token_op(code, 0x7B, token),
            I::StoreField(token) => token_op(code, 0x7D, token),
            I::LoadStaticField(token) => token_op(code, 0x7E, token),
            I::LoadStaticFieldAddress(token) => token_op(code, 0x7F, token),
            I::StoreStaticField(token) => token_op(code, 0x80, token),
            I::Box(token) => token_op(code, 0x8C, token),
            I::NewArray(token) => token_op(code, 0x8D, token),
            I::LoadLength => code.push(0x8E),
            I::StoreElementRef => code.push(0xA2),
            I::LoadElementI1 => code.push(0x90),
            I::LoadElementU1 => code.push(0x91),
            I::LoadElementI2 => code.push(0x92),
            I::LoadElementU2 => code.push(0x93),
            I::LoadElementI4 => code.push(0x94),
            I::LoadElementU4 => code.push(0x95),
            I::LoadElementI8 => code.push(0x96),
            I::LoadElementR4 => code.push(0x98),
            I::LoadElementR8 => code.push(0x99),
            I::LoadElementRef => code.push(0x9A),
            I::StoreElementI1 => code.push(0x9C),
            I::StoreElementI2 => code.push(0x9D),
            I::StoreElementI4 => code.push(0x9E),
            I::StoreElementI8 => code.push(0x9F),
            I::StoreElementR4 => code.push(0xA0),
            I::StoreElementR8 => code.push(0xA1),
            I::LoadElement(token) => token_op(code, 0xA3, token),
            I::StoreElement(token) => token_op(code, 0xA4, token),
            I::LoadToken(token) => token_op(code, 0xD0, token),
            I::ConvertU2 => code.push(0xD1),
            I::ConvertU1 => code.push(0xD2),
            I::CompareEqual => code.extend_from_slice(&[0xFE, 0x01]),
            I::CompareGreater => code.extend_from_slice(&[0xFE, 0x02]),
            I::CompareGreaterUnsigned => code.extend_from_slice(&[0xFE, 0x03]),
            I::CompareLess => code.extend_from_slice(&[0xFE, 0x04]),
            I::CompareLessUnsigned => code.extend_from_slice(&[0xFE, 0x05]),
            I::InitObject(token) => {
                code.extend_from_slice(&[0xFE, 0x15]);
                code.extend_from_slice(&token.0.to_le_bytes());
            }
            I::LoadFunction(token) => {
                code.extend_from_slice(&[0xFE, 0x06]);
                code.extend_from_slice(&token.0.to_le_bytes());
            }
            I::LoadIndirect(kind) => match kind {
                IndirectKind::Object(token) => token_op(code, 0x71, token),
                other => code.push(match other {
                    IndirectKind::I1 => 0x46,
                    IndirectKind::U1 => 0x47,
                    IndirectKind::I2 => 0x48,
                    IndirectKind::U2 => 0x49,
                    IndirectKind::I4 => 0x4A,
                    IndirectKind::I8 => 0x4C,
                    IndirectKind::R4 => 0x4E,
                    IndirectKind::R8 => 0x4F,
                    _ => 0x50,
                }),
            },
            I::StoreIndirect(kind) => match kind {
                IndirectKind::Object(token) => token_op(code, 0x81, token),
                other => code.push(match other {
                    IndirectKind::I1 | IndirectKind::U1 => 0x52,
                    IndirectKind::I2 | IndirectKind::U2 => 0x53,
                    IndirectKind::I4 => 0x54,
                    IndirectKind::I8 => 0x55,
                    IndirectKind::R4 => 0x56,
                    IndirectKind::R8 => 0x57,
                    _ => 0x51,
                }),
            },
            I::LoadElementAddress(token) => token_op(code, 0x8F, token),
            I::LoadFieldAddress(token) => token_op(code, 0x7C, token),
            I::LoadVirtualFunction(token) => {
                code.extend_from_slice(&[0xFE, 0x07]);
                code.extend_from_slice(&token.0.to_le_bytes());
            }
            I::Readonly => code.extend_from_slice(&[0xFE, 0x1E]),
            I::Constrained(token) => {
                code.extend_from_slice(&[0xFE, 0x16]);
                code.extend_from_slice(&token.0.to_le_bytes());
            }
        }
    }

    /// The deepest the evaluation stack gets.
    ///
    /// Walking the instructions in order is not enough: a branch carries a
    /// depth to its target, and the target may sit before the branch. The
    /// depths are propagated to a fixed point instead, which is what a
    /// verifier does when it checks the number this produces.
    /// How deep the stack is where the flow falls off the end of the
    /// stream, or `None` where nothing reaches it.
    ///
    /// An expression-bodied lambda leaves its value there for the `ret`
    /// that closes the body; a value-returning method whose end is reached
    /// with nothing on the stack is one the language proved never gets
    /// there.
    #[must_use]
    pub(crate) fn end_depth(&self) -> Option<i32> {
        let end = self.entries.len();
        let mut depths: HashMap<usize, i32> = HashMap::new();
        let mut pending = vec![(0usize, 0i32)];
        for (label, depth) in &self.entry_points {
            if let Some(index) = self.labels[label.0] {
                pending.push((index, *depth));
            }
        }
        let mut at_end = None;
        while let Some((index, depth)) = pending.pop() {
            if depth > MAX_STACK_DEPTH {
                break;
            }
            if index >= end {
                at_end = Some(at_end.map_or(depth, |seen: i32| seen.max(depth)));
                continue;
            }
            match depths.get(&index) {
                Some(seen) if *seen >= depth => continue,
                _ => {}
            }
            depths.insert(index, depth);
            let entry = self.entries[index];
            let after = depth + entry.effect;
            if let Some(label) = branch_target(entry.instruction)
                && let Some(target) = self.labels[label.0]
            {
                let arriving = if matches!(entry.instruction, Instruction::Leave(_)) {
                    0
                } else {
                    after
                };
                pending.push((target, arriving));
            }
            if entry.instruction.falls_through() {
                pending.push((index + 1, after));
            }
        }
        at_end
    }

    fn max_stack(&self) -> u16 {
        let mut depths: HashMap<usize, i32> = HashMap::new();
        let mut pending = vec![(0usize, 0i32)];
        for (label, depth) in &self.entry_points {
            if let Some(index) = self.labels[label.0] {
                pending.push((index, *depth));
            }
        }
        let mut deepest = 0i32;

        while let Some((index, depth)) = pending.pop() {
            // A correct lowering never leaves anything behind across a branch,
            // so a depth this large means the emitter left a stray value on
            // the stack in a loop. Stopping here turns that into an assembly
            // the runtime rejects, which is a bad outcome; not stopping turns
            // it into a compiler that never finishes, which is a worse one.
            if depth > MAX_STACK_DEPTH {
                debug_assert!(
                    false,
                    "the evaluation stack grows without bound: something is \
                     left on it each time round a loop"
                );
                break;
            }
            if index >= self.entries.len() {
                continue;
            }
            // A position reached twice with the same depth has nothing new to
            // say; with a greater one it does.
            match depths.get(&index) {
                Some(seen) if *seen >= depth => continue,
                _ => {}
            }
            depths.insert(index, depth);
            deepest = deepest.max(depth);

            let entry = self.entries[index];
            let after = depth + entry.effect;
            deepest = deepest.max(after);
            if let Some(label) = branch_target(entry.instruction) {
                let target = self.labels[label.0].expect("every label must be marked");
                // `leave` empties the stack on its way out of the region.
                let arriving = if matches!(entry.instruction, Instruction::Leave(_)) {
                    0
                } else {
                    after
                };
                pending.push((target, arriving));
            }
            if entry.instruction.falls_through() {
                pending.push((index + 1, after));
            }
        }

        u16::try_from(deepest.max(0)).unwrap_or(u16::MAX)
    }
}

/// How deep the evaluation stack may get: what a method header can say
/// (`maxstack` is sixteen bits). Real IL stays in single digits, and
/// anything past this is a bug in the emitter rather than a program — but
/// a few hundred is a program: `F(1, F(1, F(1, …)))` holds one argument per
/// level, an array initializer nested as deep three, and the parser lets
/// source nest a thousand levels.
const MAX_STACK_DEPTH: i32 = u16::MAX as i32;

const fn branch_target(instruction: Instruction) -> Option<Label> {
    match instruction {
        Instruction::Branch(label)
        | Instruction::BranchIfFalse(label)
        | Instruction::BranchIfTrue(label)
        | Instruction::Leave(label) => Some(label),
        _ => None,
    }
}

fn token_op(code: &mut Vec<u8>, opcode: u8, token: Token) {
    code.push(opcode);
    code.extend_from_slice(&token.0.to_le_bytes());
}

fn size_of_instruction(instruction: Instruction) -> u32 {
    use Instruction as I;
    match instruction {
        I::LoadArgument(index) | I::LoadLocal(index) | I::StoreLocal(index) => match index {
            0..=3 => 1,
            4..=255 => 2,
            _ => 4,
        },
        I::StoreArgument(index) | I::LoadArgumentAddress(index) | I::LoadLocalAddress(index) => {
            if index <= 255 {
                2
            } else {
                4
            }
        }
        I::LoadInt32(value) => match value {
            -1..=8 => 1,
            -128..=127 => 2,
            _ => 5,
        },
        I::LoadInt64(_) | I::LoadFloat64(_) => 9,
        I::LoadFloat32(_) => 5,
        I::Branch(_) | I::BranchIfFalse(_) | I::BranchIfTrue(_) | I::Leave(_) => 5,
        I::EndFilter => 2,
        I::Call(_)
        | I::CallVirtual(_)
        | I::CallIndirect(_)
        | I::NewObject(_)
        | I::LoadString(_)
        | I::LoadField(_)
        | I::StoreField(_)
        | I::LoadStaticField(_)
        | I::StoreStaticField(_)
        | I::LoadStaticFieldAddress(_)
        | I::Box(_)
        | I::UnboxAny(_)
        | I::CastClass(_)
        | I::IsInstance(_)
        | I::LoadToken(_)
        | I::NewArray(_)
        | I::LoadElement(_)
        | I::StoreElement(_) => 5,
        I::InitObject(_)
        | I::LoadFunction(_)
        | I::LoadVirtualFunction(_)
        | I::Constrained(_)
        | I::SizeOf(_) => 6,
        I::Rethrow | I::LocalAlloc | I::RefAnyType | I::Readonly | I::ArgList => 2,
        I::MakeRefAny(_) | I::RefAnyValue(_) => 5,
        I::LoadElementAddress(_) | I::LoadFieldAddress(_) => 5,
        I::LoadIndirect(IndirectKind::Object(_)) | I::StoreIndirect(IndirectKind::Object(_)) => 5,
        I::CompareEqual
        | I::CompareGreater
        | I::CompareGreaterUnsigned
        | I::CompareLess
        | I::CompareLessUnsigned => 2,
        _ => 1,
    }
}

/// A method body, encoded the way §II.25.4 lays one out.
///
/// The tiny header is available only when there are no locals, the stack stays
/// within eight slots and the code is shorter than 64 bytes; anything else
/// needs the fat header, which is also the only one that can name a local
/// signature.
#[must_use]
pub(crate) fn method_body(
    code: &[u8],
    max_stack: u16,
    locals: Option<Token>,
    regions: &[ResolvedRegion],
) -> Vec<u8> {
    let tiny = locals.is_none() && regions.is_empty() && max_stack <= 8 && code.len() < 64;
    let mut body = Vec::with_capacity(code.len() + 12);
    if tiny {
        body.push(0x02 | ((code.len() as u8) << 2));
        body.extend_from_slice(code);
        return body;
    }

    // Fat format, header three double words long, and `MoreSects` when there
    // are handlers: the exception table follows the code.
    // `0x10` asks the runtime to zero the locals — and what `localloc` hands
    // out — before the body runs, which is what C# promises for both.
    let flags = 0x3013u16 | if regions.is_empty() { 0 } else { 0x0008 };
    body.extend_from_slice(&flags.to_le_bytes());
    body.extend_from_slice(&max_stack.to_le_bytes());
    body.extend_from_slice(&(code.len() as u32).to_le_bytes());
    body.extend_from_slice(&locals.map_or(0, |token| token.0).to_le_bytes());
    body.extend_from_slice(code);

    if regions.is_empty() {
        return body;
    }
    // The section starts on a four-byte boundary after the code.
    while body.len() % 4 != 0 {
        body.push(0);
    }
    // Kind 0x01 is an exception table and 0x40 says the fat form, whose
    // clauses are 24 bytes and whose offsets are not limited to 16 bits.
    let data_size = 4 + regions.len() * 24;
    body.push(0x41);
    body.extend_from_slice(&(data_size as u32).to_le_bytes()[..3]);
    for region in regions {
        let (flags, class_or_filter) = match region.kind {
            ResolvedKind::Catch(token) => (0x0000u32, token.0),
            ResolvedKind::Filter(offset) => (0x0001, offset),
            ResolvedKind::Finally => (0x0002, 0),
        };
        body.extend_from_slice(&flags.to_le_bytes());
        body.extend_from_slice(&region.try_offset.to_le_bytes());
        body.extend_from_slice(&region.try_length.to_le_bytes());
        body.extend_from_slice(&region.handler_offset.to_le_bytes());
        body.extend_from_slice(&region.handler_length.to_le_bytes());
        body.extend_from_slice(&class_or_filter.to_le_bytes());
    }
    body
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_branch_past_a_return_does_not_reach_the_end() {
        // `if (c) return a; else return b;`: the `br` after the first
        // return targets the end and is never run.
        let mut stream = InstructionStream::new();
        let otherwise = stream.label();
        let end = stream.label();
        stream.emit(Instruction::LoadArgument(0));
        stream.emit(Instruction::BranchIfFalse(otherwise));
        stream.emit(Instruction::LoadInt32(1));
        stream.emit(Instruction::Ret);
        // Nothing reaches this point, so the branch past the `else` is
        // left out, and the end is not reached either.
        assert!(!stream.end_reachable());
        stream.mark(otherwise);
        stream.emit(Instruction::LoadInt32(2));
        stream.emit(Instruction::Ret);
        stream.mark(end);
        assert!(stream.ends_flow());

        // Had the dead branch been written, the label it names still needs
        // an instruction under it, or the branch points past the method.
        let mut stream = InstructionStream::new();
        let end = stream.label();
        stream.emit(Instruction::Ret);
        stream.emit(Instruction::Branch(end));
        stream.mark(end);
        assert!(!stream.end_reachable());
        assert!(!stream.ends_flow());

        // `if (c) return a;` on its own falls through to the end.
        let mut stream = InstructionStream::new();
        let end = stream.label();
        stream.emit(Instruction::LoadArgument(0));
        stream.emit(Instruction::BranchIfFalse(end));
        stream.emit(Instruction::LoadInt32(1));
        stream.emit(Instruction::Ret);
        stream.mark(end);
        assert!(!stream.ends_flow());
    }

    #[test]
    fn short_forms_are_used_where_they_fit() {
        let mut stream = InstructionStream::new();
        stream.emit(Instruction::LoadInt32(3));
        stream.emit(Instruction::LoadInt32(100));
        stream.emit(Instruction::LoadInt32(1000));
        stream.emit(Instruction::Ret);
        let (code, _, _) = stream.finish();
        assert_eq!(code[0], 0x19); // ldc.i4.3
        assert_eq!(&code[1..3], &[0x1F, 100]); // ldc.i4.s 100
        assert_eq!(code[3], 0x20); // ldc.i4 1000
        assert_eq!(&code[4..8], &1000i32.to_le_bytes());
    }

    #[test]
    fn a_branch_that_reaches_is_shrunk() {
        let mut stream = InstructionStream::new();
        let target = stream.label();
        stream.emit(Instruction::Branch(target));
        stream.emit(Instruction::Pop);
        stream.mark(target);
        stream.emit(Instruction::Ret);
        let (code, _, _) = stream.finish();
        // `br.s` is two bytes, and one one-byte instruction stands between it
        // and the target.
        assert_eq!(code[0], 0x2B);
        assert_eq!(code[1] as i8, 1);
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn a_branch_that_does_not_reach_stays_long() {
        let mut stream = InstructionStream::new();
        let target = stream.label();
        stream.emit(Instruction::Branch(target));
        // Two hundred one-byte instructions put the target out of range of a
        // signed byte.
        for _ in 0..200 {
            stream.emit(Instruction::Pop);
        }
        stream.mark(target);
        stream.emit(Instruction::Ret);
        let (code, _, _) = stream.finish();
        assert_eq!(code[0], 0x38);
        assert_eq!(i32::from_le_bytes(code[1..5].try_into().unwrap()), 200);
    }

    #[test]
    fn shrinking_runs_to_a_fixed_point() {
        // The outer branch only reaches once the inner one has been shrunk,
        // which is why one pass is not enough.
        let mut stream = InstructionStream::new();
        let outer = stream.label();
        let inner = stream.label();
        stream.emit(Instruction::Branch(outer));
        for _ in 0..40 {
            stream.emit(Instruction::Branch(inner));
        }
        stream.mark(inner);
        for _ in 0..40 {
            stream.emit(Instruction::Pop);
        }
        stream.mark(outer);
        stream.emit(Instruction::Ret);
        let (code, _, _) = stream.finish();
        // With every branch long the outer one covers 240 bytes and cannot be
        // short; once the forty inner ones have shrunk it covers 120 and can.
        assert_eq!(code.len(), 41 * 2 + 40 + 1);
        assert_eq!(code[0], 0x2B);
    }

    #[test]
    fn max_stack_follows_branches_backwards() {
        // A loop whose body pushes before the branch that reaches its head.
        let mut stream = InstructionStream::new();
        let head = stream.label();
        stream.mark(head);
        stream.emit(Instruction::LoadInt32(1));
        stream.emit(Instruction::LoadInt32(2));
        stream.emit(Instruction::Add);
        stream.emit(Instruction::BranchIfTrue(head));
        stream.emit(Instruction::Ret);
        let (_, max_stack, _) = stream.finish();
        assert_eq!(max_stack, 2);
    }

    #[test]
    fn a_call_says_what_it_does_to_the_stack() {
        let mut stream = InstructionStream::new();
        stream.emit(Instruction::LoadInt32(1));
        stream.emit(Instruction::LoadInt32(2));
        stream.call_effect(Instruction::Call(Token::new(0x0A, 1)), 2, 1);
        stream.emit(Instruction::Ret);
        let (_, max_stack, _) = stream.finish();
        assert_eq!(max_stack, 2);
    }

    #[test]
    fn a_tiny_header_is_used_when_it_fits() {
        let body = method_body(&[0x2A], 1, None, &[]);
        assert_eq!(body, vec![(1 << 2) | 0x02, 0x2A]);
    }

    #[test]
    fn locals_force_the_fat_header() {
        let body = method_body(&[0x2A], 1, Some(Token::new(0x11, 1)), &[]);
        // Fat, three words long, and asking for the locals to be zeroed.
        assert_eq!(u16::from_le_bytes([body[0], body[1]]), 0x3013);
        assert_eq!(u32::from_le_bytes(body[4..8].try_into().unwrap()), 1);
        assert_eq!(body[12], 0x2A);
    }
}
