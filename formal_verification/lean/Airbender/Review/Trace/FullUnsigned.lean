import Airbender.Review.Trace.Modular.ExternalCalls
import Airbender.Review.Trace.UnifiedReduced.DelegationUse
import Airbender.Review.Circuits.Keccak.SplitCall
import Airbender.Review.Helpers.Decoder.ProgramRows

namespace Airbender.FullUnsigned
open Trace Reference.RiscV.Sail Reference.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Production full unsigned calls besides the blessed split Keccak workers.
Special5 remains an explicit public exclusion; BLAKE2 G belongs to unified. -/
def standardCall : Delegation.Family → Prop
  | .bigint | .blakeRound => True
  | .blakeG | .keccak => False

structure Program where
  ordinary : List PooledProgramEntry
  callers : List Delegation.Caller.ProgramEntry
  bundles : List UnifiedReduced.Caller.DelegationUse.Bundle
  splitCallers : List Keccak.Split.Caller.ProgramEntry
  splitBundles : List Keccak.Split.Bundle

/-- Construct typed caller registries from public text, retaining the original
Sail instruction. An effectful or unsupported decode contributes no entry. -/
def entriesWith {Family : Type}
    (fields : SailRV32.instruction → Option (DecoderData Family))
    (text : List (BitVec 32)) : List (Trace.ProgramEntry Family) :=
  text.zipIdx.filterMap fun (bits, index) => do
    let instruction ← match SailRV32.Functions.encdec_backwards bits with
      | .pure instruction => some instruction
      | .impure _ _ => none
    let data ← fields instruction
    pure ⟨BitVec.ofNat 32 (4 * index), bits, instruction, data⟩

def standardDecoderFields (instruction : SailRV32.instruction) :
    Option (DecoderData Delegation.Family) := do
  let data ← Delegation.Caller.decoderFields instruction
  match data.family with
  | .bigint | .blakeRound => some data
  | .blakeG | .keccak => none

/-- All executable registries are functions of the supplied public text.
Only public wrapper partitions are supplied independently. -/
def Program.ofText (initial : State) (text : List (BitVec 32))
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle)
    (splitBundles : List Keccak.Split.Bundle) : Program where
  ordinary := NativeDecoder.ProgramRows.programOf .fullUnsigned initial text
  callers := entriesWith standardDecoderFields text
  bundles := bundles
  splitCallers := entriesWith Keccak.Split.Caller.decoderFields text
  splitBundles := splitBundles

/-- The only excluded Keccak protocol is the public special5 CSR. The three
split CSRs remain in `Program.ofText` and `Step`. -/
def NoSpecial5Call (initial : State) (text : List (BitVec 32)) : Prop :=
  NativeDecoder.ProgramRows.NoSpecial5Call
    (NativeDecoder.ProgramRows.callerProgramOf .fullUnsigned initial text)

def SplitCallStep (callers : List Keccak.Split.Caller.ProgramEntry)
    (before after : State × Nat) : Prop :=
  before.2 = after.2 ∧
    ∃ entry ∈ callers,
      entry.SourceWith before.1 Keccak.Split.Caller.decoderFields ∧
      run (SailRV32.Functions.get_arch_pc ()) before.1 = .ok entry.pc before.1 ∧
      Keccak.Split.Call.Retires entry.data.family before.1 after.1

/-- One full unsigned stream relation contains the six ordinary families,
modular operations, nondeterminism, bigint and extended-round calls, and each
of the three split Keccak calls. Every nonread step preserves stream position. -/
def Step (stream : List (BitVec 32)) (program : Program)
    (before after : State × Nat) : Prop :=
  AddSub.Modular.External.Caller.Step standardCall stream program.ordinary
      program.callers before after ∨
    SplitCallStep program.splitCallers before after

def Reachable (stream : List (BitVec 32)) (program : Program)
    (initial : State) (state : State × Nat) : Prop :=
  Relation.ReflTransGen (Step stream program) (initial, 0) state

/-- Exact public wrapper syntax and coverage for both worker protocols. -/
structure Shapes (program : Program) : Prop where
  standard : ∀ entry ∈ program.callers, standardCall entry.data.family
  kinds : ∀ bundle ∈ program.bundles,
    standardCall bundle.kind.family
  bounds : ∀ bundle ∈ program.bundles,
    bundle.start.toNat % 4 = 0 ∧
      bundle.start.toNat + 4 * bundle.instructions ≤ ROM.limit
  calls : ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.kind.calls,
    ∃ entry ∈ program.callers,
      entry.pc = bundle.callPC index.val ∧
      entry.data.family = bundle.kind.family ∧
      entry.instruction = UnifiedReduced.Caller.DelegationUse.csrInstruction bundle.kind.family
  coverage : ∀ entry ∈ program.callers,
    ∃ bundle ∈ program.bundles, ∃ index : Fin bundle.kind.calls,
      entry.pc = bundle.callPC index.val ∧ entry.data.family = bundle.kind.family
  disjoint : ∀ one ∈ program.bundles, ∀ two ∈ program.bundles,
    ∀ i : Fin one.instructions, ∀ j : Fin two.instructions,
      one.instructionPC i.val = two.instructionPC j.val → one = two ∧ i.val = j.val
  split : Keccak.Split.Shapes program.splitCallers program.splitBundles
  separate : ∀ standard ∈ program.bundles, ∀ split ∈ program.splitBundles,
    ∀ i : Fin standard.instructions, ∀ j : Fin 361,
      standard.instructionPC i.val ≠ split.callPC j.val

/-- Public supported use is checked along every possible external stream.
Only code, reference reachability, control registers and aligned pointers occur
here; no worker result, native assignment or witness schedule is assumed. -/
structure ValidDelegationUse (program : Program) (initial : State) : Prop where
  shapes : Shapes program
  initialEntry : ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.instructions,
    0 < index.val → ¬ UnifiedReduced.Caller.DelegationUse.AtPC initial
      (bundle.instructionPC index.val)
  entry : ∀ stream before after, Reachable stream program initial before →
    Step stream program before after →
    ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.instructions,
      0 < index.val →
      UnifiedReduced.Caller.DelegationUse.AtPC after.1 (bundle.instructionPC index.val) →
      UnifiedReduced.Caller.DelegationUse.AtPC before.1
        (bundle.instructionPC (index.val - 1))
  arguments : ∀ stream state, Reachable stream program initial state →
    ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.kind.calls,
      UnifiedReduced.Caller.DelegationUse.AtPC state.1 (bundle.callPC index.val) →
      UnifiedReduced.Caller.DelegationUse.ArgumentsAt bundle index.val state.1
  splitInitialEntry : Keccak.Split.SafeInitialEntry program.splitBundles initial
  splitEntry : ∀ stream before after, Reachable stream program initial before →
    Step stream program before after →
    ∀ bundle ∈ program.splitBundles, ∀ index : Fin 361,
      0 < index.val → Keccak.Split.AtPC after.1 (bundle.callPC index.val) →
      Keccak.Split.AtPC before.1 (bundle.callPC (index.val - 1))
  splitArguments : ∀ stream state, Reachable stream program initial state →
    ∀ bundle ∈ program.splitBundles, ∀ index : Fin 361,
      Keccak.Split.AtPC state.1 (bundle.callPC index.val) →
      Keccak.Split.ArgumentsAt index.val state.1

/-- The full machine retains the existing terminal PC, tracked-memory and
external-stream observations. Split calls participate in this same execution. -/
def Realizes {p : Nat} [Fact p.Prime] (stream : List (BitVec 32))
    (program : Program) (trace : PooledTrace p) (initial : State)
    (cells : List Cell) (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ after, Relation.ReflTransGen (Step stream program)
      (initial, 0) (after, NonDeterminism.Pooled.readCount trace) ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (view sink).word.toBitVec after

end Airbender.FullUnsigned
