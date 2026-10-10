import Airbender.Proofs.UnifiedReduced.TraceSoundness
import Airbender.Proofs.UnifiedReduced.TriAdd
import Airbender.Proofs.UnifiedReduced.Trace
import Airbender.Proofs.UnifiedReduced.Values
import Airbender.Proofs.UnifiedReduced.History
import Airbender.Proofs.UnifiedReduced.Decoder
import Airbender.Proofs.BabyBear

namespace Airbender.UnifiedReduced
open Airbender.Reference.RiscV

/-- All unified rows advance four ticks and access each cell after its previous
    write. `accepted` checks imported equations and native state/memory matching;
    `boundary` bounds only the public starting clock and seed timestamps.
    Shared history derives every row's clock bounds and alignment internally.
    This covers all selectors; it does not yet prove their instruction semantics. -/
theorem native_clocks {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (boundary : Trace.ClockBoundary trace) :
    ∀ row ∈ trace.rows, Trace.ClockEffects row.columns row.assignment :=
  Trace.Proofs.trace_clocks hp inverse accepted boundary

/-- Every native register/RAM read, write and final token has bounded word limbs.
    `image` reads the public starting Sail cells; `accepted` binds the actual
    imported accesses through logical matching. Local range queries bound fresh
    results, while shared latest-write history supplies copied and incoming values.
    No operand range or expected read is a premise. Instruction/ABI soundness is separate. -/
theorem native_value_bounds {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (clocks : Trace.ClockBoundary trace)
    {before : Sail.State} {cells : List Trace.Cell}
    (image : Trace.initialImage before cells = some trace.initialMemory) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (Trace.readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (Trace.writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  Proofs.value_bounds hp inverse accepted clocks image

/-- Native accesses form a Clean-consistent latest-write/read history seeded by
    actual public Sail values. `distinct` excludes duplicate public cell entries;
    the circuit supplies ports and clocks, and logical matching links their tokens.
    The conclusion proves read consistency, without an expected-read premise. -/
theorem native_memory_history {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (clocks : Trace.ClockBoundary trace)
    {before : Sail.State} {cells : List Trace.Cell}
    (image : Trace.initialImage before cells = some trace.initialMemory)
    (distinct : cells.Nodup) : ∃ history, Trace.MemoryHistory trace history :=
  Proofs.memory_history hp inverse accepted clocks image distinct

/-- The initialized logical history executes as actual Sail cell reads/writes.
    Public initialization and original decoding supply the starting values and
    x0 rules; native constraints supply clocks and transfers. Expected reads,
    operand ranges and instruction results are not premises. `MemoryExecution`
    states the transport result; original ISA retirement is a separate claim. -/
theorem native_memory_execution [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    {initial : Sail.State} {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Trace.NativeInputs decoderFields trace initial cells program)
    (decoded : Decoded trace program) : MemoryExecution trace initial cells :=
  Proofs.memory_execution hp inverse accepted inputs decoded

/-- The native decoder query comes from public Sail bytes and the original
    decoder. Imported equations recover all nineteen selector bits; no decoded
    opcode, operand value or desired result is supplied as an assumption. -/
theorem fetched {p : Nat} [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    {before : Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (accepted : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (membership : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image accepted membership

/-- Standard arithmetic agrees with the original Sail register and PC effects.
    The per-row model keeps public initialization and program membership visible;
    shared native history derives operand/immediate/PC bounds, actual reads and
    x0 preprocessing. Other admitted selectors may participate in that history. -/
theorem soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.UnifiedTrace p) (initial : Sail.State) (cells : List Trace.Cell)
    (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec :=
  Proofs.trace_soundness hp inverse trace initial cells program

theorem babyBear_soundness (trace : Trace.UnifiedTrace babyBearModulus)
    (initial : Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec :=
  soundness (by decide) (by decide) trace initial cells program

/-- TRIADD follows the pinned project operation and Sail's native register/PC
    effects, including three-way aliasing, carry-two wraparound and x0 writes. -/
theorem TriAdd.soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (setup : Table (ZMod p) (fields 10)) :
    (TriAdd.circuitModel setup).SoundnessUnder TriAdd.InterfaceAssumptions TriAdd.spec :=
  Proofs.triadd_soundness hp setup

theorem TriAdd.babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 10)) :
    (TriAdd.circuitModel setup).SoundnessUnder TriAdd.InterfaceAssumptions TriAdd.spec :=
  TriAdd.soundness (by decide) setup

end Airbender.UnifiedReduced
