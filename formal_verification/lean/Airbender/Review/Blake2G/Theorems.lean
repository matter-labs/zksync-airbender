import Airbender.Proofs.Blake2G.NativeExecution
import Airbender.Proofs.Blake2G.CallHistory
import Airbender.Proofs.Blake2G.PointerHistory
import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.Blake2G.MemorySoundness
import Airbender.Proofs.Blake2G.Control
import Airbender.Proofs.Blake2G.Addresses
import Airbender.Proofs.Blake2G.State
import Airbender.Proofs.Blake2G.Row
import Airbender.Proofs.BabyBear

namespace Airbender.Blake2G

/-- Initialized x12 matching and imported controller lookups force the entire
    schedule of 56 or 80 calls and its terminal counter. The request-span and public
    starting mode are explicit; no later controls, bounds or reads are assumed. -/
theorem call_control_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {reduced : Bool} (accepted : Delegation.MemoryAccepted data)
    (inputs : CallInputs data initial cells reduced) : CallSchedule data reduced := by
  obtain ⟨ordered, matching, clocks, controls, sink, member, address, final⟩ :=
    Proofs.ordered_controls hp accepted inputs
  have reset : controlAt reduced data.rows.length = controlAt reduced 0 := by
    rw [inputs.calls]
    cases reduced <;> rfl
  exact ⟨ordered, matching, clocks, controls, sink, member, address, final.trans reset⟩

/-- Complete G request spans execute their actual ports in Sail memory,
    follow the derived controller schedule, retain public pointers and satisfy
    Clean's G relation. Work-vector composition and caller binding remain open. -/
theorem Native.call_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {reduced : Bool} (accepted : Delegation.MemoryAccepted data)
    (inputs : CallInputs data initial cells reduced) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data initial cells ∧ CallSchedule data reduced ∧
      CallPointers data initial ∧ ∀ row ∈ data.rows, spec (input row.assignment) (output row.assignment) := by
  have operation : Delegation.OperationInputs data initial cells Keccak.Controller.rows := by
    refine ⟨inputs.memory, inputs.tables, ?_, ?_⟩
    all_goals intro row member other; have := inputs.family row member; simp_all
  obtain ⟨execution, effects⟩ := Native.Proofs.operation_execution hp inverse accepted operation aligned
  have clockBound : 2 * Trace.timestampBase + 4 < p := by norm_num [Trace.timestampBase]; omega
  obtain ⟨statePointer, messagePointer, stateRead, messageRead, pointers, _, _⟩ :=
    Proofs.call_pointers clockBound accepted inputs
  exact ⟨execution, call_control_soundness clockBound accepted inputs,
    ⟨statePointer, messagePointer, stateRead, messageRead, pointers⟩,
    fun row member => effects row member (inputs.family row member)⟩

namespace Row

/-- Primary active-row claim: controller, complete G state update and six byte
    addresses for one assignment. Memory transport and setup provenance remain
    explicit interfaces; component claims below support reuse and inspection. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Row

/-- Imported G mixing agrees with Clean's reference, under the four documented
    input bounds. This does not assert control, address or memory-transport soundness. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := p) control).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.soundness hp compatible control

theorem babyBear_soundness (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := babyBearModulus) control).SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide) control

namespace Control

/-- The imported controller query enforces the modeled register update and
    all six word indices for active and inactive rows. The eight-bit ABI input
    domain and unproved Rust setup binding are explicit in the model. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) :
    Properties.Soundness (circuitModel (p := p)).relation spec :=
  Proofs.soundness hp

theorem babyBear_soundness :
    Properties.Soundness (circuitModel (p := babyBearModulus)).relation spec :=
  soundness (by decide)

end Control

namespace Addresses

/-- The six addresses described by imported memory metadata select the modeled
    controller's words within the ABI blocks. Pointer bounds and global memory
    transport remain external; alignment and offset bounds are proved locally. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Addresses

namespace State

/-- An active row agrees with Clean's G on all sixteen state words, under
    the explicit port/read/frame interface. Selected lanes are proved distinct
    from the modeled controller; global memory enforcement remains external. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end State

namespace Memory

/-- Clean's G reference follows from native constraints and initialized memory
    history. Public initialization, logical matching, caller-clock alignment and
    the modeled G table remain explicit; operand ranges are derived internally. -/
theorem soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Blake2G.spec :=
  Proofs.soundness hp inverse data before cells

theorem babyBear_soundness (data : Delegation.MemoryData babyBearModulus)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Blake2G.spec :=
  soundness (by decide) (by decide) data before cells

end Memory

end Airbender.Blake2G

namespace Airbender.Blake2G.Native

/-- Native G reads and writes agree with Clean's original G reference within
    actual Sail memory execution. Other families may share the initialized pool;
    shared operation/history helpers derive every operand bound. The remaining
    inputs are public state/alignment, modeled tables and caller/padding rules.
    Request/controller ABI and whole compression remain separate. -/
theorem operation_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.OperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment) :=
  Proofs.operation_execution hp inverse accepted inputs aligned

end Airbender.Blake2G.Native
