import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.Blake2G.Theorems
import Airbender.Review.Trace.Workers.Blake2G.Theorems
import Airbender.Proofs.Blake2G.WorkVectorBinding
import Airbender.Proofs.Blake2G.BlockFrame
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


theorem Native.call_blocks_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {reduced : Bool} (accepted : Delegation.MemoryAccepted data)
    (inputs : CallInputs data initial cells reduced) :
    ∃ statePointer messagePointer, BlockMapping initial cells statePointer messagePointer := by
  obtain ⟨state, message, stateRead, messageRead, stateAligned, messageAligned, separate, initialized⟩ :=
    Proofs.call_block_domain hp inverse accepted inputs.toBoundaryInputs
  exact ⟨state, message, ⟨⟨stateRead, messageRead⟩, ⟨stateAligned, messageAligned⟩, separate, initialized⟩⟩



theorem call_control_soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {reduced : Bool} (accepted : Delegation.MemoryAccepted data)
    (inputs : CallInputs data initial cells reduced) : CallSchedule data reduced := by
  obtain ⟨ordered, matching, clocks, controls, sink, member, address, final⟩ :=
    Proofs.ordered_controls hp accepted inputs.toBoundaryInputs
  have reset : controlAt reduced data.rows.length = controlAt reduced 0 := by
    rw [inputs.calls]
    cases reduced <;> rfl
  exact ⟨ordered, matching, clocks, controls, sink, member, address, final.trans reset⟩


theorem Native.call_execution [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
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
    Proofs.call_pointers clockBound accepted inputs.toBoundaryInputs
  exact ⟨execution, call_control_soundness clockBound accepted inputs,
    ⟨statePointer, messagePointer, stateRead, messageRead, pointers⟩,
    fun row member => effects row member (inputs.family row member)⟩

namespace Row


theorem soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (compatible : SerializedInverse.Scale64 p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Row

namespace Control


theorem soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512) :
    Properties.Soundness (circuitModel (p := p)).relation spec :=
  Proofs.soundness hp

theorem babyBear_soundness :
    Properties.Soundness (circuitModel (p := babyBearModulus)).relation spec :=
  soundness (by decide)

end Control

namespace Addresses


theorem soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (compatible : SerializedInverse.Scale64 p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Addresses

namespace State


theorem soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 262144)
    (compatible : SerializedInverse.Scale64 p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end State

namespace Memory


theorem soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (inverse : SerializedInverse.Scale64 p) (data : Delegation.MemoryData p)
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

end Airbender.Blake2G.Native
