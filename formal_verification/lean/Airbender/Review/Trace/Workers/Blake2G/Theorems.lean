import Airbender.Proofs.Blake2G.Windows
import Airbender.Proofs.Blake2G.WorkVectorBinding
import Airbender.Proofs.Blake2G.NativeExecution
import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.BabyBear

namespace Airbender.Blake2G

/-- The complete native G span updates its actual RAM work vector through
    the pinned 56/80-call schedule and original Clean G. `WordMapping` exposes
    successful initial/final reads; shared `TraceMapping` binds the same final
    state to every native access and terminal token. Message preservation,
    intermediate states, ranges and frames are proved internally. Caller
    request binding and modeled-table fidelity remain separate boundaries. -/
theorem Native.workvector_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {reduced : Bool} (accepted : Delegation.MemoryAccepted data)
    (inputs : CallInputs data initial cells reduced) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : Reference.RiscV.Sail.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.WordMapping initial after statePointer messagePointer input message output ∧
        Delegation.TraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message :=
  Proofs.workvector_binding hp inverse accepted inputs aligned

/-- The complete G reference binds actual boundary reads and the final Sail state,
    retaining native seed timestamps. Controls, pointers and intermediate states
    follow from accepted history and the public complete-span ABI. -/
theorem Native.workvector_boundary_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {reduced : Bool} (accepted : Delegation.MemoryAccepted data)
    (inputs : NativeCallInputs data initial cells reduced) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : Reference.RiscV.Sail.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.WordMapping initial after statePointer messagePointer input message output ∧
        Delegation.TraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message :=
  Proofs.workvector_binding_at_boundary hp inverse accepted inputs.toBoundaryInputs aligned

/-- A complete G-worker span selected after whole preceding spans reaches
    the pinned work-vector reference in its actual native-clock cut states.
    Matching derives the entry control, boundary values and intermediate states. -/
theorem Native.window_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {reduced : Bool} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data)
    (inputs : WindowInputs data before cells reduced lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (Delegation.Caller.HashSpan.blakeG reduced).WindowResult data before cells lower upper :=
  Proofs.window_binding hp inverse accepted inputs aligned

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
