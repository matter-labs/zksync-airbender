import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.UnifiedReduced.ComputedHashWindows

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem prepared_hash_memory_inputs [Fact p.Prime]
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (inputs : PreparedHashWindowInputs data before ca oa cells program span lower upper) :
    MixedMemoryInputs data program before ca oa cells :=
  computed_hash_memory_inputs (literal_computed_hash_inputs inputs)

theorem prepared_hash_window [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    JointHashWindowResult data before cells span lower upper :=
  computed_hash_window hp clockInverse accepted (literal_computed_hash_inputs inputs) first last

theorem prepared_hash_reference_at_states [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before atStart atFinish : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    {start finish : List (MemoryToken p)} {spanEvents : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0)
    (prefixMatching : (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps lower).map Prod.fst))
    (matching : (start ++ (data.windowSteps lower upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps lower upper).map Prod.fst))
    (startBoundary : NativeBoundary start atStart cells) (finishBoundary : NativeBoundary finish atFinish cells)
    (spanPerm : spanEvents.Perm ((data.windowSteps lower upper).map transferEvent))
    (spanHistory : SailHistory cells spanEvents atStart atFinish) :
    span.Result (data.windowProjection lower upper start finish) atStart atFinish (Delegation.Caller.workerCells cells) :=
  computed_hash_reference_at_states hp clockInverse accepted (literal_computed_hash_inputs inputs)
    first last prefixMatching matching startBoundary finishBoundary spanPerm spanHistory

theorem prepared_hash_chain [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {firstSpan secondSpan : Delegation.Caller.HashSpan}
    {a b c d : Nat}
    (accepted : MixedMemoryAccepted data program)
    (firstInputs : PreparedHashWindowInputs data before ca oa cells program firstSpan a b)
    (secondInputs : PreparedHashWindowInputs data before ca oa cells program secondSpan c d)
    (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0) (gap : b ≤ c) :
    PreparedHashChainResult data before cells firstSpan secondSpan a b c d :=
  computed_hash_chain hp clockInverse accepted (literal_computed_hash_inputs firstInputs)
    (literal_computed_hash_inputs secondInputs) aa ba ca' da gap

theorem prepared_hash_sequence_at_segments [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {windows : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ∀ window ∈ windows, PreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
    {cut : Nat} {tokens : List (MemoryToken p)} {state : State} {segments : List (WindowSegment p)}
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval))
    (actual : WindowSegmentsRealize data cells cut tokens state (windows.map HashWindow.interval) segments) :
    List.Forall₂ (HashWindowResult data cells) windows segments :=
  computed_hash_sequence_at_segments hp clockInverse accepted
    (fun window member => literal_computed_hash_inputs (inputs window member)) ordered actual

theorem prepared_hash_sequence [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (firstInputs : PreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper)
    (restInputs : ∀ window ∈ rest, PreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    PreparedHashSequenceResult data before cells first rest :=
  computed_hash_sequence hp clockInverse accepted (literal_computed_hash_inputs firstInputs)
    (fun window member => literal_computed_hash_inputs (restInputs window member)) ordered

end Airbender.UnifiedReduced.Caller.Proofs
