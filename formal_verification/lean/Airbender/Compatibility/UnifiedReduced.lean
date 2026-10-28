import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.UnifiedReduced.MixedComposition
import Airbender.Proofs.UnifiedReduced.MixedCycleComposition
import Airbender.Proofs.UnifiedReduced.Composition
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.SharedSpans
import Airbender.Proofs.UnifiedReduced.RequestWindows
import Airbender.Proofs.UnifiedReduced.MixedWindows
import Airbender.Proofs.UnifiedReduced.JointHashWindows
import Airbender.Proofs.UnifiedReduced.MixedWindowProjection
import Airbender.Proofs.UnifiedReduced.ControlPreparation
import Airbender.Proofs.UnifiedReduced.PCRelativePreparation
import Airbender.Proofs.UnifiedReduced.RegisterPreparation
import Airbender.Proofs.UnifiedReduced.RegisterChains
import Airbender.Proofs.UnifiedReduced.RegisterDataflow
import Airbender.Proofs.UnifiedReduced.PreparedHashWindows
import Airbender.Proofs.UnifiedReduced.ComputedHashWindows
import Airbender.Proofs.UnifiedReduced.ComputedRoundRegions
import Airbender.Proofs.UnifiedReduced.PreparedRoundWindows
import Airbender.Proofs.UnifiedReduced.CallerCycles
import Airbender.Proofs.UnifiedReduced.UnissuedWorkers
import Airbender.Proofs.UnifiedReduced.WorkerExecution
import Airbender.Proofs.UnifiedReduced.Segmentation
import Airbender.Proofs.Delegation.RequestHashWindows

namespace Airbender.UnifiedReduced

/-- Complete G and Keccak references reach the actual mixed-history cut states
    after original public literal preparation. Shared matching derives controls,
    caller scheduling, worker boundaries and native reads. Other nonround workers
    may precede or follow the homogeneous selected span. Public span ABI,
    program/domain and modeled tables remain explicit; no worker masks are supplied. -/
theorem Caller.prepared_hash_window_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    Caller.JointHashWindowResult data before cells span lower upper :=
  Caller.Proofs.prepared_hash_window hp clockInverse accepted inputs first last

/-- Two complete prepared G/Keccak references compose through one continuous
    history, including the intervening preparation and other worker effects.
    Public mode/count/duration and nonround worker scope remain explicit. -/
theorem Caller.prepared_hash_chain_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {firstSpan secondSpan : Delegation.Caller.HashSpan} {a b c d : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (firstInputs : Caller.PreparedHashWindowInputs data before ca oa cells program firstSpan a b)
    (secondInputs : Caller.PreparedHashWindowInputs data before ca oa cells program secondSpan c d)
    (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0) (gap : b ≤ c) :
    Caller.PreparedHashChainResult data before cells firstSpan secondSpan a b c d :=
  Caller.Proofs.prepared_hash_chain hp clockInverse accepted firstInputs secondInputs aa ba ca' da gap

/-- A nonempty ordered list of complete prepared G/Keccak references shares one
    continuous actual memory history. Each span retains its public preparation,
    mode/count/duration and nonround scope; all intermediate states are derived. -/
theorem Caller.prepared_hash_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (firstInputs : Caller.PreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper)
    (restInputs : ∀ window ∈ rest, Caller.PreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.prepared_hash_sequence hp clockInverse accepted firstInputs restInputs ordered

/-- Public LUI preparation and native matching derive all extended-BLAKE masks
    before Sail transport. The public suffix duration and ten-position ABI remain explicit. -/
theorem Caller.prepared_round_masks_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {flags : Fin 8} {lower : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedRoundInputs data before ca oa cells program flags lower) (first : lower % 4 = 0) :
    ∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round :=
  Caller.Proofs.prepared_round_masks hp clockInverse accepted inputs first

/-- Complete extended-BLAKE compression reaches the actual prepared mixed-history
    cut states. Controls, masks, caller selectors and worker boundaries are derived. -/
theorem Caller.prepared_round_window_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {flags : Fin 8} {lower upper : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedRoundWindowInputs data before ca oa cells program flags lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    Caller.JointHashWindowResult data before cells (.blakeRound flags) lower upper :=
  Caller.Proofs.prepared_round_window hp clockInverse accepted inputs first last

/-- The prepared extended-round scope derives masks before constructing the
    same actual caller cycles; no mask or intermediate state is supplied. -/
theorem Caller.prepared_round_cycles_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {flags : Fin 8} {lower : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedRoundInputs data initial ca oa cells program flags lower) (first : lower % 4 = 0)
    (code : Caller.CodeProfile data program cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value) :
    Caller.CallerCycleEffects data program initial cells :=
  Caller.Proofs.prepared_round_caller_cycles accepted inputs first code started

/-- Two consecutive public literal/ADDI instructions bind a protocol constant.
    Initialized matching derives the actual operand and result; both final
    cycles are worker-free, with all earlier transfers retained. The existing
    public cell domain supplies uniqueness, and only public constants occur in
    the value equation. Full Sail retirement remains separate. -/
theorem Caller.literal_addi_hash_preparation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {span : Delegation.Caller.HashSpan} {source : BitVec 5}
    {literal : Caller.ControlLiteral} {immediate : BitVec 12}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (seed : Caller.ControlPreparation data program (cut - 4) source literal)
    (step : Caller.RegisterImmediatePreparation data program cut source span.controlRegister immediate)
    (nonzero : source ≠ 0)
    (value : Caller.registerImmediateValue literal.value immediate = span.controlStart)
    (aligned : cut % 4 = 0) :
    Caller.PreparedBoundaryExecution data before cells cut span.controlRegister (Caller.hashPreparation span) :=
  Caller.Proofs.hash_control_preparation hp clockInverse rotationInverse accepted inputs
    (Caller.Proofs.literal_addi_hash_preparation_source inputs.initialization inputs.distinct seed step nonzero value) aligned

/-- The same public chain binds a protocol entry constant, feeding every
    existing selected-reference window/list interface before regional masks and
    Sail transport. The public cell domain supplies seed uniqueness. -/
theorem Caller.register_chain_hash_preparation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {span : Delegation.Caller.HashSpan} {value : BitVec 32}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (preparation : Caller.PublicRegisterPreparation data program cut span.controlRegister value)
    (entry : value = span.controlStart) (aligned : cut % 4 = 0) :
    Caller.PreparedBoundaryExecution data before cells cut span.controlRegister (Caller.hashPreparation span) :=
  Caller.Proofs.hash_control_preparation hp clockInverse rotationInverse accepted inputs
    (Caller.Proofs.register_chain_hash_preparation_source inputs.initialization inputs.distinct preparation entry) aligned

/-- A final public ADDI binds the derived dataflow value to a protocol constant
    and restores the canonical cut-minus-two output timestamp. The same source
    feeds all existing selected-reference windows/lists before regional masks. -/
theorem Caller.register_dataflow_hash_preparation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {span : Delegation.Caller.HashSpan} {source : BitVec 5} {value : BitVec 32} {immediate : BitVec 12}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (prior : Caller.PublicRegisterDataflow data program (cut - 4) source value)
    (scope : Caller.RegisterImmediatePreparation data program cut source span.controlRegister immediate)
    (nonzero : source ≠ 0)
    (entry : Caller.registerImmediateValue value immediate = span.controlStart) (aligned : cut % 4 = 0) :
    Caller.PreparedBoundaryExecution data before cells cut span.controlRegister (Caller.hashPreparation span) :=
  Caller.Proofs.hash_control_preparation hp clockInverse rotationInverse accepted inputs
    (Caller.Proofs.register_dataflow_hash_preparation_source inputs.initialization inputs.distinct prior scope nonzero entry) aligned

/-- Actual caller fetch, issued-worker references and Sail PC retirement use
    one shared history. The physical/code domain and existing worker ABI remain explicit. -/
theorem Caller.caller_cycles_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (code : Caller.CodeProfile data program cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value) :
    Caller.CallerCycleEffects data program initial cells :=
  Caller.Proofs.caller_cycles accepted inputs code started

end Airbender.UnifiedReduced
