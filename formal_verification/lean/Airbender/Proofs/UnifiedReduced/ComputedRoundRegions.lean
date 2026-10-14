import Airbender.Review.Trace.UnifiedReduced.ComputedRoundRegions
import Airbender.Proofs.UnifiedReduced.ComputedHashWindows
import Airbender.Proofs.Blake2Round.ControlPool

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem literal_computed_round_region_inputs [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (scope : RoundRegionInputs data program region) : ComputedRoundRegionInputs data program region :=
  ⟨scope.family, .literal scope.preparation, scope.roundsBound, scope.duration, scope.aligned, scope.beforeTerminal⟩

theorem literal_computed_protocol_inputs [Fact p.Prime]
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (inputs : PreparedProtocolInputs data before ca oa cells program regions) :
    ComputedPreparedProtocolInputs data before ca oa cells program regions :=
  ⟨inputs.toProtocolContextInputs,
    fun region member => literal_computed_round_region_inputs (inputs.scopes region member), inputs.coverage⟩

theorem computed_round_region_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProtocolContextInputs data before ca oa cells program)
    (scope : ComputedRoundRegionInputs data program region) :
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have floor := hash_control_preparation_after_initial scope.preparation
  have duration := scope.duration
  have positive : 2 ≤ region.lower := by omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  obtain ⟨start, earlier, suffix⟩ := Transfer.split_at facts (region.lower - 1)
  obtain ⟨finish, window, _⟩ := Transfer.split_at suffix (region.upper - 1)
  change Transfer.Facts ⟨start, finish,
    Transfer.windowSteps (mixedData data) (region.lower - 1) (region.upper - 1)⟩ at window
  rw [← mixed_window_steps size clockInverse accepted.toRequestChecks inputs.publicProgram
    scope.aligned.1 scope.aligned.2 positive (by omega)] at window
  have prefixMatching := earlier.matching
  rw [mixed_prefix_steps data (by omega)] at prefixMatching
  obtain ⟨token, member, address, _, word⟩ := hash_control_preparation_token hp clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.initialization scope.preparation
    scope.aligned.1 prefixMatching
  have word : token.word = Blake2Round.controlAt region.flags 0 := by
    rw [word]
    have bound := region.flags.isLt
    simp [Delegation.Caller.HashSpan.controlStart, Word.ofBitVec, Blake2Round.controlAt, limbBase, BitVec.toNat_ofNat]
    omega
  have schedule := caller_window_schedule size clockInverse accepted.toRequestChecks inputs.publicProgram
    scope.aligned.1 scope.aligned.2 positive (by omega) (by omega) scope.beforeTerminal duration
  let keep := fun token : MemoryToken p => token.address != (Cell.register 0).addressCode
  let projected := data.windowProjection region.lower region.upper start finish
  have matching := window.matching.filter keep
  have writes := caller_window_filtered_tokens schedule requests true
  have reads := caller_window_filtered_tokens schedule requests false
  change ((data.windowSteps region.lower region.upper).map Prod.snd).filter keep = _ at writes
  change ((data.windowSteps region.lower region.upper).map Prod.fst).filter keep = _ at reads
  simp only [List.filter_append, writes, reads] at matching
  have selected : Delegation.MemoryAccepted projected := by
    refine ⟨fun row member => accepted.workerConstraints row (List.mem_of_mem_filter member), matching⟩
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp (by
    change (data.machine.initialMemory.map MemoryToken.address).Nodup
    rw [image_addresses inputs.initialization]
    exact inputs.distinct)
  have pool : Blake2Round.Proofs.ControlMatchingInputs projected region.flags := by
    refine ⟨⟨matching, Delegation.Proofs.preserved_addresses, ?_⟩,
      unique.sublist (List.filter_sublist.map MemoryToken.address), inputs.tables, scope.family,
      ⟨token, List.mem_filter.mpr ⟨member, ?_⟩, address, word⟩, scope.roundsBound⟩
    · intro edge present
      have member := List.mem_flatMap.mp present
      obtain ⟨row, included, step⟩ := member
      exact facts.order edge (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨row, List.mem_of_mem_filter included, step⟩)))
    · simp [address, Cell.addressCode, Delegation.Caller.HashSpan.controlRegister]
  exact Blake2Round.Proofs.matching_masks size selected pool

theorem wrapped_program_computed_round_region_inputs [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (scope : WrappedProgramComputedRoundRegionInputs data program region) :
    ComputedRoundRegionInputs data program region := by
  have schedule := wrapped_program_hash_preparation_schedule hp clockInverse setup accepted publicProgram
    ordinaryProgram registry scope.preparation scope.code scope.aligned.1 scope.aligned.2
    scope.extent.1 scope.beforeTerminal
  have count : (data.workers.windowRows region.lower region.upper).length = (region.upper - region.lower) / 4 :=
    schedule.workerCount.symm.trans schedule.machineCount
  refine ⟨schedule.family, scope.preparation, ?_, ?_, scope.aligned, scope.beforeTerminal⟩
  · rw [count]
    have extent := scope.extent
    omega
  · rw [count]
    have aligned := scope.aligned
    have extent := scope.extent
    omega

theorem wrapped_program_computed_round_region_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProtocolContextInputs data before ca oa cells program) (registry : WrappedSequentialProgram program)
    (scope : WrappedProgramComputedRoundRegionInputs data program region) :
    ComputedRoundRegionInputs data program region ∧
      ∀ row ∈ data.workers.windowRows region.lower region.upper,
        ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  have shape := wrapped_program_computed_round_region_inputs (by omega) clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram registry scope
  exact ⟨shape, computed_round_region_masks hp clockInverse accepted inputs shape⟩

theorem computed_protocol_memory_inputs [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ComputedPreparedProtocolInputs data before ca oa cells program regions) :
    MixedMemoryInputs data program before ca oa cells := by
  refine ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables, ?_⟩
  intro row member family
  obtain ⟨region, included, inside⟩ := inputs.coverage row member family
  exact computed_round_region_masks hp clockInverse accepted inputs.toProtocolContextInputs
    (inputs.scopes region included) row inside

end Airbender.UnifiedReduced.Caller.Proofs
