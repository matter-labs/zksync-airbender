import Airbender.Review.Trace.UnifiedReduced.RegisterChains
import Airbender.Proofs.UnifiedReduced.RegisterPreparation

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem public_register_preparation_after_initial [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (preparation : PublicRegisterPreparation data program cut register value) :
    (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut := by
  cases preparation with
  | literal scope => exact scope.afterInitial
  | pcRelative scope => exact scope.afterInitial
  | addi _ scope _ => exact scope.afterInitial

/-- Induction over public dataflow derives each real source token before using
    native arithmetic for the next ADDI. No intermediate values are assumed from
    witness reads, and no Sail transport or worker round mask is needed. -/
theorem public_register_preparation_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (preparation : PublicRegisterPreparation data program cut register value) :
    ∀ {tokens : List (MemoryToken p)}, register ≠ 0 → cut % 4 = 0 →
      (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
        (tokens ++ (data.prefixSteps cut).map Prod.fst) →
      ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
        (timeOfPair token.time).value = cut - 2 ∧ token.word = Word.ofBitVec value := by
  induction preparation with
  | literal scope =>
    intro tokens nonzero aligned matching
    exact preparation_token hp clockInverse accepted publicProgram ordinaryProgram initialization scope nonzero aligned matching
  | pcRelative scope =>
    intro tokens nonzero aligned matching
    exact pc_relative_preparation_token hp clockInverse setup accepted publicProgram ordinaryProgram
      initialization scope nonzero aligned matching
  | addi prior scope sourceNonzero ih =>
    intro tokens nonzero aligned matching
    have floor := public_register_preparation_after_initial prior
    exact register_immediate_preparation_token hp clockInverse setup accepted publicProgram ordinaryProgram
      initialization scope uniqueSeeds floor
      (fun _ prefixMatching => ih sourceNonzero (by omega) prefixMatching) nonzero aligned matching

theorem public_register_preparation_at_boundary [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before atCut : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {tokens : List (MemoryToken p)}
    {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (preparation : PublicRegisterPreparation data program cut register value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) (boundary : NativeBoundary tokens atCut cells) :
    (Cell.register register).read atCut = .ok value atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
        (timeOfPair token.time).value = cut - 2 ∧ token.word = Word.ofBitVec value := by
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses inputs.initialization]
    exact inputs.distinct
  obtain ⟨token, present, address, time, word⟩ := public_register_preparation_token hp clockInverse inputs.setup
    accepted inputs.publicProgram inputs.ordinaryProgram inputs.initialization unique preparation nonzero aligned matching
  obtain ⟨cell, _, code, read⟩ := native_boundary_read boundary present
  have same : cell = Cell.register register := cell_address_injective (code.trans address)
  subst cell
  have bits : token.word.toBitVec = value := by rw [word, Word.ofBitVec_roundtrip]
  exact ⟨bits ▸ read, token, present, address, time, word⟩

theorem public_register_control_preparation [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (preparation : PublicRegisterPreparation data program cut register value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    RegisterChainPreparedBoundaryExecution data before cells cut register value := by
  have floor := public_register_preparation_after_initial preparation
  obtain ⟨tokens, _, events, _, atCut, _, permutation, _, history, _, matching, _, boundary, _⟩ :=
    (mixed_window_execution (lower := cut) (upper := cut) hp clockInverse rotationInverse accepted inputs
      aligned aligned (by omega) (by omega)).execution
  exact ⟨tokens, events, atCut, permutation, history, boundary,
    public_register_preparation_at_boundary hp clockInverse accepted inputs preparation nonzero aligned matching boundary⟩

end Airbender.UnifiedReduced.Caller.Proofs
