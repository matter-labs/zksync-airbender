import Human.Trace.Workers.KeccakSplit.RVTheorems
import Slop.KeccakSplit.Contract
import Slop.KeccakSplit.Setup.Control
import Slop.KeccakSplit.Chain.RVCalls
import Slop.KeccakSplit.RVLink
import Slop.KeccakSplit.Field

namespace Airbender.Keccak.Split.Native
open Proofs

/-- RV sibling of `operation_execution`. -/
theorem rv_operation_execution [Fact p.Prime] (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    (accepted : MemoryAccepted data) (inputs : RVOperationInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    RVMemoryExecution data before cells ∧ ∀ row ∈ data.rows, RowEffects row := by
  obtain rfl := scale256_field inverse
  exact Proofs.rv_operation_execution row_contract Split.Proofs.control_facts accepted inputs aligned

/-- RV sibling of `permutation_soundness`, with the delegate link to `RV.calls RV.f1600Calls`. -/
theorem rv_permutation_soundness [Fact p.Prime] (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : MemoryData p} {initial : RV.State} {cells : List Trace.Cell}
    (accepted : MemoryAccepted data) (inputs : RVCallInputs data initial cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (states : Fin 362 → RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      states 0 = initial ∧ (∀ index : Fin 361, Call.RVExecutesAt index (states index.castSucc) (states index.succ)) ∧
      Keccak.Permutation.RVWordMapping initial (states 361) pointer input output ∧
      RVTraceMapping data initial (states 361) cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
      ∃ s', RV.calls RV.f1600Calls initial = some s' ∧
        RV.Same s' ((states 361).setPC (initial.pc + BitVec.ofNat 32 (4 * RV.f1600Calls.length))) := by
  obtain rfl := scale256_field inverse
  obtain ⟨states, pointer, start, executes, pointerRead, laneReads, trace⟩ :=
    rv_call_chain row_contract Split.Proofs.control_facts accepted inputs aligned
  obtain ⟨input, output, mapping, result⟩ :=
    Call.Proofs.rv_permutation_of_executions states pointer executes pointerRead laneReads
  let chron : Nat → RV.State := fun m => states ⟨min m 361, by omega⟩
  have link := Delegation.Proofs.calls_list_link (ks := RV.f1600Calls) chron (by
    intro m bound x
    rw [Call.Proofs.f1600_calls_length] at bound
    have kinds := Call.Proofs.f1600_calls_kinds ⟨m, bound⟩
    have previous : chron m = states (⟨m, bound⟩ : Fin 361).castSucc := by
      simp only [chron, Fin.castSucc_mk, Nat.min_eq_left (by omega : m ≤ 361)]
    have next : chron (m + 1) = states (⟨m, bound⟩ : Fin 361).succ := by
      simp only [chron, Fin.succ_mk, Nat.min_eq_left (by omega : m + 1 ≤ 361)]
    rw [previous, next]
    simp only [kinds]
    exact Call.Proofs.split_call_link ⟨m, bound⟩ (executes ⟨m, bound⟩) x)
  have first : chron 0 = initial := start
  have final : chron RV.f1600Calls.length = states 361 := by
    simp only [chron, Call.Proofs.f1600_calls_length, Nat.min_self]
    rfl
  rw [first, final] at link
  subst start
  exact ⟨states, pointer, input, output, rfl, executes, mapping, trace, result, link⟩

end Airbender.Keccak.Split.Native
