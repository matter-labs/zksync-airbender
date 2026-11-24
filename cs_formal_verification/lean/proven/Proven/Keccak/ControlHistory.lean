module
public import Proven.Keccak.Schedule
public import Proven.KernelRfl
public import Proven.Defs.Trace.Workers.Keccak.Call

@[expose] public section

namespace Airbender.Keccak.Proofs
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem control_edges [Fact p.Prime] {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .keccak) :
    (data.steps.filter fun edge => edge.1.address = (Cell.register 10).addressCode) =
      data.rows.map (fun row => (readToken row.assignment importedConstraintsMemoryPorts[0],
        row.writeToken importedConstraintsMemoryPorts[0])) := by
  simp only [Delegation.MemoryData.steps, List.filter_flatMap, List.map_eq_flatMap]
  change (data.rows.map _).flatten = (data.rows.map _).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row member
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ member
    change kind = .keccak at same
    subst kind
    simp [Delegation.Row.memorySteps, Delegation.Row.ports, importedConstraintsMemoryPorts,
      readToken, MemoryAddress.code, Cell.addressCode, pairCode, Nat.pair_eq_pair]

theorem forced_path [Fact p.Prime] (hp : 4096 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {path : List (MemoryToken p)} {source : MemoryToken p}
    (size : path.length = 650) (start : path.head? = some source) (startWord : source.word = ⟨0, 0⟩)
    (steps : ∀ edge ∈ path.zip path.tail, ∃ w : Nat → ZMod p,
      FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup) ∧ w 0 = 1 ∧
      edge.1.word = Word.mk (w 3).val (w 4).val ∧ edge.2.word = Word.mk (w 5).val (w 6).val) :
    ∀ i : Fin 650, (path[i.val]'(by omega)).word = ⟨(scheduleControl i).packed, 0⟩ := by
  intro i
  have establish : ∀ (n : Nat) (bound : n < 650), (path[n]'(by omega)).word =
      Word.mk (scheduleControl ⟨n, by omega⟩).packed 0 := by
    intro n
    induction n with
    | zero =>
      intro bound
      have first : (path[0]'(by omega)) = source := by
        have head : path[0]? = some source := by
          simpa only [List.head?_eq_getElem?] using start
        simpa [List.getElem?_eq_getElem, size] using head
      rw [first, startWord]
      simp [schedule_start]
    | succ n ih =>
      intro bound
      have prior := ih (by omega)
      have edge : (path[n]'(by omega), path[n + 1]'(by omega)) ∈ path.zip path.tail := by
        apply List.mem_iff_getElem.mpr
        refine ⟨n, by simp [size]; omega, ?_⟩
        simp
      obtain ⟨w, holds, active, read, write⟩ := steps _ edge
      have high := control_high_zero holds
      have current : (w 3).val = (scheduleControl ⟨n, by omega⟩).packed := by
        exact congrArg Word.lo (read.symm.trans prior)
      have next := forced_schedule_step hp ⟨n, by omega⟩ holds active current
      rw [write, next, high.2, ZMod.val_zero]
  exact establish i.val i.isLt

end Airbender.Keccak.Proofs
