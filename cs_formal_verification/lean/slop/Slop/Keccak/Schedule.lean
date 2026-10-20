import Slop.Keccak.ControlUpdate
import Human.Trace.Workers.Keccak.Call
import Mathlib.Tactic.IntervalCases

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem control_packed_injective {a b : ControlState} (same : a.packed = b.packed) : a = b := by
  have am := a.mode.isLt; have ai := a.iteration.isLt; have ar := a.round.isLt
  have bm := b.mode.isLt; have bi := b.iteration.isLt; have br := b.round.isLt
  have mode : a.mode = b.mode := Fin.ext (by dsimp [ControlState.packed] at same; omega)
  have iteration : a.iteration = b.iteration := Fin.ext (by dsimp [ControlState.packed] at same; omega)
  have round : a.round = b.round := Fin.ext (by dsimp [ControlState.packed] at same; omega)
  cases a; cases b; simp_all

theorem schedule_start : (scheduleControl 0).packed = 0 := by decide
theorem schedule_finish : (scheduleControl 649).packed = 1544 := by decide

theorem schedule_next (i : Fin 649) :
    (scheduleControl ⟨i.val, by have := i.isLt; omega⟩).nextPacked =
      (scheduleControl ⟨i.val + 1, by have := i.isLt; omega⟩).packed := by
  have stageBound : i.val % 27 < 27 := Nat.mod_lt _ (by decide)
  have nextStage : (i.val + 1) % 27 = if i.val % 27 = 26 then 0 else i.val % 27 + 1 := by
    by_cases last : i.val % 27 = 26 <;> simp only [last, ite_true, ite_false] <;> omega
  have nextRound : (i.val + 1) / 27 = i.val / 27 + if i.val % 27 = 26 then 1 else 0 := by
    by_cases last : i.val % 27 = 26 <;> simp only [last, ite_true, ite_false] <;> omega
  simp only [scheduleControl, ControlState.packed, ControlState.nextPacked]
  rw [nextStage, nextRound]
  interval_cases i.val % 27 <;> simp

theorem forced_schedule_step [Fact p.Prime] (hp : 4096 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (i : Fin 649)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1)
    (current : (w 3).val = (scheduleControl ⟨i.val, by have := i.isLt; omega⟩).packed) :
    (w 5).val = (scheduleControl ⟨i.val + 1, by have := i.isLt; omega⟩).packed := by
  obtain ⟨state, read, write⟩ := (control_update_checks hp holds).active active
  have same : state = scheduleControl ⟨i.val, by have := i.isLt; omega⟩ :=
    control_packed_injective (read.symm.trans current)
  rw [write, same, schedule_next]

end Airbender.Keccak.Proofs
