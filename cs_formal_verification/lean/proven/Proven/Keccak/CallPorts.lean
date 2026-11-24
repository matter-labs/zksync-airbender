module
public import Proven.Defs.Trace.Workers.Keccak.Call
public import Human.Circuits.Keccak.Execution
public import Mathlib.Data.List.Nodup
public import Proven.OpIndex
public import Mathlib.Tactic.LinearCombination
public import Proven.Defs.Circuits.Keccak.Artifact

@[expose] public section

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem scheduled_lane_indices [Fact p.Prime] {w : Nat → ZMod p}
    (i : Fin 649) (effects : Native.RowEffects w) (active : w Variables.execute = 1)
    (control : (w Variables.controlReadLo).val = (scheduleControl ⟨i.val, by omega⟩).packed) :
    ∀ lane : Fin 6, (w (7 + lane.val)).val =
      (Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048)))[lane] := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  obtain ⟨key, keyValue, selected⟩ := effects.indices
  have keyEqual : key = Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048) := by
    apply Fin.ext
    simp only [Fin.val_ofNat]
    rw [← control]
    have keyValue : key.val = (w 3).val + 2048 := by simpa only [active, ZMod.val_one, Nat.mul_one] using keyValue
    change key.val = ((w 3).val + 2048) % 4096
    rw [← keyValue]
    exact (Nat.mod_eq_of_lt key.isLt).symm
  simpa only [keyEqual] using selected

end Airbender.Keccak.Proofs
