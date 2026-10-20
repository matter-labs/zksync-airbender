import Human.Trace.Workers.Keccak.Call
import Slop.Keccak.ControllerLayout
import Human.Circuits.Keccak.Execution
import Mathlib.Data.List.Nodup

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem scheduled_lane_indices_distinct (i : Fin 649) :
    ((Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048))).toList).Nodup := by
  have all : ∀ i : Fin 649,
      ((Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048))).toList).Nodup := by
    decide +kernel
  exact all i

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

theorem scheduled_indices_injective [Fact p.Prime] {w : Nat → ZMod p}
    (i : Fin 649) (effects : Native.RowEffects w) (active : w Variables.execute = 1)
    (control : (w Variables.controlReadLo).val = (scheduleControl ⟨i.val, by omega⟩).packed) :
    Function.Injective (fun lane : Fin 6 => (w (7 + lane.val)).val) := by
  have selected := scheduled_lane_indices i effects active control
  have distinct := scheduled_lane_indices_distinct i
  intro a b same
  have entries : (Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048))).toList[a.val]'(by simp) =
      (Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048))).toList[b.val]'(by simp) := by
    simpa only [Vector.getElem_toList, Fin.getElem_fin] using ((selected a).symm.trans (same.trans (selected b)))
  exact Fin.ext (distinct.getElem_inj_iff.mp entries)

private theorem low_address_value [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (effects : Native.RowEffects w) (i : Fin 12) :
    (w 13 + 8 * w (7 + i.val / 2) + (4 * (i.val % 2) : Nat)).val =
      (w 13).val + 8 * (w (7 + i.val / 2)).val + 4 * (i.val % 2) := by
  have encoded : w 13 + 8 * w (7 + i.val / 2) + (4 * (i.val % 2) : Nat) =
      (((w 13).val + 8 * (w (7 + i.val / 2)).val + 4 * (i.val % 2) : Nat) : ZMod p) := by
    simp
  rw [encoded, ZMod.val_natCast_of_lt]
  have room := effects.addresses.noCarry i
  change (w 13).val + 8 * (w (7 + i.val / 2)).val + 4 * (i.val % 2) < Arithmetic.limbBase at room
  dsimp [Arithmetic.limbBase] at room
  omega

private theorem port_code [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (effects : Native.RowEffects w) (i : Fin 14) :
    importedConstraintsMemoryPorts[i.val].address.code w =
      if i.val < 2 then Nat.pair 0 (Nat.pair (10 + i.val) 0)
      else Nat.pair 1 (Nat.pair ((w 13).val + 8 * (w (7 + (i.val - 2) / 2)).val +
        4 * ((i.val - 2) % 2)) (w 14).val) := by
  fin_cases i
  all_goals first | rfl | skip
  all_goals simp [importedConstraintsMemoryPorts, Trace.MemoryAddress.code,
    Verification.IndirectPort.rawAddress]
  all_goals first
    | simpa using low_address_value hp effects (0 : Fin 12)
    | simpa using low_address_value hp effects (1 : Fin 12)
    | simpa using low_address_value hp effects (2 : Fin 12)
    | simpa using low_address_value hp effects (3 : Fin 12)
    | simpa using low_address_value hp effects (4 : Fin 12)
    | simpa using low_address_value hp effects (5 : Fin 12)
    | simpa using low_address_value hp effects (6 : Fin 12)
    | simpa using low_address_value hp effects (7 : Fin 12)
    | simpa using low_address_value hp effects (8 : Fin 12)
    | simpa using low_address_value hp effects (9 : Fin 12)
    | simpa using low_address_value hp effects (10 : Fin 12)
    | simpa using low_address_value hp effects (11 : Fin 12)

theorem scheduled_ports_distinct [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (i : Fin 649) (effects : Native.RowEffects w) (active : w Variables.execute = 1)
    (control : (w Variables.controlReadLo).val = (scheduleControl ⟨i.val, by omega⟩).packed) :
    Function.Injective (fun port : Fin 14 => importedConstraintsMemoryPorts[port.val].address.code w) := by
  have lanes := scheduled_indices_injective i effects active control
  intro a b sameCode
  have combined := (port_code hp effects a).symm.trans (sameCode.trans (port_code hp effects b))
  clear sameCode
  have sameCode := combined
  have aBound := a.isLt
  have bBound := b.isLt
  apply Fin.ext
  by_cases first : a.val < 2
  · rw [ite_eq_left first] at sameCode
    by_cases second : b.val < 2
    · rw [ite_eq_left second] at sameCode
      have equal := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp sameCode).2).1
      omega
    · rw [ite_eq_right second] at sameCode
      have impossible := (Nat.pair_eq_pair.mp sameCode).1
      omega
  · rw [ite_eq_right first] at sameCode
    by_cases second : b.val < 2
    · rw [ite_eq_left second] at sameCode
      have impossible := (Nat.pair_eq_pair.mp sameCode).1
      omega
    · rw [ite_eq_right second] at sameCode
      have low := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp sameCode).2).1
      have sameLane : (w (7 + (a.val - 2) / 2)).val = (w (7 + (b.val - 2) / 2)).val := by omega
      have equal := @lanes ⟨(a.val - 2) / 2, by omega⟩
        ⟨(b.val - 2) / 2, by omega⟩ sameLane
      have equalIndex := congrArg Fin.val equal
      dsimp only at equalIndex
      omega

end Airbender.Keccak.Proofs
