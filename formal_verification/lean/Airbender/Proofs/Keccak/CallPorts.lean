import Airbender.Review.Trace.Workers.Keccak.Call
import Airbender.Proofs.Keccak.ControllerLayout
import Airbender.Review.Circuits.Keccak.Execution
import Mathlib.Data.List.Nodup

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private abbrev scheduledDistinct (i : Fin 649) : Prop :=
  ((Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048))).toList).Nodup

private def scheduledChunk (base width : Nat) (fits : base + width ≤ 649)
    (i : Fin width) : Fin 649 := ⟨base + i.val, by omega⟩

private theorem distinct0 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 0 64 (by decide) i) := by decide +kernel
private theorem distinct1 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 64 64 (by decide) i) := by decide +kernel
private theorem distinct2 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 128 64 (by decide) i) := by decide +kernel
private theorem distinct3 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 192 64 (by decide) i) := by decide +kernel
private theorem distinct4 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 256 64 (by decide) i) := by decide +kernel
private theorem distinct5 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 320 64 (by decide) i) := by decide +kernel
private theorem distinct6 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 384 64 (by decide) i) := by decide +kernel
private theorem distinct7 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 448 64 (by decide) i) := by decide +kernel
private theorem distinct8 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 512 64 (by decide) i) := by decide +kernel
private theorem distinct9 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 576 64 (by decide) i) := by decide +kernel
private theorem distinct10 : ∀ i : Fin 9,
    scheduledDistinct (scheduledChunk 640 9 (by decide) i) := by decide +kernel

theorem scheduled_lane_indices_distinct (i : Fin 649) :
    ((Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048))).toList).Nodup := by
  change scheduledDistinct i
  have bound := i.isLt
  by_cases h0 : i.val < 64
  · simpa only [scheduledChunk, Nat.zero_add] using distinct0 ⟨i.val, h0⟩
  by_cases h1 : i.val < 128
  · simpa only [scheduledChunk, show 64 + (i.val - 64) = i.val by omega] using
      distinct1 ⟨i.val - 64, by omega⟩
  by_cases h2 : i.val < 192
  · simpa only [scheduledChunk, show 128 + (i.val - 128) = i.val by omega] using
      distinct2 ⟨i.val - 128, by omega⟩
  by_cases h3 : i.val < 256
  · simpa only [scheduledChunk, show 192 + (i.val - 192) = i.val by omega] using
      distinct3 ⟨i.val - 192, by omega⟩
  by_cases h4 : i.val < 320
  · simpa only [scheduledChunk, show 256 + (i.val - 256) = i.val by omega] using
      distinct4 ⟨i.val - 256, by omega⟩
  by_cases h5 : i.val < 384
  · simpa only [scheduledChunk, show 320 + (i.val - 320) = i.val by omega] using
      distinct5 ⟨i.val - 320, by omega⟩
  by_cases h6 : i.val < 448
  · simpa only [scheduledChunk, show 384 + (i.val - 384) = i.val by omega] using
      distinct6 ⟨i.val - 384, by omega⟩
  by_cases h7 : i.val < 512
  · simpa only [scheduledChunk, show 448 + (i.val - 448) = i.val by omega] using
      distinct7 ⟨i.val - 448, by omega⟩
  by_cases h8 : i.val < 576
  · simpa only [scheduledChunk, show 512 + (i.val - 512) = i.val by omega] using
      distinct8 ⟨i.val - 512, by omega⟩
  by_cases h9 : i.val < 640
  · simpa only [scheduledChunk, show 576 + (i.val - 576) = i.val by omega] using
      distinct9 ⟨i.val - 576, by omega⟩
  · simpa only [scheduledChunk, show 640 + (i.val - 640) = i.val by omega] using
      distinct10 ⟨i.val - 640, by omega⟩

theorem scheduled_lane_indices [Fact p.Prime] {w : Nat → ZMod p}
    (i : Fin 649) (effects : Native.RowEffects w) (active : w Variables.execute = 1)
    (control : (w Variables.controlReadLo).val = (scheduleControl ⟨i.val, by omega⟩).packed) :
    ∀ lane : Fin 6, (w (7 + lane.val)).val =
      (Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048)))[lane] := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
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
  · rw [if_pos first] at sameCode
    by_cases second : b.val < 2
    · rw [if_pos second] at sameCode
      have equal := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp sameCode).2).1
      omega
    · rw [if_neg second] at sameCode
      have impossible := (Nat.pair_eq_pair.mp sameCode).1
      omega
  · rw [if_neg first] at sameCode
    by_cases second : b.val < 2
    · rw [if_pos second] at sameCode
      have impossible := (Nat.pair_eq_pair.mp sameCode).1
      omega
    · rw [if_neg second] at sameCode
      have low := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp sameCode).2).1
      have sameLane : (w (7 + (a.val - 2) / 2)).val = (w (7 + (b.val - 2) / 2)).val := by omega
      have equal := @lanes ⟨(a.val - 2) / 2, by omega⟩
        ⟨(b.val - 2) / 2, by omega⟩ sameLane
      have equalIndex := congrArg Fin.val equal
      dsimp only at equalIndex
      omega

end Airbender.Keccak.Proofs
