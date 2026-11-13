module
public import Proven.KeccakSplit.RVSpec
public import Proven.KeccakSplit.Reference.PermutationDefinitions
public import Batteries.Data.Fin.Fold

@[expose] public section

/-! One split call: the spec's `f1600Step` on 64-bit lanes is the split `microStep` on their values. The live slots of
    each call are distinct (`distinct_slots`); at a live slot both write the call's result, elsewhere both keep the
    lane. -/

namespace Airbender.Keccak.Split.Call.Proofs
open Spec RV.Delegation
set_option warningAsError true
set_option maxRecDepth 16384

theorem live_slots_injective (i : Fin 361) {a b : Fin 7} (liveA : a.val < slotCount (kindAt i.val))
    (liveB : b.val < slotCount (kindAt i.val)) (same : (slots i)[a] = (slots i)[b]) : a = b := by
  have nodup := distinct_slots i
  have bound := slot_count_bound (kindAt i.val)
  have getA : ((slots i).toList.take (slotCount (kindAt i.val)))[a.val]'(by simp; omega) = (slots i)[a] := by
    simp
  have getB : ((slots i).toList.take (slotCount (kindAt i.val)))[b.val]'(by simp; omega) = (slots i)[b] := by
    simp
  exact Fin.ext ((List.Nodup.getElem_inj_iff nodup).mp (getA.trans (same.trans getB.symm)))

theorem micro_step_hit (i : Fin 361) (state : LaneState) (k : Fin 7) (live : k.val < slotCount (kindAt i.val)) :
    microStep i state (slots i)[k] =
      (result i (Vector.ofFn fun lane : Fin 7 => state (slots i)[lane]))[k] := by
  have bound : (slots i).toList.idxOf (slots i)[k] ≤ k.val := by
    have mem : (slots i)[k] ∈ (slots i).toList.take (k.val + 1) :=
      List.mem_iff_getElem.mpr ⟨k.val, by simp, by simp⟩
    have eq : (slots i).toList.idxOf (slots i)[k] = ((slots i).toList.take (k.val + 1)).idxOf (slots i)[k] := by
      conv_lhs => rw [← List.take_append_drop (k.val + 1) (slots i).toList]
      rw [List.idxOf_append, ite_eq_left mem]
    have lt := List.idxOf_lt_length_of_mem mem
    simp only [List.length_take, Vector.length_toList] at lt
    omega
  have short : (slots i).toList.idxOf (slots i)[k] < slotCount (kindAt i.val) := by omega
  have seven : (slots i).toList.idxOf (slots i)[k] < 7 := lt_of_lt_of_le short (slot_count_bound _)
  have found : (slots i)[(slots i).toList.idxOf (slots i)[k]] = (slots i)[k] := by
    simpa only [Vector.getElem_toList] using List.getElem_idxOf
      (show (slots i).toList.idxOf (slots i)[k] < (slots i).toList.length by simpa using seven)
  have equal := live_slots_injective i (a := ⟨_, seven⟩) short live (by simpa only [Fin.getElem_fin] using found)
  unfold microStep
  simp only []
  rw [dite_eq_left short]
  congr 1
  exact congrArg Fin.val equal

theorem micro_step_miss (i : Fin 361) (state : LaneState) (l : Fin 31)
    (miss : ∀ k : Fin 7, k.val < slotCount (kindAt i.val) → (slots i)[k] ≠ l) :
    microStep i state l = state l := by
  unfold microStep
  simp only []
  rw [dite_eq_right]
  intro short
  have seven : (slots i).toList.idxOf l < 7 := lt_of_lt_of_le short (slot_count_bound _)
  have found : (slots i)[(slots i).toList.idxOf l] = l := by
    simpa only [Vector.getElem_toList] using List.getElem_idxOf
      (show (slots i).toList.idxOf l < (slots i).toList.length by simpa using seven)
  exact miss ⟨_, seven⟩ short (by simpa only [Fin.getElem_fin] using found)

end Airbender.Keccak.Split.Call.Proofs

namespace Airbender.Keccak.Split.Call.Proofs
open Spec RV.Delegation
set_option warningAsError true
set_option maxRecDepth 16384

theorem round_constant_spec (r : Nat) : roundConstant r = (delayedRC r).toNat := by
  unfold roundConstant delayedRC
  split
  · rw [RC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    rfl
  · rfl

theorem rotate_toNat (a : Lane) (n : Nat) (h : n < 64) : (a.rotateLeft n).toNat = rotLeft64 a.toNat ⟨n, h⟩ :=
  (rotLeft64_toNat a ⟨n, h⟩).symm

/-- `slots` with the worker, column/row and round as parameters. -/
def slotsOf (kind : Kind) (x : Fin 5) (round : Nat) : Vector (Fin 31) 7 :=
  Vector.ofFn fun position =>
    if lane : position.val < 5 then
      let logical : Fin 25 :=
        if kind = .chi5 then ⟨5 * x.val + (position.val + 2 * x.val) % 5, by omega⟩
        else ⟨x.val + 5 * position.val, by omega⟩
      let physical := physicalSlot (if kind = .chi5 then round + 1 else round) logical
      ⟨physical.val, by have := physical.isLt; omega⟩
    else if kind = .columnParity ∧ position.val = 5 then ⟨25 + x.val, by omega⟩
    else if kind = .thetaRho then
      ⟨25 + (if position.val = 5 then (x.val + 4) % 5 else (x.val + 1) % 5), by split <;> omega⟩
    else 30

theorem slots_of (i : Fin 361) : slots i = slotsOf (kindAt i.val) ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ (i.val / 15) :=
  by rfl

/-- `result` with the worker, column/row and round as parameters. -/
def resultOf (kind : Kind) (x : Fin 5) (round : Nat) (input : Vector Nat 7) : Vector Nat 7 :=
  match kind with
  | .columnParity =>
    let first := if x.val = 0 then input[0] ^^^ roundConstant round else input[0]
    #v[first, input[1], input[2], input[3], input[4],
      first ^^^ input[1] ^^^ input[2] ^^^ input[3] ^^^ input[4], input[6]]
  | .thetaRho =>
    let d := input[5] ^^^ rotLeft64 input[6] 1
    Vector.ofFn fun lane => if active : lane.val < 5 then
      rotLeft64 (input[lane] ^^^ d) (rotations[x][lane.val]'active)
    else input[lane]
  | .chi5 => Vector.ofFn fun lane => if active : lane.val < 5 then
      input[lane] ^^^
        (not64 (input[(lane.val + 1) % 5]'(by omega)) &&& input[(lane.val + 2) % 5]'(by omega))
    else input[lane]

theorem result_of (i : Fin 361) (input : Vector Nat 7) :
    result i input = resultOf (kindAt i.val) ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ (i.val / 15) input := by
  unfold result resultOf
  cases kindAt i.val <;> rfl

theorem big_ne_lane (a : Fin 25) {k : Nat} (h : 25 ≤ k) : (k = a.val) ↔ False := ⟨fun e => by omega, False.elim⟩

theorem parity_hit (x : Fin 5) (r : Nat) (S : Vector Lane 31) (k : Fin 7) (live : k.val < 6) :
    ((f1600Step 0 x r S)[(slotsOf .columnParity x r)[k]]).toNat =
      (resultOf .columnParity x r (Vector.ofFn fun lane : Fin 7 => S[(slotsOf .columnParity x r)[lane]].toNat))[k] := by
  fin_cases x
  all_goals fin_cases k
  all_goals try (simp only at live; omega)
  all_goals simp [slotsOf, resultOf, physical_slot_spec, round_constant_spec, f1600Step, columnParity,
    slot, scratch, lane, laneSlot_val_eq, BitVec.toNat_xor,
    big_ne_lane]

theorem set5_hit (f : Fin 5 → Fin 31) (g : Fin 5 → Lane) (S : Vector Lane 31)
    (injective : Function.Injective f) (y : Fin 5) : (set5 S f g)[f y] = g y := by
  have ne (a b : Fin 5) (different : a ≠ b) : (f a).val ≠ (f b).val := fun h => different (injective (Fin.ext h))
  simp only [set5, finRange5_foldl]
  fin_cases y <;> simp [ne]

theorem set5_miss (f : Fin 5 → Fin 31) (g : Fin 5 → Lane) (S : Vector Lane 31) (l : Fin 31)
    (miss : ∀ y, f y ≠ l) : (set5 S f g)[l] = S[l] := by
  have ne (y : Fin 5) : (f y).val ≠ l.val := fun h => miss y (Fin.ext h)
  simp only [set5, finRange5_foldl]
  simp [ne]

theorem column_injective (r : Nat) (x : Fin 5) : Function.Injective (slot r x) := by
  intro a b same
  have values := congrArg Fin.val same
  simp only [slot, Fin.val_castLE, laneSlot_val_eq, lane_eq_iff] at values
  exact values.2

theorem row_injective (r : Nat) (x : Fin 5) : Function.Injective (fun k => slot r k x) := by
  intro a b same
  have values := congrArg Fin.val same
  simp only [slot, Fin.val_castLE, laneSlot_val_eq, lane_eq_iff] at values
  exact values.1

theorem rho_rotation (x : Fin 5) : ∀ y : Fin 5, ((rotations[x])[y.val]).val = rhoOffset x y := by
  revert x
  decide

theorem rho_lt : ∀ x y : Fin 5, rhoOffset x y < 64 := by decide

theorem rho_rotation_fin (x y : Fin 5) :
    rotations[x.val][y.val] = (⟨rhoOffset x y, rho_lt x y⟩ : Fin 64) :=
  Fin.ext (rho_rotation x y)

theorem theta_slot (x : Fin 5) (r : Nat) (k : Fin 5) :
    (slotsOf .thetaRho x r)[Fin.castLE (by decide : 5 ≤ 7) k] = slot r x k := by
  apply Fin.ext
  simp only [slotsOf, slot, Fin.getElem_fin, Vector.getElem_ofFn, Fin.val_castLE, k.isLt, ↓reduceDIte,
    reduceCtorEq, ↓reduceIte, physical_slot_spec]
  rfl

theorem theta_slot_val (x : Fin 5) (r : Nat) (k : Fin 5) :
    (slotsOf .thetaRho x r)[k.val]'(by omega) = slot r x k :=
  theta_slot x r k

theorem theta_hit (x : Fin 5) (r : Nat) (S : Vector Lane 31) (k : Fin 7) (live : k.val < 7) :
    ((f1600Step 3 x r S)[(slotsOf .thetaRho x r)[k]]).toNat =
      (resultOf .thetaRho x r (Vector.ofFn fun lane : Fin 7 => S[(slotsOf .thetaRho x r)[lane]].toNat))[k] := by
  have scratchLow : (slotsOf .thetaRho x r)[5]'(by decide) = scratch (x - 1).castSucc := by
    apply Fin.ext
    simp only [slotsOf, scratch, Vector.getElem_ofFn]
    fin_cases x <;> rfl
  have scratchHigh : (slotsOf .thetaRho x r)[6]'(by decide) = scratch (x + 1).castSucc := by
    apply Fin.ext
    simp only [slotsOf, scratch, Vector.getElem_ofFn]
    fin_cases x <;> rfl
  by_cases small : k.val < 5
  · obtain ⟨y, rfl⟩ : ∃ y : Fin 5, k = Fin.castLE (by decide : 5 ≤ 7) y := ⟨⟨k.val, small⟩, rfl⟩
    simp only [theta_slot, f1600Step]
    rw [set5_hit _ _ _ (column_injective r x)]
    simp only [resultOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.val_castLE, y.isLt, ↓reduceDIte,
      theta_slot_val, scratchLow, scratchHigh]
    simp only [rho_rotation_fin, thetaD]
    have outer := rotate_toNat (S[(slot r x y).val] ^^^ (S[(scratch (x - 1).castSucc).val] ^^^
      (S[(scratch (x + 1).castSucc).val]).rotateLeft 1)) (rhoOffset x y) (rho_lt x y)
    have inner := rotate_toNat S[(scratch (x + 1).castSucc).val] 1 (by decide)
    simp only [BitVec.toNat_xor, inner] at outer
    exact outer
  · have scratchSlot : ∃ z : Fin 5, (slotsOf .thetaRho x r)[k] = scratch z.castSucc := by
      have : k = 5 ∨ k = 6 := by omega
      rcases this with rfl | rfl
      · exact ⟨_, scratchLow⟩
      · exact ⟨_, scratchHigh⟩
    obtain ⟨z, hz⟩ := scratchSlot
    simp only [f1600Step, hz]
    rw [set5_miss _ _ _ _ (fun y same => by
      have values := congrArg Fin.val same
      simp only [slot, scratch, Fin.val_castLE, Fin.val_castSucc] at values
      omega)]
    simp only [resultOf, Fin.getElem_fin, Vector.getElem_ofFn, small, ↓reduceDIte]
    have same := congrArg (fun f : Fin 31 => (S[f]).toNat) hz
    simpa only [Fin.getElem_fin] using same.symm

/-- Chi position `q` of row `x` is the spec's row slot `(q + 2x) mod 5`. -/
def chiColumn (x q : Fin 5) : Fin 5 := ⟨(q.val + 2 * x.val) % 5, Nat.mod_lt _ (by decide)⟩

theorem chi_slot (x : Fin 5) (r : Nat) (q : Fin 5) :
    (slotsOf .chi5 x r)[q.val]'(by omega) = slot (r + 1) (chiColumn x q) x := by
  apply Fin.ext
  simp only [slotsOf, slot, Vector.getElem_ofFn, q.isLt, ↓reduceDIte, ↓reduceIte,
    physical_slot_spec, Fin.val_castLE]
  congr 2
  apply Fin.ext
  simp only [lane, chiColumn]
  omega

theorem chi_column_succ (x q : Fin 5) :
    chiColumn x q + 1 = chiColumn x ⟨(q.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ∧
    chiColumn x q + 2 = chiColumn x ⟨(q.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ := by
  revert x q
  decide

theorem chi_hit (x : Fin 5) (r : Nat) (S : Vector Lane 31) (k : Fin 7) (live : k.val < 5) :
    ((f1600Step 5 x r S)[(slotsOf .chi5 x r)[k]]).toNat =
      (resultOf .chi5 x r (Vector.ofFn fun lane : Fin 7 => S[(slotsOf .chi5 x r)[lane]].toNat))[k] := by
  obtain ⟨q, rfl⟩ : ∃ q : Fin 5, k = Fin.castLE (by decide : 5 ≤ 7) q := ⟨⟨k.val, live⟩, rfl⟩
  have position : (slotsOf .chi5 x r)[Fin.castLE (by decide : 5 ≤ 7) q] = slot (r + 1) (chiColumn x q) x :=
    chi_slot x r q
  simp only [position, f1600Step]
  rw [set5_hit _ _ _ (row_injective (r + 1) x)]
  have next := chi_slot x r ⟨(q.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
  have after := chi_slot x r ⟨(q.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
  simp only [resultOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.val_castLE, q.isLt, ↓reduceDIte,
    chi_slot, next, after, (chi_column_succ x q).1, (chi_column_succ x q).2, BitVec.toNat_xor, BitVec.toNat_and,
    ← not64_toNat]

theorem chi_column_onto : ∀ x k : Fin 5, ∃ q : Fin 5, chiColumn x q = k := by decide

theorem parity_slots (x : Fin 5) (r : Nat) :
    (slotsOf .columnParity x r)[0]'(by decide) = slot r x 0 ∧
      (slotsOf .columnParity x r)[5]'(by decide) = scratch x.castSucc := by
  constructor
  all_goals apply Fin.ext
  all_goals simp only [slotsOf, slot, scratch, Vector.getElem_ofFn, physical_slot_spec,
    Fin.val_castLE, Fin.val_castSucc]
  · rfl
  · simp

theorem spec_miss (kind : Kind) (x : Fin 5) (r : Nat) (S : Vector Lane 31) (l : Fin 31)
    (miss : ∀ k : Fin 7, k.val < slotCount kind → (slotsOf kind x r)[k] ≠ l) :
    (f1600Step kind.mode x r S)[l] = S[l] := by
  cases kind with
  | columnParity =>
    have low := miss 0 (by decide)
    have high := miss 5 (by decide)
    simp only [Fin.getElem_fin, Fin.isValue, Fin.val_zero, (parity_slots x r).1] at low high
    have low' : (slot r x 0).val ≠ l.val := fun h => low (Fin.ext h)
    have high' : (scratch x.castSucc).val ≠ l.val := fun h => high (Fin.ext h)
    simp only [f1600Step, Kind.mode, columnParity]
    split <;> simp [Vector.getElem_set, low', high']
  | thetaRho =>
    simp only [f1600Step, Kind.mode]
    apply set5_miss
    intro y same
    apply miss (Fin.castLE (by decide : 5 ≤ 7) y) (by simp [slotCount]; omega)
    rw [theta_slot]
    exact same
  | chi5 =>
    simp only [f1600Step, Kind.mode]
    apply set5_miss
    intro k same
    obtain ⟨q, rfl⟩ := chi_column_onto x k
    apply miss (Fin.castLE (by decide : 5 ≤ 7) q) (by simp [slotCount])
    have position : (slotsOf .chi5 x r)[Fin.castLE (by decide : 5 ≤ 7) q] = slot (r + 1) (chiColumn x q) x :=
      chi_slot x r q
    rw [position]
    exact same

theorem spec_hit (kind : Kind) (x : Fin 5) (r : Nat) (S : Vector Lane 31) (k : Fin 7)
    (live : k.val < slotCount kind) :
    ((f1600Step kind.mode x r S)[(slotsOf kind x r)[k]]).toNat =
      (resultOf kind x r (Vector.ofFn fun lane : Fin 7 => S[(slotsOf kind x r)[lane]].toNat))[k] := by
  cases kind with
  | columnParity => exact parity_hit x r S k live
  | thetaRho => exact theta_hit x r S k live
  | chi5 => exact chi_hit x r S k live

/-- One scheduled split call: the spec's `f1600Step` on 64-bit lanes is the split `microStep` on their values. -/
theorem f1600_step_nat (i : Fin 361) (S : Vector Lane 31) (l : Fin 31) :
    (f1600Step (kindAt i.val).mode ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ (i.val / 15) S)[l].toNat =
      microStep i (fun l => S[l].toNat) l := by
  by_cases hit : ∃ k : Fin 7, k.val < slotCount (kindAt i.val) ∧ (slots i)[k] = l
  · obtain ⟨k, live, rfl⟩ := hit
    rw [micro_step_hit i _ k live, result_of]
    simp only [slots_of]
    exact spec_hit _ _ _ S k live
  · have miss : ∀ k : Fin 7, k.val < slotCount (kindAt i.val) → (slots i)[k] ≠ l :=
      fun k live same => hit ⟨k, live, same⟩
    rw [micro_step_miss i _ l miss]
    simp only [slots_of] at miss
    rw [spec_miss _ _ _ S l miss]

end Airbender.Keccak.Split.Call.Proofs
