import Slop.Deleg.KeccakFips
import Clean.Utils.Rotation
import Mathlib.Tactic.IntervalCases

/-! FIPS 202's composition `fipsF` is `keccakF`, Clean's `keccakPermutation` (`fipsF_eq`): each step maps our
lanes (`BitVec 64`, numbered `x + 5y`) to Clean's (natural numbers, numbered `5x + y`; `toClean`) as Clean's step
does. -/

namespace Spec

/-- Clean's lanes of ours. -/
def toClean (A : Vector Lane 25) : Vector Nat 25 := Vector.ofFn fun c => A[cleanLane c].toNat

theorem rotLeft64_toNat (a : Lane) (n : Fin 64) : rotLeft64 a.toNat n = (a.rotateLeft n.val).toNat := by
  rw [rotLeft64, Utils.Rotation.rotRight64_eq_bv_rotate _ a.isLt]
  congr 1
  have e : a.toNat.toUInt64.toBitVec = a := by
    simp [Nat.toUInt64]
  rw [e]
  have hv : ((((64 : Fin 64) - n) % 64 : Fin 64) : Nat) = (64 - n.val) % 64 := by
    rcases n with ⟨n, hn⟩
    simp [Fin.mod_def, Fin.val_neg']
  rw [hv]
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]
  split_ifs <;> congr 1 <;> omega

theorem not64_toNat (a : Lane) : not64 a.toNat = (~~~a).toNat := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [not64, show (0xffffffffffffffff : Nat) = 2 ^ 64 - 1 from rfl, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_not]
  by_cases h : i < 64
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge a i (by omega)]

theorem toClean_get (A : Vector Lane 25) (c : Nat) (hc : c < 25) :
    (toClean A)[c] = (A[5 * (c % 5) + c / 5]'(by omega)).toNat := by
  simp [toClean, cleanLane]

theorem theta_clean (A : Vector Lane 25) : toClean (theta A) = Specs.Keccak256.theta (toClean A) := by
  apply Vector.ext; intro c hc
  interval_cases c <;> simp [-BitVec.toNat_rotateLeft, toClean_get, theta, thetaD, parity, laneX, lane, Specs.Keccak256.theta,
    Specs.Keccak256.thetaXor, Specs.Keccak256.thetaD, Specs.Keccak256.thetaC, ← BitVec.toNat_xor, rotLeft64_toNat]

/-- Clean's ρ∘π as two tables: lane `c` is lane `rhoPiSrc c` rotated by `rhoPiOff c`. -/
def rhoPiSrc : Fin 25 → Fin 25 :=
  ![0, 15, 5, 20, 10, 6, 21, 11, 1, 16, 12, 2, 17, 7, 22, 18, 8, 23, 13, 3, 24, 14, 4, 19, 9]
def rhoPiOff : Fin 25 → Fin 64 :=
  ![0, 28, 1, 27, 62, 44, 20, 6, 36, 55, 43, 3, 25, 10, 39, 21, 45, 8, 15, 41, 14, 61, 18, 56, 2]

theorem clean_rhoPi (s : Vector Nat 25) :
    Specs.Keccak256.rhoPi s = Vector.ofFn fun c => rotLeft64 s[rhoPiSrc c] (rhoPiOff c) := by
  apply Vector.ext; intro c hc; interval_cases c <;> simp [Specs.Keccak256.rhoPi, rhoPiSrc, rhoPiOff]

theorem rhoPi_tables : ∀ c : Fin 25, cleanLane (rhoPiSrc c) = piSrc (cleanLane c) ∧
    (rhoPiOff c).val = rhoOffset (laneX (piSrc (cleanLane c))) (laneY (piSrc (cleanLane c))) := by
  decide

theorem rhoPi_clean (A : Vector Lane 25) : toClean (pi (rho A)) = Specs.Keccak256.rhoPi (toClean A) := by
  apply Vector.ext; intro c hc
  obtain ⟨h1, h2⟩ := rhoPi_tables ⟨c, hc⟩
  simp only [toClean, pi, rho, clean_rhoPi, Vector.getElem_ofFn, Fin.getElem_fin, rotLeft64_toNat, h1, h2]

theorem chi_clean (A : Vector Lane 25) : toClean (chi A) = Specs.Keccak256.chi (toClean A) := by
  apply Vector.ext; intro c hc
  interval_cases c <;> simp [-BitVec.toNat_not, toClean_get, chi, laneX, laneY, lane, Specs.Keccak256.chi,
    not64_toNat, ← BitVec.toNat_xor, ← BitVec.toNat_and]

theorem iota_clean (r : Fin 24) (A : Vector Lane 25) :
    toClean (iota r A) = Specs.Keccak256.iota (toClean A) Specs.Keccak256.roundConstants[r] := by
  apply Vector.ext; intro c hc
  simp only [toClean, iota, Specs.Keccak256.iota, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_set]
  by_cases h : c = 0
  · subst h
    simp [cleanLane, RC, UInt64.toFin_val]
  · rw [ite_eq_right (show ¬0 = (cleanLane ⟨c, hc⟩).val by simp only [cleanLane]; omega), ite_eq_right (Ne.symm h)]

theorem round_clean (r : Fin 24) (A : Vector Lane 25) :
    toClean (keccakRound r A) = Specs.Keccak256.keccakRound (toClean A) Specs.Keccak256.roundConstants[r] := by
  rw [keccakRound, iota_clean, chi_clean, rhoPi_clean, theta_clean]
  rfl

theorem toList_eq_map {α : Type} {n : Nat} (v : Vector α n) : v.toList = (List.finRange n).map fun i => v[i] := by
  apply List.ext_getElem <;> simp

theorem cleanLane_cleanLane : ∀ p, cleanLane (cleanLane p) = p := by decide

/-- FIPS 202's Keccak-f[1600] is Clean's (`keccakF`). -/
theorem fipsF_eq (A : Vector Lane 25) : fipsF A = keccakF A := by
  have hp : Specs.Keccak256.keccakPermutation (toClean A) = toClean (fipsF A) := by
    rw [Specs.Keccak256.keccakPermutation, ← Vector.foldl_toList, toList_eq_map, List.foldl_map, fipsF]
    generalize List.finRange 24 = l
    induction l generalizing A with
    | nil => rfl
    | cons r l ih => rw [List.foldl_cons, List.foldl_cons, ← round_clean, ih]
  have hk : keccakF A = Vector.ofFn fun p => BitVec.ofNat 64 (Specs.Keccak256.keccakPermutation (toClean A))[cleanLane p] :=
    rfl
  rw [hk, hp]
  apply Vector.ext; intro i hi
  simp only [toClean, Vector.getElem_ofFn, Fin.getElem_fin, Fin.eta, cleanLane_cleanLane, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Spec
