module
public import Slop.KeccakSplit.ThetaRho.Output
public import Slop.KeccakSplit.ThetaRho.Rotate

@[expose] public section

/- Each written state lane of a theta/rho call is rho of (lane ^ D) (ported from PR
   #585's SplitThetaOutputBytes, SplitThetaOutputPacking, SplitThetaLaneOperation and
   SplitThetaReferenceEffect). -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

/-- The eight state bytes XOR D of lane `lane`. -/
noncomputable def xoredBytes (w : Nat → ZMod babyBearModulus) (lane : Fin 5) : Vector Nat 8 :=
  Vector.ofFn fun digit : Fin 8 => (stateByte w lane digit).val ^^^ (dByte w digit).val

theorem xored_byte_bound {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 5) (digit : Fin 8) :
    (xoredBytes w lane)[digit] < 256 := by
  have bound := Nat.xor_lt_two_pow (n := 8) (state_byte_bound h lane digit)
    (d_operand_bounds h digit).2.2
  simpa [xoredBytes] using bound

theorem output_byte_value {w : Nat → ZMod babyBearModulus} (h : Holds w) (column lane : Fin 5)
    (digit : Fin 8)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = column.val then 1 else 0) :
    (outputByte w lane (Call.rotations[column][lane]) digit).val =
      rotatedLaneByte (xoredBytes w lane) (Call.rotations[column][lane]) digit := by
  let left := Call.rotations[column][lane]
  let bytes := xoredBytes w lane
  let source := byteRotationSource left digit
  let prior := byteRotationPrevious source
  have low := (fragment_byte_operation h lane source).1
  have high := (fragment_byte_operation h lane prior).2
  have shift := rotation_shift_value w column lane flags
  change (rotationShift w lane).val = left.val % 8 at shift
  rw [shift] at low high
  have lowValue : (fragmentByte w false lane source).val = (bytes[source] * 2 ^ (left.val % 8)) % 256 := by
    simpa [bytes, xoredBytes] using low
  have highValue : (fragmentByte w true lane prior).val = bytes[prior] / 2 ^ (8 - left.val % 8) := by
    simpa [bytes, xoredBytes] using high
  have priorIndex : (⟨(digit.val + 7 - left.val / 8) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) = prior := by
    apply Fin.ext
    dsimp [prior, source, byteRotationSource, byteRotationPrevious]
    have := left.isLt
    have := digit.isLt
    omega
  have output : outputByte w lane left digit =
      fragmentByte w false lane source + if left.val % 8 = 0 then 0 else fragmentByte w true lane prior := by
    dsimp only [outputByte]
    rw [priorIndex]
    rfl
  change (outputByte w lane left digit).val = rotatedLaneByte bytes left digit
  rw [output]
  by_cases zero : left.val % 8 = 0
  · simp only [zero, ↓reduceIte, add_zero]
    rw [lowValue]
    have priorBound : bytes[prior] < 256 := xored_byte_bound h lane prior
    change (bytes[source] * 2 ^ (left.val % 8)) % 256 =
      (bytes[source] * 2 ^ (left.val % 8)) % 256 + bytes[prior] / 2 ^ (8 - left.val % 8)
    simp only [zero, Nat.sub_zero, Nat.reducePow, Nat.div_eq_of_lt priorBound, Nat.add_zero]
  · simp only [zero, ↓reduceIte]
    have lowBound := fragment_byte_bound h false lane source
    have highBound := fragment_byte_bound h true lane prior
    have small : (fragmentByte w false lane source).val + (fragmentByte w true lane prior).val <
        babyBearModulus := lt_of_lt_of_le (by omega : _ < 512) (by decide)
    have cast : (((fragmentByte w false lane source).val + (fragmentByte w true lane prior).val : Nat) :
        ZMod babyBearModulus) = fragmentByte w false lane source + fragmentByte w true lane prior := by
      simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    rw [← cast, ZMod.val_natCast_of_lt small, lowValue, highValue]
    rfl

theorem output_byte_bound {w : Nat → ZMod babyBearModulus} (h : Holds w) (column lane : Fin 5)
    (digit : Fin 8)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = column.val then 1 else 0) :
    (outputByte w lane (Call.rotations[column][lane]) digit).val < 256 := by
  rw [output_byte_value h column lane digit flags]
  exact rotated_lane_byte_bound (xored_byte_bound h lane) _ digit

theorem write_limb_value {w : Nat → ZMod babyBearModulus} (h : Holds w) (column lane : Fin 5)
    (limb : Fin 4)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = column.val then 1 else 0) :
    (limbOf w true ⟨lane.val, by omega⟩ limb).val < 65536 ∧
      (limbOf w true ⟨lane.val, by omega⟩ limb).val =
        (outputByte w lane (Call.rotations[column][lane]) ⟨2 * limb.val, by omega⟩).val +
          256 * (outputByte w lane (Call.rotations[column][lane]) ⟨2 * limb.val + 1, by omega⟩).val := by
  have low := output_byte_bound h column lane ⟨2 * limb.val, by omega⟩ flags
  have high := output_byte_bound h column lane ⟨2 * limb.val + 1, by omega⟩ flags
  have equation := selected_output h column lane limb flags
  have value := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide) low high
    equation.symm
  exact ⟨by rw [value]; omega, value⟩

theorem write_limb_rotation {w : Nat → ZMod babyBearModulus} (h : Holds w) (column lane : Fin 5)
    (limb : Fin 4)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = column.val then 1 else 0) :
    (limbOf w true ⟨lane.val, by omega⟩ limb).val =
      rotatedLaneByte (xoredBytes w lane) (Call.rotations[column][lane]) ⟨2 * limb.val, by omega⟩ +
        256 * rotatedLaneByte (xoredBytes w lane) (Call.rotations[column][lane])
          ⟨2 * limb.val + 1, by omega⟩ := by
  rw [(write_limb_value h column lane limb flags).2,
    output_byte_value h column lane ⟨2 * limb.val, by omega⟩ flags,
    output_byte_value h column lane ⟨2 * limb.val + 1, by omega⟩ flags]

/-- The four memory limbs of a lane as one 64-bit value. -/
def laneValue (w : Nat → ZMod babyBearModulus) (writing : Bool) (lane : Fin 7) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => (limbOf w writing lane limb).val)

theorem readonly_lane (w : Nat → ZMod babyBearModulus) (lane : Fin 2) :
    laneValue w true ⟨5 + lane.val, by omega⟩ = laneValue w false ⟨5 + lane.val, by omega⟩ := by
  unfold laneValue
  congr 1
  apply Vector.ext
  intro limb bound
  simpa only [Vector.getElem_ofFn] using congrArg ZMod.val (readonly_limb w lane ⟨limb, bound⟩)

theorem state_lane_bytes {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 5) :
    laneValue w false ⟨lane.val, by omega⟩ =
      packByteLane (Vector.ofFn fun digit : Fin 8 => (stateByte w lane digit).val) := by
  let bytes := Vector.ofFn fun digit : Fin 8 => (stateByte w lane digit).val
  calc
    _ = packLane (Vector.ofFn fun limb : Fin 4 =>
        bytes[(⟨2 * limb.val, by omega⟩ : Fin 8)] + 256 * bytes[(⟨2 * limb.val + 1, by omega⟩ : Fin 8)]) := by
      unfold laneValue
      congr 1
      apply Vector.ext
      intro limb bound
      simpa [bytes] using (state_limb_value h lane ⟨limb, bound⟩).2
    _ = _ := pack_byte_pairs bytes

theorem d_lane_bytes (w : Nat → ZMod babyBearModulus) :
    dLaneValue w = packByteLane (Vector.ofFn fun digit : Fin 8 => (dByte w digit).val) := by
  let bytes := Vector.ofFn fun digit : Fin 8 => (dByte w digit).val
  change packLane (Vector.ofFn fun limb : Fin 4 => dLimbValue w limb) = _
  calc
    _ = packLane (Vector.ofFn fun limb : Fin 4 =>
        bytes[(⟨2 * limb.val, by omega⟩ : Fin 8)] + 256 * bytes[(⟨2 * limb.val + 1, by omega⟩ : Fin 8)]) := by
      rfl
    _ = _ := pack_byte_pairs bytes

theorem xored_lane_value {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 5) :
    packByteLane (xoredBytes w lane) = laneValue w false ⟨lane.val, by omega⟩ ^^^ dLaneValue w := by
  rw [state_lane_bytes h lane, d_lane_bytes]
  let a := Vector.ofFn fun digit : Fin 8 => (stateByte w lane digit).val
  let b := Vector.ofFn fun digit : Fin 8 => (dByte w digit).val
  have aBound (digit : Fin 8) : a[digit] < 256 := by
    simpa [a] using state_byte_bound h lane digit
  have bBound (digit : Fin 8) : b[digit] < 256 := by
    simpa [b] using (d_operand_bounds h digit).2.2
  simpa [a, b, xoredBytes] using pack_byte_lane_xor aBound bBound

theorem write_lane_bytes {w : Nat → ZMod babyBearModulus} (h : Holds w) (column lane : Fin 5)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = column.val then 1 else 0) :
    laneValue w true ⟨lane.val, by omega⟩ =
      packByteLane ((Vector.finRange 8).map
        (rotatedLaneByte (xoredBytes w lane) (Call.rotations[column][lane]))) := by
  let bytes := (Vector.finRange 8).map (rotatedLaneByte (xoredBytes w lane) (Call.rotations[column][lane]))
  calc
    _ = packLane (Vector.ofFn fun limb : Fin 4 =>
        bytes[(⟨2 * limb.val, by omega⟩ : Fin 8)] + 256 * bytes[(⟨2 * limb.val + 1, by omega⟩ : Fin 8)]) := by
      unfold laneValue
      congr 1
      apply Vector.ext
      intro limb bound
      simpa [bytes] using write_limb_rotation h column lane ⟨limb, bound⟩ flags
    _ = _ := pack_byte_pairs bytes

theorem lane_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (column lane : Fin 5)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = column.val then 1 else 0)
    (bounds : ∀ limb : Fin 4, (limbOf w false 6 limb).val < 65536) :
    laneValue w true ⟨lane.val, by omega⟩ =
      rotLeft64 (laneValue w false ⟨lane.val, by omega⟩ ^^^
        (laneValue w false 5 ^^^ rotLeft64 (laneValue w false 6) 1)) (Call.rotations[column][lane]) := by
  rw [write_lane_bytes h column lane flags, ← rotate_rho (xored_byte_bound h lane),
    xored_lane_value h lane, d_reference h bounds]
  rfl

/-- The seven lanes of a theta/rho row. -/
def refLanes (w : Nat → ZMod babyBearModulus) (writing : Bool) : Vector Nat 7 :=
  Vector.ofFn (laneValue w writing)

theorem reference_result {w : Nat → ZMod babyBearModulus} (h : Holds w) (index : Fin 361)
    (kind : kindAt index.val = .thetaRho)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = index.val % 5 then 1 else 0)
    (bounds : ∀ limb : Fin 4, (limbOf w false 6 limb).val < 65536) :
    Call.result index (refLanes w false) = refLanes w true := by
  let column : Fin 5 := ⟨index.val % 5, Nat.mod_lt _ (by decide)⟩
  have selected : ∀ flag : Fin 5, columnFlag w flag = if flag.val = column.val then 1 else 0 := flags
  simp only [Call.result, kind]
  apply Vector.ext
  intro lane bound
  by_cases live : lane < 5
  · simp only [Vector.getElem_ofFn, live, ↓reduceDIte, refLanes, Fin.getElem_fin]
    exact (lane_operation h column ⟨lane, live⟩ selected bounds).symm
  · have laneIndex : 5 + (lane - 5) = lane := by omega
    have same := readonly_lane w ⟨lane - 5, by omega⟩
    simp only [refLanes, Vector.getElem_ofFn, Fin.getElem_fin, live, ↓reduceDIte]
    simpa only [laneIndex] using same.symm

end Airbender.Keccak.Split.ThetaRho.Proofs
