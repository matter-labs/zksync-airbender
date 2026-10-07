import Airbender.Proofs.JumpBranchSlt.Soundness
import Airbender.Proofs.JumpBranchSlt.Branch
import Airbender.Proofs.JumpBranchSlt.Jump
import Airbender.Proofs.JumpBranchSlt.BranchSoundness
import Airbender.Proofs.BabyBear

namespace Airbender.JumpBranchSlt
open Airbender.Arithmetic

/-- Partial family coverage: local flags, without decoded instruction meaning. -/
theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ k : Fin 5, w (11 + k.val) = 0 ∨ w (11 + k.val) = 1 :=
  Proofs.local_flags h

/-- Bounds from the four retained 16-bit queries. -/
theorem local_ranges {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 34).val < limbBase ∧ (w 35).val < limbBase ∧
      (w 1).val < limbBase ∧ (w 36).val < limbBase :=
  Proofs.local_ranges h

/-- Zero, sign, conditional-resolution and low-PC cleanup values follow from
    native Clean membership in the modeled fixed tables. Table provenance is unproved. -/
theorem lookup_values {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    w 41 = (if (w 34 + w 35).val = 0 then 1 else 0) ∧
    w 42 = (((w 23).val / 32768 : Nat) : ZMod p) ∧
    w 44 = (Verification.conditionalValue
      (w 43 + 65536 * w 42 + 131072 * w 38 + 262144 * w 41 + 524288 * w 10).val : ZMod p) ∧
    w 46 = (((w 36).val / 2 % 2 : Nat) : ZMod p) ∧
    w 16 = (((w 36).val - (w 36).val % 4 : Nat) : ZMod p) :=
  Proofs.lookup_values hp h

/-- Local field equations, without integer timestamp bounds or global ordering. -/
theorem timestamp_equations {p : Nat} [Fact p.Prime]
    (inverse : (-3840 : ZMod p) * 524288 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 18 + 524288 * c ∧ w 3 + c = w 19 :=
  Proofs.timestamp_equations inverse h

theorem babyBear_timestamp_equations {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 18 + 524288 * c ∧ w 3 + c = w 19 :=
  timestamp_equations (by decide) h

/-- The retained subtraction computes an unsigned comparison borrow. -/
theorem unsigned_borrow {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 38 = 1 ↔ left.value < right.value :=
  Proofs.unsigned_borrow hp h selected other mapping leftBound rightBound

/-- The local SLTU/SLTIU destination is the unsigned comparison bit, derived through
    the imported resolution lookup. -/
theorem unsigned_destination {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (funct3 : w 10 = 3) (nonzero : w 15 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    (⟨(w 30).val, (w 31).val⟩ : Word).value =
      if left.value < right.value then 1 else 0 :=
  Proofs.unsigned_destination hp h selected other funct3 nonzero mapping
    ⟨rfl, rfl⟩ leftBound rightBound

/-- The signed comparison result is proved through the same imported resolution
    query and subtraction borrow, using native bitvector signed ordering. -/
theorem signed_destination {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (funct3 : w 10 = 2) (nonzero : w 15 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    (⟨(w 30).val, (w 31).val⟩ : Word).value =
      if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0 :=
  Proofs.signed_destination hp h selected other funct3 nonzero mapping
    ⟨rfl, rfl⟩ leftBound rightBound

/-- The imported destination mask forces both limbs to zero for branches/x0 jumps. -/
theorem masked_destination {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (zero : w 15 = 1) : w 30 = 0 ∧ w 31 = 0 :=
  Proofs.masked_destination h zero

/-- Local condition correctness for BEQ/BNE/BLT/BGE/BLTU/BGEU (tags 0/1/4/5/6/7).
    Tags 2/3 have the same lookup comparisons. Operand bounds and decoder identity
    remain external; full Sail branch execution is not covered by this local claim. -/
theorem branch_resolution {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 14 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0)
    (funct3Bound : (w 10).val ≤ 7)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 = (right.lo : ZMod p) ∧ w 27 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 45 = ((match (w 10).val with
      | 0 => if left.toBitVec = right.toBitVec then 1 else 0
      | 1 => if left.toBitVec ≠ right.toBitVec then 1 else 0
      | 2 | 4 => if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0
      | 3 | 6 => if left.value < right.value then 1 else 0
      | 5 => if ¬ left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0
      | _ => if ¬ left.value < right.value then 1 else 0 : Nat) : ZMod p) :=
  Proofs.branch_resolution hp h selected other funct3Bound mapping leftBound rightBound

/-- Local PC selection and alignment, including wrapping and negative offsets.
    The resolved bit is supplied by `branch_resolution`; this is not yet a Sail
    architectural-step claim. Input/offset bounds and the final high bound are explicit. -/
theorem branch_pc {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {initial offset final : Word} (taken : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 14 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0)
    (resolved : w 45 = if taken then 1 else 0)
    (mapping : initial.lo = (w 0).val ∧ initial.hi = (w 1).val ∧
      w 8 = (offset.lo : ZMod p) ∧ w 9 = (offset.hi : ZMod p) ∧
      final.lo = (w 16).val ∧ final.hi = (w 17).val)
    (initialLoBound : initial.lo < limbBase) (initialAligned : initial.lo % 4 = 0)
    (offsetBound : offset.Bounded) (offsetEven : offset.lo % 2 = 0)
    (finalHiBound : final.hi < limbBase) :
    final.toBitVec = (if taken then initial.toBitVec + offset.toBitVec else initial.toBitVec + 4) ∧
      final.toBitVec.toNat % 4 = 0 :=
  Proofs.branch_pc hp taken h selected other resolved mapping initialLoBound initialAligned offsetBound offsetEven finalHiBound

/-- JAL and JALR share the saved PC+4 word and destination mask. The mask's
    meaning as rd=x0 is a decoder obligation; its Booleanity is imported. -/
theorem jump_link {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {initial : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 + w 12 = 1) (other : w 13 = 0 ∧ w 14 = 0)
    (mapping : initial.lo = (w 0).val ∧ initial.hi = (w 1).val)
    (initialLoBound : initial.lo < limbBase) :
    (⟨(w 30).val, (w 31).val⟩ : Word).toBitVec =
      (if w 15 = 1 then 0 else initial.toBitVec + 4) ∧
    (⟨(w 30).val, (w 31).val⟩ : Word).Bounded :=
  Proofs.jump_link hp h selected other mapping initialLoBound

/-- Local JAL/JALR targets: `base` is PC for JAL, rs1 for JALR. The bit-1
    assertion enforces four-byte alignment; JALR may clear an odd sum's bit 0.
    Bounds, direct-offset parity and selector identity remain interfaces. -/
theorem jump_pc {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {base offset final : Word} (indirect : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = (if indirect then 0 else 1) ∧ w 12 = (if indirect then 1 else 0))
    (other : w 13 = 0 ∧ w 14 = 0)
    (mapping : base.lo = (w (if indirect then 22 else 0)).val ∧
      base.hi = (w (if indirect then 23 else 1)).val ∧
      w 8 = (offset.lo : ZMod p) ∧ w 9 = (offset.hi : ZMod p) ∧
      final.lo = (w 16).val ∧ final.hi = (w 17).val)
    (baseLoBound : base.lo < limbBase)
    (sourceHiBound : indirect = true → base.hi < limbBase)
    (offsetBound : offset.Bounded)
    (directEven : indirect = false → base.lo % 2 = 0 ∧ offset.lo % 2 = 0)
    (finalHiBound : final.hi < limbBase) :
    final.toBitVec = (if indirect then (base.toBitVec + offset.toBitVec) &&& 0xfffffffe
      else base.toBitVec + offset.toBitVec) ∧ final.toBitVec.toNat % 4 = 0 :=
  Proofs.jump_pc hp indirect h selected other mapping baseLoBound sourceHiBound
    offsetBound directEven finalHiBound

namespace Comparison

/-- Shared soundness for SLT, SLTI, SLTU and SLTIU against native Sail register
    and PC effects. Alignment and the final-PC high bound are explicit
    interfaces; the imported arithmetic allows 32-bit PC wraparound. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.comparison_soundness hp

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide)

end Comparison

namespace Branch

/-- All six standard branches satisfy the shared native Sail state-transition
    property. Taken targets, fall-through and alignment follow from the artifact;
    operand/offset bounds, decoding and initialized native reads remain interfaces. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.branch_soundness hp

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide)

end Branch

end Airbender.JumpBranchSlt
