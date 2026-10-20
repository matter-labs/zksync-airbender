import Slop.Sail.Sequential
import Slop.Arithmetic.Word

namespace Airbender.Reference.Sail

-- Properties of successful outputs of the existing Sail interpreter. These
-- proof rules inspect the original generated decoder, without reimplementing it.
private def Returns {α : Type} (property : α → Prop) (action : SailRV32.SailM α) : Prop :=
  ∀ before value after, run action before = .ok value after → property value

private theorem returns_pure {α : Type} (property : α → Prop) (value : α)
    (h : property value) : Returns property (pure value) := by
  intro before actual after executed
  exact (EStateM.Result.ok.inj executed).1 ▸ h

private theorem returns_bind {α β : Type} (property : β → Prop)
    (action : SailRV32.SailM α) (next : α → SailRV32.SailM β)
    (h : ∀ value, Returns property (next value)) : Returns property (action >>= next) := by
  intro before value after executed
  cases first : run action before with
  | error error middle =>
    rw [run_bind_of_error _ _ _ _ _ first] at executed
    cases executed
  | ok result middle =>
    rw [run_bind_of_ok _ _ _ _ _ first] at executed
    exact h result middle value after executed

private theorem returns_ite {α : Type} (property : α → Prop) (condition : Prop)
    [Decidable condition] (yes no : SailRV32.SailM α)
    (hy : Returns property yes) (hn : Returns property no) :
    Returns property (if condition then yes else no) := by
  by_cases selected : condition <;> simp [selected, hy, hn]

private def optionProperty {α : Type} (property : α → Prop) : Option α → Prop
  | none => True
  | some value => property value

private theorem returns_bind_with {α β : Type} (property : β → Prop)
    (firstProperty : α → Prop) (action : SailRV32.SailM α)
    (next : α → SailRV32.SailM β)
    (hfirst : Returns firstProperty action)
    (hnext : ∀ value, firstProperty value → Returns property (next value)) :
    Returns property (action >>= next) := by
  intro before value after executed
  cases firstRun : run action before with
  | error error middle =>
    rw [run_bind_of_error _ _ _ _ _ firstRun] at executed
    cases executed
  | ok result middle =>
    rw [run_bind_of_ok _ _ _ _ _ firstRun] at executed
    exact hnext result (hfirst before result middle firstRun) middle value after executed

private def evenOffsets : SailRV32.instruction → Prop
  | .JAL (imm, _) => imm.toNat % 2 = 0
  | .BTYPE (imm, _, _, _) => imm.toNat % 2 = 0
  | _ => True

private theorem appended_zero_even {n : Nat} (upperBits : BitVec n) :
    (upperBits +++ (0 : BitVec 1)).toNat % 2 = 0 := by
  change (upperBits.toNat <<< 1 ||| 0) % 2 = 0
  simp [Nat.shiftLeft_eq]

attribute [irreducible] Returns

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
/-- The original decoder supplies the implicit zero bit of JAL/branch offsets.
    This holds for successful decoding, including any effects in other clauses. -/
theorem decoded_offset_even (bits : BitVec 32) :
    ∀ before instruction after,
      run (SailRV32.Functions.encdec_backwards bits) before = .ok instruction after →
      match instruction with
      | .JAL (imm, _) => imm.toNat % 2 = 0
      | .BTYPE (imm, _, _, _) => imm.toNat % 2 = 0
      | _ => True := by
  have checked : Returns evenOffsets (SailRV32.Functions.encdec_backwards bits) := by
    unfold SailRV32.Functions.encdec_backwards
    repeat' first
      | assumption
      | trivial
      | (apply returns_pure; dsimp [optionProperty, evenOffsets])
      | (apply returns_bind_with (firstProperty := optionProperty evenOffsets) <;>
          try (intro result satisfies; cases result))
      | apply returns_ite
      | (apply returns_bind; intro)
      | exact appended_zero_even _
      | split
      | (unfold Returns; intro before value after executed; cases executed)
  unfold Returns at checked
  exact checked

/-- Word encoding and sign extension preserve the decoded offset's zero bit. -/
theorem sign_extend_low_even {n : Nat} (positive : 0 < n) (bits : BitVec n)
    (even : bits.toNat % 2 = 0) :
    (Arithmetic.Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) bits)).lo % 2 = 0 := by
  have low : bits.getLsbD 0 = false := Nat.mod_two_eq_zero_iff_testBit_zero.mp even
  have extended : (bits.signExtend 32).getLsbD 0 = false := by
    rw [BitVec.getLsbD_signExtend, if_pos positive, low, Bool.and_false]
  have evenExtended : (bits.signExtend 32).toNat % 2 = 0 :=
    Nat.mod_two_eq_zero_iff_testBit_zero.mpr extended
  change ((bits.signExtend 32).toNat % 65536) % 2 = 0
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 65536)]
  exact evenExtended

end Airbender.Reference.Sail
