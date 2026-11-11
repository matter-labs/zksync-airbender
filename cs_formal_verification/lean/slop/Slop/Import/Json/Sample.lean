module
public import Human.Import.Theorems
public import Slop.Import.Json.Index
import all Init.Data.Repr -- Init.Data.Repr is not exposed (still true in 4.35)
import all Init.Data.String.Defs -- Init.Data.Repr is not exposed (still true in 4.35)
import all Init.Data.Int.Repr -- Int.repr is not exposed

@[expose] public section

/-! The parser on the two sample texts, evaluated by the kernel (through the list parser, `parse_eq`). `Value` has no `DecidableEq`, so the result is
compared with a Boolean equality proven sound here. -/

namespace Airbender.Json.Parser
open Airbender.Json

mutual
def valueBeq : Value → Value → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .str a, .str b => a == b
  | .arr as, .arr bs => itemsBeq as bs
  | .obj as, .obj bs => membersBeq as bs
  | _, _ => false
def itemsBeq : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => valueBeq a b && itemsBeq as bs
  | _, _ => false
def membersBeq : List (String × Value) → List (String × Value) → Bool
  | [], [] => true
  | (k, a) :: as, (k', b) :: bs => k == k' && valueBeq a b && membersBeq as bs
  | _, _ => false
end

mutual
theorem valueBeq_sound : ∀ v w : Value, valueBeq v w = true → v = w
  | .null, w, h => by cases w <;> simp_all [valueBeq]
  | .bool a, w, h => by cases w <;> simp_all [valueBeq]
  | .int a, w, h => by cases w <;> simp_all [valueBeq]
  | .str a, w, h => by cases w <;> simp_all [valueBeq]
  | .arr as, w, h => by
    cases w with
    | arr bs => rw [itemsBeq_sound as bs (by simpa [valueBeq] using h)]
    | _ => simp [valueBeq] at h
  | .obj as, w, h => by
    cases w with
    | obj bs => rw [membersBeq_sound as bs (by simpa [valueBeq] using h)]
    | _ => simp [valueBeq] at h
theorem itemsBeq_sound : ∀ as bs : List Value, itemsBeq as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [itemsBeq]
  | a :: as, [], h => by simp [itemsBeq] at h
  | a :: as, b :: bs, h => by
    simp only [itemsBeq, Bool.and_eq_true] at h
    rw [valueBeq_sound a b h.1, itemsBeq_sound as bs h.2]
theorem membersBeq_sound : ∀ as bs : List (String × Value), membersBeq as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [membersBeq]
  | (k, a) :: as, [], h => by simp [membersBeq] at h
  | (k, a) :: as, (k', b) :: bs, h => by
    simp only [membersBeq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, valueBeq_sound a b h.1.2, membersBeq_sound as bs h.2]
end

theorem parse_sample : parse sample.toUTF8 = .ok sampleValue := by
  rw [parse_eq]
  have h : (match parseReference sample.toUTF8 with
    | .ok v => valueBeq v sampleValue
    | .error _ => false) = true := by decide +kernel
  revert h
  generalize parseReference sample.toUTF8 = r
  cases r with
  | ok v => intro h; rw [valueBeq_sound v sampleValue h]
  | error e => intro h; simp at h

theorem parse_duplicate : (parse duplicate.toUTF8).toBool = false := by rw [parse_eq]; decide +kernel

end Airbender.Json.Parser
