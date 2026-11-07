import Airbender.Proofs.Blake2Worker.Xor7Certificate
import Airbender.Proofs.Blake2Worker.Xor9Certificate
import Airbender.Proofs.Blake2Worker.NativeFixed
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2Worker.FixedProofs
open Fixed Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem tag_injective : Function.Injective Kind.tag := by
  intro a b equal
  cases a <;> cases b <;> simp_all [Kind.tag]

theorem selected_region (kind : Kind) (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3].val = kind.tag) :
    ∃ i : Fin (data kind).length, query = (data kind).row i := by
  obtain ⟨other,i,same⟩ := member_region query member
  have tag := (fields other i).2.2
  have equal : other.tag = kind.tag := by rw [← tag,← same]; exact selected
  have kinds := tag_injective equal
  subst other
  exact ⟨i,same⟩

theorem byte_result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (4 : ZMod mersenne31Modulus)) :
    query[0].val < 256 ∧ query[1].val < 256 ∧ query[2].val < 256 ∧
      BitVec.ofNat 8 query[2].val = byteOperation 4 (BitVec.ofNat 8 query[0].val) (BitVec.ofNat 8 query[1].val) := by
  have tag : query[3].val = Kind.byte.tag := by rw [selected]; decide
  obtain ⟨i,same⟩ := selected_region .byte query member tag
  have literal := congrArg (fun columns : Vector Setup.Column 4 =>
    (columns.map (fun column => (column.get? i.val).getD 0)).map
      (fun n : Nat => (n : ZMod mersenne31Modulus))) byte_columns
  have reconstruct : (#v[query[0],query[1],query[2]]).push (4 : ZMod mersenne31Modulus) = query := by
    ext lane bound
    interval_cases lane <;> simp [selected]
  have actual : NativeBinary.Contains .xor #v[query[0],query[1],query[2]] := by
    exact ⟨i,reconstruct.trans (same.trans literal)⟩
  exact native_binary_result .xor _ actual

theorem three_result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (26 : ZMod mersenne31Modulus)) :
    query[2].val = query[0].val ^^^ query[1].val := by
  have tag : query[3].val = Kind.three.tag := by rw [selected]; decide
  obtain ⟨i,rfl⟩ := selected_region .three query member tag
  obtain ⟨first,second,_⟩ := fields .three i
  rw [first,second]
  exact xor3 i

theorem four_result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (27 : ZMod mersenne31Modulus)) :
    query[2].val = query[0].val ^^^ query[1].val := by
  have tag : query[3].val = Kind.four.tag := by rw [selected]; decide
  obtain ⟨i,rfl⟩ := selected_region .four query member tag
  obtain ⟨first,second,_⟩ := fields .four i
  rw [first,second]
  exact xor4 i

theorem seven_result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (28 : ZMod mersenne31Modulus)) :
    query[2].val = query[0].val ^^^ query[1].val := by
  have tag : query[3].val = Kind.seven.tag := by rw [selected]; decide
  obtain ⟨i,rfl⟩ := selected_region .seven query member tag
  obtain ⟨first,second,_⟩ := fields .seven i
  rw [first,second]
  exact Xor7Certificate.output_value i

theorem nine_result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (29 : ZMod mersenne31Modulus)) :
    query[2].val = query[0].val ^^^ query[1].val := by
  have tag : query[3].val = Kind.nine.tag := by rw [selected]; decide
  obtain ⟨i,rfl⟩ := selected_region .nine query member tag
  obtain ⟨first,second,_⟩ := fields .nine i
  rw [first,second]
  exact Xor9Certificate.output_value i

end Airbender.Blake2Worker.FixedProofs
