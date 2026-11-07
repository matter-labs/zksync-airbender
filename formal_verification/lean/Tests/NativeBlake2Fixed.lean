import Airbender.Review.Circuits.Blake2Worker.TablesTheorems

namespace Airbender.Tests.NativeBlake2Fixed
open Verification Blake2Worker Blake2Worker.Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Every stored native row participates, including both ends of all five regions. -/
theorem all_rows (kind : Kind) (i : Fin (data kind).length) :
    (table (p := mersenne31Modulus)).Contains #[] ((data kind).row i) :=
  FixedProofs.every_row kind i

theorem native_geometry : Kind.byte.offset = 0 ∧ Kind.three.offset = 65536 ∧
    Kind.four.offset = 65600 ∧ Kind.seven.offset = 65856 ∧ Kind.nine.offset = 82240 ∧
    dataT29.length = 262144 := by decide

theorem xor3_positive : (table (p := mersenne31Modulus)).Contains #[] #v[7,5,2,26] := by
  have actual := FixedProofs.every_row .three ⟨61,by decide⟩
  have literal : ((data .three).row ⟨61,by decide⟩ : Vector (ZMod mersenne31Modulus) 4) = #v[7,5,2,26] := by decide +kernel
  rw [literal] at actual
  exact actual

theorem xor4_positive : (table (p := mersenne31Modulus)).Contains #[] #v[15,9,6,27] := by
  have actual := FixedProofs.every_row .four ⟨249,by decide⟩
  have literal : ((data .four).row ⟨249,by decide⟩ : Vector (ZMod mersenne31Modulus) 4) = #v[15,9,6,27] := by decide +kernel
  rw [literal] at actual
  exact actual

theorem absent_csr_tag (query : Vector (ZMod mersenne31Modulus) 4)
    (tag : query[3] = 25) : ¬ (table (p := mersenne31Modulus)).Contains #[] query := by
  intro member
  obtain ⟨kind,selected,_,_⟩ := input_properties query member
  rw [tag] at selected
  have numeral : (25 : ZMod mersenne31Modulus).val = 25 := by decide
  rw [numeral] at selected
  cases kind <;> contradiction

theorem oversized_operand (query : Vector (ZMod mersenne31Modulus) 4)
    (oversized : 512 ≤ query[0].val) : ¬ (table (p := mersenne31Modulus)).Contains #[] query := by
  intro member
  obtain ⟨kind,_,bound,_⟩ := input_properties query member
  have maximum : kind.bound ≤ 512 := by cases kind <;> decide
  omega

theorem xor3_forgery (query : Vector (ZMod mersenne31Modulus) 4)
    (tag : query[3] = 26) (forged : query[2].val ≠ query[0].val ^^^ query[1].val) :
    ¬ (table (p := mersenne31Modulus)).Contains #[] query := by
  exact fun member => forged (three_xor query member tag)

theorem xor4_forgery (query : Vector (ZMod mersenne31Modulus) 4)
    (tag : query[3] = 27) (forged : query[2].val ≠ query[0].val ^^^ query[1].val) :
    ¬ (table (p := mersenne31Modulus)).Contains #[] query := by
  exact fun member => forged (four_xor query member tag)

theorem xor7_forgery (query : Vector (ZMod mersenne31Modulus) 4)
    (tag : query[3] = 28) (forged : query[2].val ≠ query[0].val ^^^ query[1].val) :
    ¬ (table (p := mersenne31Modulus)).Contains #[] query := by
  exact fun member => forged (seven_xor query member tag)

theorem xor9_forgery (query : Vector (ZMod mersenne31Modulus) 4)
    (tag : query[3] = 29) (forged : query[2].val ≠ query[0].val ^^^ query[1].val) :
    ¬ (table (p := mersenne31Modulus)).Contains #[] query := by
  exact fun member => forged (nine_xor query member tag)

/-- Reused byte literals do not identify the worker pool with an old main pool. -/
theorem byte_literal_binding : dataT4.columns = NativeBinary.dataXor.columns ∧ Kind.byte.offset = 0 :=
  ⟨FixedProofs.byte_columns,rfl⟩

theorem last_xor9_inputs :
    ((dataT29.row ⟨262143,by decide⟩ : Vector (ZMod mersenne31Modulus) 4)[0]).val = 511 ∧
    ((dataT29.row ⟨262143,by decide⟩ : Vector (ZMod mersenne31Modulus) 4)[1]).val = 511 := by
  have actual := FixedProofs.fields .nine ⟨262143,by decide⟩
  exact ⟨actual.1,actual.2.1⟩

end Airbender.Tests.NativeBlake2Fixed
