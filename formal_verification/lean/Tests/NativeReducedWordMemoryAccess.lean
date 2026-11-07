import Airbender.Review.Circuits.ReducedMachine.WordMemoryTheorems
import Airbender.Review.Circuits.ReducedMachine.Tables.WordMemoryTheorems
import Airbender.Proofs.ReducedMachine.NativeWordMemoryNumerics

namespace Tests.NativeReducedWordMemoryAccess
open Airbender Arithmetic ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Every actual offset row is lifted at its exact native pool offset. -/
theorem actual_offset_rows (i : Fin 65536) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      ((NativeFixed.wordOffsetRow i.val).map Nat.cast) := by
  refine ⟨⟨i.val+327681,by change i.val+327681 < 5771521; have := i.isLt; omega⟩,?_⟩
  change _ = (NativeFixed.rowNat ⟨i.val+327681,_⟩).map Nat.cast
  have h0 : ¬ i.val+327681 < 1 := by omega
  have h1 : ¬ i.val+327681 < 65537 := by omega
  have h2 : ¬ i.val+327681 < 131073 := by omega
  have h3 : ¬ i.val+327681 < 196609 := by omega
  have h4 : ¬ i.val+327681 < 262145 := by omega
  have h5 : ¬ i.val+327681 < 327681 := by omega
  have selected : i.val+327681 < 393217 := by have := i.isLt; omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  exact congrArg (fun v : Vector Nat 4 => v.map (Nat.cast : Nat → ZMod mersenne31Modulus))
    (NativeWordMemoryTableProofs.offset_rows i).symm

/-- Every actual separator row is lifted at its exact native pool offset. -/
theorem actual_separator_rows (i : Fin 65536) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      ((NativeFixed.wordSeparatorRow i.val).map Nat.cast) := by
  refine ⟨⟨i.val+393473,by change i.val+393473 < 5771521; have := i.isLt; omega⟩,?_⟩
  change _ = (NativeFixed.rowNat ⟨i.val+393473,_⟩).map Nat.cast
  have h0 : ¬ i.val+393473 < 1 := by omega
  have h1 : ¬ i.val+393473 < 65537 := by omega
  have h2 : ¬ i.val+393473 < 131073 := by omega
  have h3 : ¬ i.val+393473 < 196609 := by omega
  have h4 : ¬ i.val+393473 < 262145 := by omega
  have h5 : ¬ i.val+393473 < 327681 := by omega
  have h6 : ¬ i.val+393473 < 393217 := by omega
  have h7 : ¬ i.val+393473 < 393345 := by omega
  have h8 : ¬ i.val+393473 < 393473 := by omega
  have selected : i.val+393473 < 459009 := by have := i.isLt; omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  exact congrArg (fun v : Vector Nat 4 => v.map (Nat.cast : Nat → ZMod mersenne31Modulus))
    (NativeWordMemoryTableProofs.separator_rows i).symm

/-- Every actual rom row is lifted at its exact native pool offset. -/
theorem actual_rom_rows (i : Fin 1048576) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      ((NativeFixed.wordROMRow i.val).map Nat.cast) := by
  refine ⟨⟨i.val+459009,by change i.val+459009 < 5771521; have := i.isLt; omega⟩,?_⟩
  change _ = (NativeFixed.rowNat ⟨i.val+459009,_⟩).map Nat.cast
  have h0 : ¬ i.val+459009 < 1 := by omega
  have h1 : ¬ i.val+459009 < 65537 := by omega
  have h2 : ¬ i.val+459009 < 131073 := by omega
  have h3 : ¬ i.val+459009 < 196609 := by omega
  have h4 : ¬ i.val+459009 < 262145 := by omega
  have h5 : ¬ i.val+459009 < 327681 := by omega
  have h6 : ¬ i.val+459009 < 393217 := by omega
  have h7 : ¬ i.val+459009 < 393345 := by omega
  have h8 : ¬ i.val+459009 < 393473 := by omega
  have h9 : ¬ i.val+459009 < 459009 := by omega
  have selected : i.val+459009 < 1507585 := by have := i.isLt; omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_neg h9,dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  exact congrArg (fun v : Vector Nat 4 => v.map (Nat.cast : Nat → ZMod mersenne31Modulus))
    (NativeWordMemoryTableProofs.rom_rows i).symm

/-- Exact linkage to all eight retained public fixture words, not an arbitrary
    original Sail image or a physical preprocessing certificate. -/
theorem rom_public_image (i : Fin 8) :
    NativeFixed.dataImage.get? i.val = some
      ((NativeFixed.wordROMValue i.val)[0]+65536*(NativeFixed.wordROMValue i.val)[1]) := by
  fin_cases i <;> decide +kernel

theorem independent_table_edges :
    NativeFixed.wordOffsetRow 65535 = #v[65535,1,1,18] ∧
    NativeFixed.wordSeparatorRow 63 = #v[63,0,63,23] ∧
    NativeFixed.wordSeparatorRow 64 = #v[64,1,0,23] ∧
    NativeFixed.wordSeparatorRow 65535 = #v[65535,1,63,23] ∧
    NativeFixed.wordROMRow 0 = #v[0,32947,16,24] ∧
    NativeFixed.wordROMRow 1048575 = #v[4194300,4211,49152,24] := by decide +kernel

theorem load_shadow_corruption_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (1025 : ZMod mersenne31Modulus)) (bad : w 39 ≠ w 61) : False := by
  have address := (word_load_access holds mask).shadowAddress
  exact bad (by simpa using congrArg (fun q : Vector (ZMod mersenne31Modulus) 2 => q[0]) address)

theorem store_zero_flag_does_not_discard {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (16386 : ZMod mersenne31Modulus)) :
    w 8 = 1 → #v[w 43,w 44] = #v[w 37,w 38] := fun _ => (word_store_access holds mask).written

theorem store_source_corruption_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (16386 : ZMod mersenne31Modulus)) (bad : w 39 ≠ w 6) : False := by
  have address := (word_store_access holds mask).sourceAddress
  exact bad (by simpa using congrArg (fun q : Vector (ZMod mersenne31Modulus) 2 => q[0]) address)

theorem rom_misalignment_rejected {lo hi : ZMod mersenne31Modulus} :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[2,lo,hi,24] := by
  intro member
  have bad := (NativeFixed.word_rom_implementation member).2.1
  have literal : (2 : ZMod mersenne31Modulus).val = 2 := by decide
  rw [literal] at bad
  omega

theorem rom_oversized_key_rejected {lo hi : ZMod mersenne31Modulus} :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[4194304,lo,hi,24] := by
  intro member
  have bad := (NativeFixed.word_rom_implementation member).1
  have literal : (4194304 : ZMod mersenne31Modulus).val = 4194304 := by decide
  rw [literal] at bad
  omega

/-- Positive checks of the actual four-assertion addition slice only. They do
    not supply full 117-equation/22-lookup accepted memory instructions. -/
private def addressRow (store : Bool) (lo hi offLo offHi carry wrap outLo outHi : Nat)
    (i : Nat) : ZMod mersenne31Modulus :=
  if i = 35 then lo else if i = 36 then hi else if i = 9 then offLo else
  if i = 10 then offHi else if i = 27 then (if store then 0 else 1) else
  if i = 31 then (if store then 1 else 0) else if i = 95 then carry else
  if i = 63 then wrap else if i = 61 then outLo else if i = 62 then outHi else 0

private def addressSamples (store : Bool) : Vector (Nat → ZMod mersenne31Modulus) 4 :=
  #v[addressRow store 16 0 4 0 0 0 20 0,
    addressRow store 65532 0 4 0 1 0 0 1,
    addressRow store 0 0 65532 65535 0 0 65532 65535,
    addressRow store 65532 65535 8 0 1 1 4 0]

private def addressIndices : Vector (Fin 117) 4 :=
  #v[⟨20,by decide⟩,⟨23,by decide⟩,⟨74,by decide⟩,⟨75,by decide⟩]

private def addressAssertions (w : Nat → ZMod mersenne31Modulus) : Prop :=
  ∀ i : Fin 4, ((FlatOperation.constraints (importedConstraints NativeFixed.table)).get
    ⟨addressIndices[i].val,by change addressIndices[i].val < 117; exact addressIndices[i].isLt⟩).eval
      (environment w) = 0

theorem actual_address_edges (store : Bool) (sample : Fin 4) :
    addressAssertions (addressSamples store)[sample] := by
  intro i
  cases store <;> fin_cases sample <;> fin_cases i <;> decide +kernel

theorem independent_address_values (store : Bool) :
    (wordMemoryAddressWord (addressSamples store)[0]).toBitVec = 20 ∧
    (wordMemoryAddressWord (addressSamples store)[1]).toBitVec = 65536 ∧
    (wordMemoryAddressWord (addressSamples store)[2]).toBitVec = 0xfffffffc ∧
    (wordMemoryAddressWord (addressSamples store)[3]).toBitVec = 4 := by
  cases store <;> decide +kernel

end Tests.NativeReducedWordMemoryAccess
