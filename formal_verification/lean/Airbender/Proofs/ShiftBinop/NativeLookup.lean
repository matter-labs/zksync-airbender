import Airbender.Review.Circuits.ShiftBinop.Tables.Native
import Airbender.Proofs.Mersenne31

namespace Airbender.ShiftBinop.NativeLookupProofs
open Verification
set_option warningAsError true
set_option Elab.async false

-- Structural inclusion of every actual stored row. Values remain literal data;
-- existing helper certificates supply their mathematical meanings separately.

theorem zero_region (i : Fin NativeBinary.dataZero.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeBinary.dataZero.row i) := by
  have hi : i.val < 1 := i.isLt
  refine ⟨⟨i.val + 0, by change i.val + 0 < 10817537; omega⟩, ?_⟩
  change (NativeBinary.dataZero.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 0, _⟩).map Nat.cast
  have selected : i.val + 0 < 1 := by omega
  rw [NativeShiftLookup.rowNat, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem xor_region (i : Fin NativeBinary.dataXor.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeBinary.dataXor.row i) := by
  have hi : i.val < 65536 := i.isLt
  refine ⟨⟨i.val + 1, by change i.val + 1 < 10817537; omega⟩, ?_⟩
  change (NativeBinary.dataXor.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 1, _⟩).map Nat.cast
  have h0 : ¬ i.val + 1 < 1 := by omega
  have selected : i.val + 1 < 65537 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem or_region (i : Fin NativeBinary.dataOr.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeBinary.dataOr.row i) := by
  have hi : i.val < 65536 := i.isLt
  refine ⟨⟨i.val + 65537, by change i.val + 65537 < 10817537; omega⟩, ?_⟩
  change (NativeBinary.dataOr.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 65537, _⟩).map Nat.cast
  have h0 : ¬ i.val + 65537 < 1 := by omega
  have h1 : ¬ i.val + 65537 < 65537 := by omega
  have selected : i.val + 65537 < 131073 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem and_region (i : Fin NativeBinary.dataAnd.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeBinary.dataAnd.row i) := by
  have hi : i.val < 65536 := i.isLt
  refine ⟨⟨i.val + 131073, by change i.val + 131073 < 10817537; omega⟩, ?_⟩
  change (NativeBinary.dataAnd.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 131073, _⟩).map Nat.cast
  have h0 : ¬ i.val + 131073 < 1 := by omega
  have h1 : ¬ i.val + 131073 < 65537 := by omega
  have h2 : ¬ i.val + 131073 < 131073 := by omega
  have selected : i.val + 131073 < 196609 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem csr_region (i : Fin NativeShiftCsr.data.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeShiftCsr.data.row i) := by
  have hi : i.val < 4096 := i.isLt
  refine ⟨⟨i.val + 196609, by change i.val + 196609 < 10817537; omega⟩, ?_⟩
  change (NativeShiftCsr.data.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 196609, _⟩).map Nat.cast
  have h0 : ¬ i.val + 196609 < 1 := by omega
  have h1 : ¬ i.val + 196609 < 65537 := by omega
  have h2 : ¬ i.val + 196609 < 131073 := by omega
  have h3 : ¬ i.val + 196609 < 196609 := by omega
  have selected : i.val + 196609 < 200705 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem truncate_region (i : Fin NativeShiftScalars.dataTruncate.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeShiftScalars.dataTruncate.row i) := by
  have hi : i.val < 65536 := i.isLt
  refine ⟨⟨i.val + 200705, by change i.val + 200705 < 10817537; omega⟩, ?_⟩
  change (NativeShiftScalars.dataTruncate.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 200705, _⟩).map Nat.cast
  have h0 : ¬ i.val + 200705 < 1 := by omega
  have h1 : ¬ i.val + 200705 < 65537 := by omega
  have h2 : ¬ i.val + 200705 < 131073 := by omega
  have h3 : ¬ i.val + 200705 < 196609 := by omega
  have h4 : ¬ i.val + 200705 < 200705 := by omega
  have selected : i.val + 200705 < 266241 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem sll_low_region (i : Fin NativeSllLow.data.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeSllLow.data.row i) := by
  have hi : i.val < 2097152 := i.isLt
  refine ⟨⟨i.val + 266241, by change i.val + 266241 < 10817537; omega⟩, ?_⟩
  change (NativeSllLow.data.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 266241, _⟩).map Nat.cast
  have h0 : ¬ i.val + 266241 < 1 := by omega
  have h1 : ¬ i.val + 266241 < 65537 := by omega
  have h2 : ¬ i.val + 266241 < 131073 := by omega
  have h3 : ¬ i.val + 266241 < 196609 := by omega
  have h4 : ¬ i.val + 266241 < 200705 := by omega
  have h5 : ¬ i.val + 266241 < 266241 := by omega
  have selected : i.val + 266241 < 2363393 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem sll_high_region (i : Fin NativeSllHigh.data.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeSllHigh.data.row i) := by
  have hi : i.val < 2097152 := i.isLt
  refine ⟨⟨i.val + 2363393, by change i.val + 2363393 < 10817537; omega⟩, ?_⟩
  change (NativeSllHigh.data.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 2363393, _⟩).map Nat.cast
  have h0 : ¬ i.val + 2363393 < 1 := by omega
  have h1 : ¬ i.val + 2363393 < 65537 := by omega
  have h2 : ¬ i.val + 2363393 < 131073 := by omega
  have h3 : ¬ i.val + 2363393 < 196609 := by omega
  have h4 : ¬ i.val + 2363393 < 200705 := by omega
  have h5 : ¬ i.val + 2363393 < 266241 := by omega
  have h6 : ¬ i.val + 2363393 < 2363393 := by omega
  have selected : i.val + 2363393 < 4460545 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem srl_low_region (i : Fin NativeSrlLow.data.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeSrlLow.data.row i) := by
  have hi : i.val < 2097152 := i.isLt
  refine ⟨⟨i.val + 4460545, by change i.val + 4460545 < 10817537; omega⟩, ?_⟩
  change (NativeSrlLow.data.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 4460545, _⟩).map Nat.cast
  have h0 : ¬ i.val + 4460545 < 1 := by omega
  have h1 : ¬ i.val + 4460545 < 65537 := by omega
  have h2 : ¬ i.val + 4460545 < 131073 := by omega
  have h3 : ¬ i.val + 4460545 < 196609 := by omega
  have h4 : ¬ i.val + 4460545 < 200705 := by omega
  have h5 : ¬ i.val + 4460545 < 266241 := by omega
  have h6 : ¬ i.val + 4460545 < 2363393 := by omega
  have h7 : ¬ i.val + 4460545 < 4460545 := by omega
  have selected : i.val + 4460545 < 6557697 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6, dif_neg h7, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem srl_high_region (i : Fin NativeSrlHigh.data.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeSrlHigh.data.row i) := by
  have hi : i.val < 2097152 := i.isLt
  refine ⟨⟨i.val + 6557697, by change i.val + 6557697 < 10817537; omega⟩, ?_⟩
  change (NativeSrlHigh.data.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 6557697, _⟩).map Nat.cast
  have h0 : ¬ i.val + 6557697 < 1 := by omega
  have h1 : ¬ i.val + 6557697 < 65537 := by omega
  have h2 : ¬ i.val + 6557697 < 131073 := by omega
  have h3 : ¬ i.val + 6557697 < 196609 := by omega
  have h4 : ¬ i.val + 6557697 < 200705 := by omega
  have h5 : ¬ i.val + 6557697 < 266241 := by omega
  have h6 : ¬ i.val + 6557697 < 2363393 := by omega
  have h7 : ¬ i.val + 6557697 < 4460545 := by omega
  have h8 : ¬ i.val + 6557697 < 6557697 := by omega
  have selected : i.val + 6557697 < 8654849 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6, dif_neg h7, dif_neg h8, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem sign_fill_region (i : Fin NativeShiftScalars.dataSignFill.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeShiftScalars.dataSignFill.row i) := by
  have hi : i.val < 2097152 := i.isLt
  refine ⟨⟨i.val + 8654849, by change i.val + 8654849 < 10817537; omega⟩, ?_⟩
  change (NativeShiftScalars.dataSignFill.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 8654849, _⟩).map Nat.cast
  have h0 : ¬ i.val + 8654849 < 1 := by omega
  have h1 : ¬ i.val + 8654849 < 65537 := by omega
  have h2 : ¬ i.val + 8654849 < 131073 := by omega
  have h3 : ¬ i.val + 8654849 < 196609 := by omega
  have h4 : ¬ i.val + 8654849 < 200705 := by omega
  have h5 : ¬ i.val + 8654849 < 266241 := by omega
  have h6 : ¬ i.val + 8654849 < 2363393 := by omega
  have h7 : ¬ i.val + 8654849 < 4460545 := by omega
  have h8 : ¬ i.val + 8654849 < 6557697 := by omega
  have h9 : ¬ i.val + 8654849 < 8654849 := by omega
  have selected : i.val + 8654849 < 10752001 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6, dif_neg h7, dif_neg h8, dif_neg h9, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]

theorem range_region (i : Fin NativeShiftScalars.dataRange.length) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (NativeShiftScalars.dataRange.row i) := by
  have hi : i.val < 65536 := i.isLt
  refine ⟨⟨i.val + 10752001, by change i.val + 10752001 < 10817537; omega⟩, ?_⟩
  change (NativeShiftScalars.dataRange.rowNat i).map Nat.cast =
    (NativeShiftLookup.rowNat ⟨i.val + 10752001, _⟩).map Nat.cast
  have h0 : ¬ i.val + 10752001 < 1 := by omega
  have h1 : ¬ i.val + 10752001 < 65537 := by omega
  have h2 : ¬ i.val + 10752001 < 131073 := by omega
  have h3 : ¬ i.val + 10752001 < 196609 := by omega
  have h4 : ¬ i.val + 10752001 < 200705 := by omega
  have h5 : ¬ i.val + 10752001 < 266241 := by omega
  have h6 : ¬ i.val + 10752001 < 2363393 := by omega
  have h7 : ¬ i.val + 10752001 < 4460545 := by omega
  have h8 : ¬ i.val + 10752001 < 6557697 := by omega
  have h9 : ¬ i.val + 10752001 < 8654849 := by omega
  have h10 : ¬ i.val + 10752001 < 10752001 := by omega
  rw [NativeShiftLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6, dif_neg h7, dif_neg h8, dif_neg h9, dif_neg h10]
  simp only [Nat.add_sub_cancel_right]

end Airbender.ShiftBinop.NativeLookupProofs
