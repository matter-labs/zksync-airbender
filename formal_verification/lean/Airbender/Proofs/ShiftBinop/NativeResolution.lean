import Airbender.Proofs.ShiftBinop.NativeRegions
import Mathlib.Tactic.IntervalCases
import Airbender.Review.Helpers.Tables.NativeBinaryRows
import Airbender.Review.Helpers.Tables.NativeShiftScalarRows
import Airbender.Review.Helpers.Tables.NativeSllLowRows
import Airbender.Review.Helpers.Tables.NativeSllHighRows
import Airbender.Review.Helpers.Tables.NativeSrlLowRows
import Airbender.Review.Helpers.Tables.NativeSrlHighRows

namespace Airbender.ShiftBinop.NativeLookupProofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Resolve the actual native tagged table to existing helper membership. -/
theorem binary_membership (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push kind.tag) ↔
      NativeBinary.Contains kind query := by
  cases kind with
  | xor => exact selected_membership .xor query
  | or => exact selected_membership .or query
  | and => exact selected_membership .and query

theorem scalar_membership (kind : ShiftScalarKind) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push kind.tag) ↔
      NativeShiftScalars.Contains kind query := by
  cases kind with
  | truncate => exact selected_membership .truncate query
  | signFill => exact selected_membership .signFill query
  | range => exact selected_membership .range query

theorem sll_low_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 48) ↔
      NativeSllLow.Contains query :=
  selected_membership .sllLow query

theorem sll_high_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 49) ↔
      NativeSllHigh.Contains query :=
  selected_membership .sllHigh query

theorem srl_low_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 50) ↔
      NativeSrlLow.Contains query :=
  selected_membership .srlLow query

theorem srl_high_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 51) ↔
      NativeSrlHigh.Contains query :=
  selected_membership .srlHigh query

/-- The native inactive row cannot hide arbitrary inputs or outputs. -/
theorem zero_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 0) ↔
      query = #v[0, 0, 0] := by
  have membership := selected_membership .zero query
  simp only [Region.tag, Nat.cast_zero] at membership
  rw [membership]
  constructor
  · rintro ⟨i, same⟩
    have hi : i = ⟨0, by decide⟩ := by
      apply Fin.ext
      change i.val = 0
      have bound : i.val < 1 := i.isLt
      omega
    subst i
    have actual : (Region.zero.data.row ⟨0, by decide⟩ : Vector (ZMod mersenne31Modulus) 4) =
        #v[0, 0, 0, 0] := by decide +kernel
    rw [actual] at same
    ext lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    interval_cases lane <;> simpa using selected
  · rintro rfl
    exact ⟨⟨0, by decide⟩, by decide +kernel⟩

/-- Compilation-profile CSR membership only; no runtime CSR binding or instruction claim. -/
theorem compilation_csr_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 25) ↔
      ∃ i : Fin NativeShiftCsr.data.length,
        query.push (25 : ZMod mersenne31Modulus) = NativeShiftCsr.data.row i :=
  selected_membership .csr query

end Airbender.ShiftBinop.NativeLookupProofs
