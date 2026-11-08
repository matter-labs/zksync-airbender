import Airbender.Review.Circuits.ReducedMachine.InitializationSorted
import Airbender.Proofs.ReducedMachine.NativeScalar16Lookups
import Airbender.Proofs.ReducedMachine.NativeInitializationOrdering
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.NativeInitializationSortedProofs
open Airbender.NativeInitializationSorted Airbender.NativeInitializationOrdering
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Reuse the unchanged generic two-limb subtraction/comparison theorem. All
    field-to-Nat lifting stays below M31; the 32-bit radix word is NOT cast to F. -/
theorem comparison {w next : Nat → F}
    (current : (address w)[0].val < 65536 ∧ (address w)[1].val < 65536)
    (following : (address next)[0].val < 65536 ∧ (address next)[1].val < 65536)
    (ranges : (remainder w)[0].val < 65536 ∧ (remainder w)[1].val < 65536)
    (bits : ((borrows w)[0] = 0 ∨ (borrows w)[0] = 1) ∧
      ((borrows w)[1] = 0 ∨ (borrows w)[1] = 1))
    (adjacent : AdjacentAccepted w next) :
    (borrows w)[1] = 1 ↔ addressValue w < addressValue next := by
  have bitBound {bit : F} (h : bit = 0 ∨ bit = 1) : bit.val ≤ 1 := by
    rcases h with rfl | rfl <;> decide +kernel
  have low := adjacent.low
  have high := adjacent.high
  simp only [lowTerm,highTerm,one_mul] at low high
  have result := Arithmetic.Word.borrow_iff (p := mersenne31Modulus) (by decide)
    (left := ⟨(address w)[0].val,(address w)[1].val⟩)
    (right := ⟨(address next)[0].val,(address next)[1].val⟩)
    (remainder := ⟨(remainder w)[0].val,(remainder w)[1].val⟩)
    (carry := (borrows w)[0].val) (borrow := (borrows w)[1].val)
    current following ranges (bitBound bits.1) (bitBound bits.2)
    (by simpa only [ZMod.natCast_zmod_val,Nat.cast_ofNat] using (show
      (remainder w)[0]+(address next)[0] = (address w)[0]+65536*(borrows w)[0] by linear_combination -low))
    (by simpa only [ZMod.natCast_zmod_val,Nat.cast_ofNat] using (show
      (borrows w)[0]+(remainder w)[1]+(address next)[1] = (address w)[1]+65536*(borrows w)[1] by linear_combination -high))
  have bitOne : (borrows w)[1] = 1 ↔ (borrows w)[1].val = 1 := by
    constructor
    · intro h; rw [h]; decide +kernel
    · intro h; apply ZMod.val_injective _; rw [h]; decide +kernel
  exact bitOne.trans result

theorem padding_address {w : Nat → F} (padding : PaddingRecord w) : addressValue w = 0 := by
  have columns := Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry.2.2.2
  have low := padding 126 (by rw [columns]; simp)
  have high := padding 127 (by rw [columns]; simp)
  simp [addressValue,address,NativeInitializationOrderingProofs.geometry.1,low,high]

/-- Entire local calculation over an ABSTRACT body table before native pool
    instantiation. The zero-borrow padding rule comes from the six native polys. -/
theorem local_order {setup : Table F (fields 4)} {w next : Nat → F}
    (body : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (current : (address w)[0].val < 65536 ∧ (address w)[1].val < 65536)
    (following : (address next)[0].val < 65536 ∧ (address next)[1].val < 65536)
    (padding : (borrows w)[1] = 0 → PaddingRecord w)
    (adjacent : AdjacentAccepted w next) :
    addressValue w ≤ addressValue next ∧ (¬ PaddingRecord w → addressValue w < addressValue next) := by
  obtain ⟨lo,hi,bitLo,bitHi⟩ := NativeInitializationOrderingProofs.body_controls body
  have compare := comparison current following ⟨lo,hi⟩ ⟨bitLo,bitHi⟩ adjacent
  rcases bitHi with zero | one
  · have padded := padding zero
    have value := padding_address padded
    exact ⟨by omega,fun nonpadding => False.elim (nonpadding padded)⟩
  · have strict := compare.mp one
    exact ⟨Nat.le_of_lt strict,fun _ => strict⟩

/-- Abstract finite sequence argument. The only links used are actual adjacent
    weak growth and strict growth at nonpadding records, derived above. -/
theorem sequence_order {n : Nat} {values : Nat → Nat} {padding : Nat → Prop}
    (adjacent : ∀ i, i + 1 < n → values i ≤ values (i + 1) ∧ (¬ padding i → values i < values (i + 1))) :
    (∀ i j, i ≤ j → j < n → values i ≤ values j) ∧
    (∀ i j, i < j → j < n → ¬ padding i → values i < values j) := by
  have weak : ∀ i j, i ≤ j → j < n → values i ≤ values j := by
    intro i j order bound
    induction j with
    | zero => have same : i = 0 := by omega
              subst i; exact Nat.le_refl _
    | succ j ih =>
      by_cases same : i = j + 1
      · subst i; exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega) (by omega)) (adjacent j bound).1
  refine ⟨weak,?_⟩
  intro i j order bound nonpadding
  exact Nat.lt_of_lt_of_le ((adjacent i (by omega)).2 nonpadding) (weak (i + 1) j (by omega) bound)

theorem adjacent_order {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R}
    (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof) :
    ∀ i < scalar16Layout.traceLength-2,
      addressValue (proof.initialization.main.rows i) ≤ addressValue (proof.initialization.main.rows (i + 1)) ∧
      (¬ PaddingRecord (proof.initialization.main.rows i) →
        addressValue (proof.initialization.main.rows i) < addressValue (proof.initialization.main.rows (i + 1))) := by
  have ordering : NativeInitializationOrdering.Accepted embed memory pc proof.initialization.main :=
    accepted.arguments.initialization.ordering
  intro i bound
  have domain : scalar16Layout.traceLength = callerAuxiliaryLayout.traceLength := by decide +kernel
  rw [domain] at bound
  have row := ordering.main.rows i (by omega)
  have current := NativeScalar16LookupProofs.initialization_bounds accepted.lookups i (by omega)
  have following := NativeScalar16LookupProofs.initialization_bounds accepted.lookups (i + 1) (by omega)
  exact local_order row.body current following (fun zero =>
    Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_padding embed memory pc row
      (by simpa [borrows] using zero)) (ordering.adjacent i bound)

theorem full_order {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R}
    (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof) :
    (∀ i j, i ≤ j → j < scalar16Layout.traceLength-1 →
      addressValue (proof.initialization.main.rows i) ≤ addressValue (proof.initialization.main.rows j)) ∧
    (∀ i j, i < j → j < scalar16Layout.traceLength-1 → ¬ PaddingRecord (proof.initialization.main.rows i) →
      addressValue (proof.initialization.main.rows i) < addressValue (proof.initialization.main.rows j)) := by
  exact sequence_order (fun i bound => adjacent_order embed memory pc gamma accepted i (by omega))

theorem nonpadding_unique {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R}
    (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof)
    (i j : Nat) (ib : i < scalar16Layout.traceLength-1) (jb : j < scalar16Layout.traceLength-1)
    (ip : ¬ PaddingRecord (proof.initialization.main.rows i)) (jp : ¬ PaddingRecord (proof.initialization.main.rows j))
    (same : addressValue (proof.initialization.main.rows i) = addressValue (proof.initialization.main.rows j)) : i = j := by
  have order := (full_order embed memory pc gamma accepted).2
  rcases lt_trichotomy i j with less | equal | greater
  · have strict := order i j less jb ip; omega
  · exact equal
  · have strict := order j i greater ib jp; omega

theorem token_unique {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R}
    (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof)
    (i j : Nat) (ib : i < scalar16Layout.traceLength-1) (jb : j < scalar16Layout.traceLength-1)
    (ip : ¬ PaddingRecord (proof.initialization.main.rows i)) (jp : ¬ PaddingRecord (proof.initialization.main.rows j))
    (same : (Airbender.NativeMemoryTokens.encodeKey (initializationKey (proof.initialization.main.rows i) true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (initializationKey (proof.initialization.main.rows j) true)).address) : i = j := by
  exact nonpadding_unique embed memory pc gamma accepted i j ib jb ip jp
    (congrArg (fun a : Vector F 2 => a[0].val+65536*a[1].val)
      (NativeInitializationOrderingProofs.token_address_binding same))

end Airbender.NativeInitializationSortedProofs
