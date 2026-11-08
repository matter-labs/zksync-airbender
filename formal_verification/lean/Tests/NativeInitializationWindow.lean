import Airbender.Review.Circuits.ReducedMachine.InitializationWindowTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.Tests.NativeInitializationWindow
open Airbender.NativeInitializationWindow Airbender.NativeInitializationWindowProofs
open Airbender.NativeInitializationBoundary Airbender.NativeInitializationOrdering Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private instance windowDecidable (previous current : PublicValues) : Decidable (WindowAccepted previous current) := by
  unfold WindowAccepted
  split <;> infer_instance

private def values (first last : Vector F 6) : PublicValues := ⟨first,last⟩
private def zero : Vector F 6 := #v[0,0,0,0,0,0]
private def zeroPublic : PublicValues := values zero zero

theorem parser_zero : parseAddress zero = some 0 := by decide +kernel

theorem parser_full_rv32 : parseAddress #v[65535,65535,0,0,0,0] = some (BitVec.ofNat 32 4294967295) := by decide +kernel

theorem parser_bad_low : parseAddress #v[65536,0,0,0,0,0] = none := by decide +kernel

theorem parser_bad_high : parseAddress #v[0,65536,0,0,0,0] = none := by decide +kernel

/-- Public WINDOW reference controls, not full source/global accepted witnesses. -/
theorem zero_fallback_retained : WindowAccepted zeroPublic zeroPublic := by decide +kernel

theorem strict_window_retains_raw_teardown : WindowAccepted
    (values zero #v[17,0,700000,4,700000,6]) (values #v[18,0,7,8,9,10] zero) := by decide +kernel

theorem all_four_fallback_fields_checked :
    ¬ WindowAccepted (values zero #v[0,0,1,0,0,0]) zeroPublic ∧
    ¬ WindowAccepted (values zero #v[0,0,0,1,0,0]) zeroPublic ∧
    ¬ WindowAccepted (values zero #v[0,0,0,0,1,0]) zeroPublic ∧
    ¬ WindowAccepted (values zero #v[0,0,0,0,0,1]) zeroPublic := by decide +kernel

theorem equal_nonzero_rejected : ¬ WindowAccepted
    (values zero #v[17,0,0,0,0,0]) (values #v[17,0,0,0,0,0] zero) := by decide +kernel

theorem descending_window_rejected : ¬ WindowAccepted
    (values zero #v[17,0,0,0,0,0]) (values #v[16,0,0,0,0,0] zero) := by decide +kernel

theorem failed_parser_window_rejected : ¬ WindowAccepted zeroPublic (values #v[65536,0,0,0,0,0] zero) := by decide +kernel

private def referenceValue (c i : Nat) : Nat := if c = 0 then 0 else 13 + 4 * c + 2 * i
private theorem referenceAdjacent : ∀ c, c + 1 < 4 → ∀ i < 2, ∀ j < 2,
    referenceValue c i ≤ referenceValue (c + 1) j ∧ (¬ c = 0 → referenceValue c i < referenceValue (c + 1) j) := by
  intro c bound i ib j jb
  have upper : c < 3 := by omega
  interval_cases c <;> interval_cases i <;> interval_cases j <;> decide +kernel

theorem pure_nonadjacent_growth : referenceValue 1 1 < referenceValue 3 0 :=
  (cross_sequence (padding := fun c _ => c = 0) (by decide) referenceAdjacent 1 3 (by decide) (by decide) 1 (by decide) 0 (by decide)).2 (by decide)

theorem pure_padding_chunk_retained : referenceValue 0 0 = referenceValue 0 1 ∧ referenceValue 0 1 ≤ referenceValue 3 0 :=
  ⟨by decide +kernel,(cross_sequence (padding := fun c _ => c = 0) (by decide) referenceAdjacent 0 3 (by decide) (by decide) 1 (by decide) 0 (by decide)).1⟩

theorem complete_body_with_public_window (active : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active))
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) ∧ WindowAccepted zeroPublic zeroPublic :=
  ⟨Airbender.ReducedMachine.NativeCSRPositiveWitness.body active,zero_fallback_retained⟩

theorem conditional_fallback_empty {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {previous current : Chunk R}
    (left : Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma previous.proof previous.values)
    (right : Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma current.proof current.values)
    (window : WindowAccepted previous.values current.values)
    (fallback : ¬ addressValue previous.values.oneBeforeLast < addressValue current.values.first) :
    ∀ i < scalar16Layout.traceLength-1, PaddingRecord (previous.proof.initialization.main.rows i) :=
  native_initialization_window_fallback embed memory pc gamma left right window fallback

theorem complete_conditional_order {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {count : Nat} {chunks : Nat → Chunk R}
    (accepted : Airbender.NativeInitializationWindow.Accepted embed memory pc gamma count chunks)
    (c d : Nat) (order : c < d) (bound : d < count) (i j : Nat)
    (ib : i < scalar16Layout.traceLength-1) (jb : j < scalar16Layout.traceLength-1)
    (nonpadding : ¬ PaddingRecord ((chunks c).proof.initialization.main.rows i)) :
    Airbender.NativeInitializationSorted.addressValue ((chunks c).proof.initialization.main.rows i) <
      Airbender.NativeInitializationSorted.addressValue ((chunks d).proof.initialization.main.rows j) :=
  (native_initialization_chunk_order embed memory pc gamma accepted c d order bound i ib j jb).2 nonpadding

theorem complete_conditional_unique {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {count : Nat} {chunks : Nat → Chunk R}
    (accepted : Airbender.NativeInitializationWindow.Accepted embed memory pc gamma count chunks)
    (c d i j : Nat) (cb : c < count) (db : d < count)
    (ib : i < scalar16Layout.traceLength-1) (jb : j < scalar16Layout.traceLength-1)
    (ip : ¬ PaddingRecord ((chunks c).proof.initialization.main.rows i))
    (jp : ¬ PaddingRecord ((chunks d).proof.initialization.main.rows j))
    (same : (Airbender.NativeMemoryTokens.encodeKey (initializationKey ((chunks c).proof.initialization.main.rows i) true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (initializationKey ((chunks d).proof.initialization.main.rows j) true)).address) : c = d ∧ i = j :=
  native_initialization_global_token_unique embed memory pc gamma accepted c d i j cb db ib jb ip jp same

end Airbender.Tests.NativeInitializationWindow
