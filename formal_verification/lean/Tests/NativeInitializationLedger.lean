import Airbender.Review.Circuits.ReducedMachine.InitializationLedgerTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.Tests.NativeInitializationLedger
open Airbender.NativeInitializationLedger Airbender.NativeInitializationLedgerProofs
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
open Airbender.NativeTokenLedger (Token)
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- PURE source-key/ledger slices only; no full source/global accepted witness. -/
private def row (low high valueLow valueHigh timeLow timeHigh execute : F) (column : Nat) : F :=
  if column = 126 then low else if column = 127 then high else
  if column = 128 then valueLow else if column = 129 then valueHigh else
  if column = 130 then timeLow else if column = 131 then timeHigh else if column = 4 then execute else 0

private def zero := row 0 0 0 0 0 0 0

theorem six_zero_fields_padding : paddingRow zero = true := by decide +kernel

theorem all_six_nonzero_fields_retained :
    paddingRow (row 1 0 0 0 0 0 0) = false ∧ paddingRow (row 0 1 0 0 0 0 0) = false ∧
    paddingRow (row 0 0 1 0 0 0 0) = false ∧ paddingRow (row 0 0 0 1 0 0 0) = false ∧
    paddingRow (row 0 0 0 0 1 0 0) = false ∧ paddingRow (row 0 0 0 0 0 1 0) = false := by decide +kernel

theorem padding_token_is_identical : initializationToken zero false = initializationToken zero true :=
  padding_token ((padding_test zero).mp six_zero_fields_padding)

theorem zero_address_nonpadding_kept :
    retainedRowTokens (row 0 0 1 0 0 0 0) false = [Token.memory (initializationToken (row 0 0 1 0 0 0 0) false)] := by
  decide +kernel

theorem inactive_nonpadding_kept : (retainedRowTokens (row 17 2 3 4 5 6 0) true).length = 1 := by decide +kernel

theorem active_padding_ports_kept : (retainedRowTokens (row 0 0 0 0 0 0 1) true).length = 4 := by decide +kernel

theorem padding_execute_independent : paddingRow (row 0 0 0 0 0 0 1) = paddingRow zero := by decide +kernel

theorem duplicate_padding_occurrences_kept : ([zero,zero,zero].flatMap paddingTokens).length = 3 := by decide +kernel

theorem duplicate_preserving_partition (write : Bool) :
    ([zero,zero,zero].flatMap fun w => Airbender.NativeTokenLedger.activeRowTokens w write).Perm
      (([zero,zero,zero].flatMap fun w => retainedRowTokens w write) ++ [zero,zero,zero].flatMap paddingTokens) :=
  split_rows _ _ _ _ (fun w _ => row_partition w write)

theorem seed_zero_fields_without_execute (w : Nat → F) :
    (initializationToken w true).value = 0 ∧ (initializationToken w true).time = (0,0) :=
  ⟨(seed_fields w).1,(seed_fields w).2.1⟩

theorem full_rv32_seed_word : addressValue (initializationToken (row 65535 65535 0 0 0 0 0) true) = 4294967295 := by
  rw [(row_domain (w := row 65535 65535 0 0 0 0 0) (by decide +kernel)).2.2.1]
  decide +kernel

theorem wide_low_not_ram32 : ¬ RAM32 (initializationToken (row 70000 0 0 0 0 0 0) true) := by
  simp [RAM32,initializationToken,initializationKey,Airbender.NativeMemoryTokens.encodeKey,
    Airbender.NativeMemoryTokens.encodeAddress,Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry.1,row]
  decide +kernel

theorem wide_high_not_ram32 : ¬ RAM32 (initializationToken (row 0 70000 0 0 0 0 0) true) := by
  simp [RAM32,initializationToken,initializationKey,Airbender.NativeMemoryTokens.encodeKey,
    Airbender.NativeMemoryTokens.encodeAddress,Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry.1,row]
  decide +kernel

/-- COMPLETE old CSR BODY plus local ledger observation, a WEAKER relation than
    complete new source/aux/global/worker/physical acceptance. -/
theorem complete_body_padding_ports (active : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active))
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) ∧
    paddingRow (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active) = true ∧
    (retainedRowTokens (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active) true).length = (if active then 4 else 0) := by
  refine ⟨Airbender.ReducedMachine.NativeCSRPositiveWitness.body active,?_⟩
  cases active <;> decide +kernel

theorem complete_matching_equivalence {Setup R : Type} [Field R] (mains : List (MainProof R))
    (workers : WorkerBatch Setup R) (inputs : PublicBoundary) :
    Airbender.NativeTokenLedger.LogicalMatching mains workers inputs ↔
      (retainedTokens mains workers inputs true).Perm (retainedTokens mains workers inputs false) :=
  native_initialization_padding_matching mains workers inputs

theorem explicit_seed_access_equivalence {Setup R : Type} [Field R] (mains : List (MainProof R))
    (workers : WorkerBatch Setup R) (inputs : PublicBoundary) :
    Airbender.NativeTokenLedger.LogicalMatching mains workers inputs ↔
      (initializationTokens mains true ++ accessTokens mains workers inputs true).Perm
        (initializationTokens mains false ++ accessTokens mains workers inputs false) :=
  native_seed_access_ledger mains workers inputs

theorem complete_conditional_domains {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    {proof : Airbender.NativeInitializationBatch.Proof R} (member : proof ∈ proofs)
    (i : Nat) (ordinary : i < scalar16Layout.traceLength-1) :
    ZeroSeed (initializationToken (proof.main.memory.rows i) true) ∧
      RAM32 (initializationToken (proof.main.memory.rows i) false) ∧
      addressValue (initializationToken (proof.main.memory.rows i) true) =
        Airbender.NativeInitializationSorted.addressValue (proof.main.memory.rows i) ∧
      addressValue (initializationToken (proof.main.memory.rows i) true) < 4294967296 :=
  native_initialization_seed_domain embed memory ch pc gamma config accepted member i ordinary

end Airbender.Tests.NativeInitializationLedger
