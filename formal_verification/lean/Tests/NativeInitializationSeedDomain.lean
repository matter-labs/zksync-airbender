import Airbender.Review.Circuits.ReducedMachine.InitializationSeedDomainTheorems
import Tests.NativeInitializationBatch

namespace Airbender.Tests.NativeInitializationSeedDomain
open Airbender.NativeInitializationSeedDomain Airbender.NativeInitializationSeedDomainProofs
open Airbender.NativeInitializationLedger (F ZeroSeed RAM32)
open Airbender.NativeInitializationBatch (Proof mainProofs)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private instance ramDecidable (token : Trace.MemoryToken mersenne31Modulus) : Decidable (RAM32 token) := by
  unfold RAM32
  infer_instance
private instance seedDecidable (token : Trace.MemoryToken mersenne31Modulus) : Decidable (ZeroSeed token) := by
  unfold ZeroSeed
  infer_instance
private instance alignedDecidable (c : Trace.Cell) : Decidable c.Aligned := by
  cases c <;> unfold Trace.Cell.Aligned <;> infer_instance

private def zeroRAM : Trace.MemoryToken mersenne31Modulus := ⟨Nat.pair 1 (Nat.pair 0 0),(0,0),0⟩
private def unalignedRAM : Trace.MemoryToken mersenne31Modulus := ⟨Nat.pair 1 (Nat.pair 3 0),(0,0),0⟩

theorem zero_ram_encodes_cell : zeroRAM = (cell zeroRAM).initialToken 0 := token_cell (by decide +kernel)

theorem zero_address_is_ram : cell zeroRAM = Trace.Cell.ram 0 := by decide +kernel

/-- Canonical cell encoding does NOT impose address alignment. PURE token only. -/
theorem unaligned_cell_retained : unalignedRAM = (cell unalignedRAM).initialToken 0 ∧
    ¬ (cell unalignedRAM).Aligned := ⟨token_cell (by decide +kernel),by decide +kernel⟩

private theorem ram_cell (low high : Nat) :
    cell (⟨Nat.pair 1 (Nat.pair low high),(0,0),0⟩ : Trace.MemoryToken mersenne31Modulus) =
      Trace.Cell.ram (BitVec.ofNat 32 (low + 65536 * high)) := by
  simp [cell,Airbender.NativeInitializationLedger.addressValue,Nat.unpair_pair]

theorem full_rv32_cell :
    cell (⟨Nat.pair 1 (Nat.pair 65535 65535),(0,0),0⟩ : Trace.MemoryToken mersenne31Modulus) =
      Trace.Cell.ram (BitVec.ofNat 32 4294967295) := ram_cell 65535 65535

theorem register_not_ram32 : ¬ RAM32 ((Trace.Cell.register 0).initialToken (p := mersenne31Modulus) 0) := by decide +kernel

theorem nonzero_value_not_zero_seed : ¬ ZeroSeed {zeroRAM with value := 1} := by decide +kernel

theorem nonzero_time_not_zero_seed : ¬ ZeroSeed {zeroRAM with time := (1,0)} := by decide +kernel

private def pureSources : List Nat := [9,9]

theorem indexed_positions_preserve_duplicates :
    (((List.finRange pureSources.length).product (List.finRange 1)).map
      fun index => pureSources[index.1.val]).length = 2 := by decide +kernel

theorem duplicate_key_list_rejected : ¬ (pureSources.map id).Nodup := by decide +kernel

theorem generic_unique_sampling :
    ((([3,7].flatMap fun item : Nat => (List.range 2).map fun i => 4 * item + i).filter fun _ => true).map id).Nodup := by
  apply sampled_unique [3,7] 2 (fun item i => 4 * item + i) (fun _ => true) id
  intro c d i j _ _ same
  fin_cases c <;> fin_cases d <;> fin_cases i <;> fin_cases j <;> simp_all

theorem empty_observed_domain : sources ([] : List (Proof F)) = [] ∧ tokens ([] : List (Proof F)) true = [] ∧
    cells ([] : List (Proof F)) = [] := ⟨rfl,rfl,rfl⟩

theorem complete_empty_domain : Effects ([] : List (Proof F)) :=
  native_observed_seed_domain _ _ _ _ _ _ Airbender.Tests.NativeInitializationBatch.empty_combined_component

theorem same_actual_ledger {R : Type} [Field R] (proofs : List (Proof R)) (write : Bool) :
    Airbender.NativeInitializationLedger.initializationTokens (mainProofs proofs) write =
      (tokens proofs write).map Airbender.NativeTokenLedger.Token.memory := same_ledger proofs write

theorem complete_matching_equivalence {Setup R : Type} [Field R] (proofs : List (Proof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    Airbender.NativeTokenLedger.LogicalMatching (mainProofs proofs) batch inputs ↔
      ((tokens proofs true).map Airbender.NativeTokenLedger.Token.memory ++
        Airbender.NativeInitializationLedger.accessTokens (mainProofs proofs) batch inputs true).Perm
      ((tokens proofs false).map Airbender.NativeTokenLedger.Token.memory ++
        Airbender.NativeInitializationLedger.accessTokens (mainProofs proofs) batch inputs false) :=
  native_observed_seed_ledger proofs batch inputs

theorem complete_conditional_domain {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Effects proofs := native_observed_seed_domain embed memory ch pc gamma config accepted

end Airbender.Tests.NativeInitializationSeedDomain
