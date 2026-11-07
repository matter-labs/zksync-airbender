import Airbender.Review.Circuits.ReducedMachine.MainAuxiliary
import Airbender.Proofs.ReducedMachine.NativeMemoryBoundary
import Airbender.Proofs.Blake2Worker.NativeAuxiliary
import Airbender.Proofs.Constraints
import Mathlib.Tactic.LinearCombination

namespace Airbender.ReducedMachine.NativeMainAuxiliaryProofs
open Verification Native NativeMemoryBoundary NativeMainAuxiliary Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem port_geometry :
    mainPort 0 = ⟨⟨0,#v[132,133],134⟩,.register 5,.u16 #v[35,36],none⟩ ∧
    mainPort 1 = ⟨⟨1,#v[135,136],137⟩,.mixed 88 true #v[39,40],.u16 #v[37,38],none⟩ ∧
    mainPort 2 = ⟨⟨2,#v[138,139],140⟩,.mixed 89 true #v[45,46],.u16 #v[41,42],some (.u16 #v[43,44])⟩ := by decide +kernel

theorem initialization_geometry : importedConstraintsArgumentColumns.initialAddress = #v[126,127] ∧
    importedConstraintsArgumentColumns.terminalValue = #v[128,129] ∧
    importedConstraintsArgumentColumns.terminalTime = #v[130,131] ∧ initializationColumns = [126,127,128,129,130,131] := by decide +kernel

theorem chain_geometry : callerAuxiliaryLayout.memory = #[⟨96⟩,⟨100⟩,⟨104⟩] ∧
    callerAuxiliaryLayout.state.start = 108 ∧ callerAuxiliaryLayout.masking.start = 112 ∧
    callerAuxiliaryLayout.initialization.start = 116 ∧ callerAuxiliaryLayout.grandProduct.start = 120 ∧
    importedConstraintsTraceColumns.execute = 4 ∧ importedConstraintsTraceColumns.initialPC = #v[0,1] ∧
    importedConstraintsTraceColumns.initialTime = #v[2,3] ∧ importedConstraintsTraceColumns.finalPC = #v[13,14] ∧
    importedConstraintsTraceColumns.finalTime = #v[15,16] ∧ importedConstraintsArgumentColumns.addressBorrows = #v[124,125] := by decide +kernel

private theorem body_execute_boolean {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    w 4 = 0 ∨ w 4 = 1 := by
  have equation := Verification.assertion_of_holds holds ⟨31,by change 31 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,Verification.environment] at equation
  have bit : w 4*(w 4-1) = 0 := by linear_combination equation
  exact (mul_eq_zero.mp bit).imp id sub_eq_zero.mp

theorem execute_boolean {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) :
    w importedConstraintsTraceColumns.execute = 0 ∨ w importedConstraintsTraceColumns.execute = 1 :=
  body_execute_boolean (setup := NativeRuntimePool.table) accepted.body

theorem mask_choice {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) :
    maskedWrite embed memory pc w = if w importedConstraintsTraceColumns.execute = 1
      then mainWrite embed memory pc w else mainRead embed memory pc w := by
  rcases execute_boolean embed memory pc accepted with zero | one
  · simp [maskedWrite,zero]
  · simp [maskedWrite,one]

theorem initialization_padding {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) :
    w importedConstraintsArgumentColumns.addressBorrows[1] = 0 →
      ∀ column ∈ initializationColumns, w column = 0 := by
  intro zero column member
  have equation := accepted.padding column member
  rw [zero] at equation
  simpa [processingMaskTerm] using equation

private def factor {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) (i : Nat) : R :=
  memoryKeyArgument embed memory (mainMemoryKey w ⟨i%3,Nat.mod_lt _ (by decide)⟩ write)

theorem product_binding {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    (∏ i ∈ Finset.range 3, factor embed memory w write i) = mainMemoryProduct embed memory w write := by
  rw [Finset.prod_range]
  unfold mainMemoryProduct
  rw [← Fin.prod_univ_def]
  apply Finset.prod_congr rfl
  intro i _
  simp only [factor,Nat.mod_eq_of_lt i.isLt]

/-- Source memory/state chain preserves all read/write factors before masking. -/
theorem state_balance {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) :
    aux callerAuxiliaryLayout.state * mainRead embed memory pc w = mainWrite embed memory pc w := by
  have steps : ∀ i < 3, mainChainValue aux (i+1)*factor embed memory w false i =
      mainChainValue aux i*factor embed memory w true i := by
    intro i hi
    have step := accepted.memorySteps ⟨i,hi⟩
    simpa only [memoryAuxiliaryTerm,one_mul,sub_eq_zero,mainChainValue,
      Nat.add_sub_cancel,Nat.add_one_ne_zero,if_false,factor,Nat.mod_eq_of_lt hi] using step
  have chain := AuxiliaryProofs.chain_balance 3 (mainChainValue aux)
    (factor embed memory w false) (factor embed memory w true) steps
  rw [product_binding,product_binding] at chain
  have initial : mainChainValue aux 0 = 1 := rfl
  rw [initial,one_mul] at chain
  have state := accepted.state
  simp only [memoryAuxiliaryTerm,one_mul,sub_eq_zero] at state
  unfold mainRead mainWrite
  calc
    _ = (aux callerAuxiliaryLayout.state * pcArgument embed pc (mainPCKey w false)) *
        mainMemoryProduct embed memory w false := by ring
    _ = (mainChainValue aux 3 * pcArgument embed pc (mainPCKey w true)) * mainMemoryProduct embed memory w false := by rw [state]
    _ = (mainChainValue aux 3 * mainMemoryProduct embed memory w false) * pcArgument embed pc (mainPCKey w true) := by ring
    _ = _ := by rw [chain]

/-- Arbitrary field execute is retained. Boolean/activity extraction is not a
    premise or silently substituted for the actual source masking equation. -/
theorem masked_balance {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) :
    aux callerAuxiliaryLayout.masking * mainRead embed memory pc w = maskedWrite embed memory pc w := by
  have mask := accepted.masking
  simp only [permutationMaskTerm,one_mul] at mask
  have equation : aux callerAuxiliaryLayout.masking =
      embed (w importedConstraintsTraceColumns.execute)*aux callerAuxiliaryLayout.state +
      1-embed (w importedConstraintsTraceColumns.execute) := by
    apply sub_eq_zero.mp
    calc
      _ = aux callerAuxiliaryLayout.masking -
          embed (w importedConstraintsTraceColumns.execute)*aux callerAuxiliaryLayout.state +
          embed (w importedConstraintsTraceColumns.execute)-1 := by ring
      _ = 0 := mask
  have state := state_balance embed memory pc accepted
  rw [equation]
  unfold maskedWrite
  calc
    _ = embed (w importedConstraintsTraceColumns.execute) *
        (aux callerAuxiliaryLayout.state * mainRead embed memory pc w) +
        (1-embed (w importedConstraintsTraceColumns.execute))*mainRead embed memory pc w := by ring
    _ = _ := by rw [state]

theorem row_balance {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) :
    next*rowFactor embed memory pc w false = aux callerAuxiliaryLayout.grandProduct*rowFactor embed memory pc w true := by
  have init := accepted.initialization
  have grand := accepted.grand
  simp only [memoryAuxiliaryTerm,one_mul,sub_eq_zero] at init
  simp only [grandProductTerm,one_mul,sub_eq_zero] at grand
  have masked := masked_balance embed memory pc accepted
  simp only [rowFactor,Bool.false_eq_true,↓reduceIte]
  calc
    _ = aux callerAuxiliaryLayout.grandProduct *
        ((aux callerAuxiliaryLayout.initialization*memoryKeyArgument embed memory (initializationKey w false)) *
        mainRead embed memory pc w) := by rw [grand]; ring
    _ = aux callerAuxiliaryLayout.grandProduct *
        (memoryKeyArgument embed memory (initializationKey w true) *
        (aux callerAuxiliaryLayout.masking*mainRead embed memory pc w)) := by rw [init]; ring
    _ = _ := by rw [masked]

theorem trace_balance {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) {proof : MainProof R}
    (accepted : Accepted embed memory pc proof) :
    proof.grandClaim * mainRowsProduct embed memory pc proof false = mainRowsProduct embed memory pc proof true := by
  have chain := AuxiliaryProofs.chain_balance (callerAuxiliaryLayout.traceLength-1)
    (fun i => proof.auxiliary i callerAuxiliaryLayout.grandProduct)
    (fun i => rowFactor embed memory pc (proof.rows i) false)
    (fun i => rowFactor embed memory pc (proof.rows i) true)
    (fun i hi => row_balance embed memory pc (accepted.rows i hi))
  have first := accepted.first
  have last := accepted.last
  simp only [grandBoundaryTerm,one_mul,sub_eq_zero] at first last
  simpa only [first,last,one_mul,mainRowsProduct] using chain

theorem main_batch_balance {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (mains : List (MainProof R))
    (accepted : ∀ proof ∈ mains, Accepted embed memory pc proof) :
    (mains.map MainProof.grandClaim).prod * mainBatchProduct embed memory pc mains false =
      mainBatchProduct embed memory pc mains true := by
  apply NativeMemoryBoundaryProofs.list_product_balance
  intro proof member
  exact trace_balance embed memory pc (accepted proof member)

theorem main_worker_balance {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (pc : PCChallenges R) (config : WorkerConfiguration Setup)
    {mains : List (MainProof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : MainWorkerAccepted embed memory processor pc config mains batch inputs inverse) :
    registerProduct embed memory registerInitialKey * pcArgument embed pc initialPCKey *
      mainBatchProduct embed memory pc mains true * workerBatchProduct embed memory batch true =
      registerProduct embed memory (registerFinalKey inputs) * pcArgument embed pc (finalPCKey inputs) *
      mainBatchProduct embed memory pc mains false * workerBatchProduct embed memory batch false := by
  have global := NativeMemoryBoundaryProofs.complete_worker_balance embed memory processor pc config accepted.global
  have main := main_batch_balance embed memory pc mains accepted.mainProofs
  calc
    _ = ((mains.map MainProof.grandClaim).prod * registerProduct embed memory registerInitialKey *
        pcArgument embed pc initialPCKey * workerBatchProduct embed memory batch true) *
        mainBatchProduct embed memory pc mains false := by rw [← main]; ring
    _ = (registerProduct embed memory (registerFinalKey inputs) * pcArgument embed pc (finalPCKey inputs) *
        workerBatchProduct embed memory batch false) * mainBatchProduct embed memory pc mains false := by rw [global]
    _ = _ := by ring

end Airbender.ReducedMachine.NativeMainAuxiliaryProofs
