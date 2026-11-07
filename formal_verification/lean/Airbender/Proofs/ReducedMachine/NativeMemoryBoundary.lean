import Airbender.Review.Circuits.ReducedMachine.MemoryBoundary
import Airbender.Proofs.Blake2Worker.NativeCapacity
import Airbender.Proofs.Blake2Worker.NativeAuxiliary
import Mathlib.Tactic.Ring

namespace Airbender.ReducedMachine.NativeMemoryBoundaryProofs
open NativeMemoryBoundary Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem word_bounds (word : BitVec 32) :
    (publicWord word)[0].val < 65536 ∧ (publicWord word)[1].val < 65536 := by
  have low := Nat.mod_lt word.toNat (by decide : 0 < 65536)
  have high : word.toNat / 65536 < 65536 := by
    have bound := word.isLt
    change word.toNat < 4294967296 at bound
    omega
  change ((word.toNat % 65536 : Nat) : ZMod mersenne31Modulus).val < 65536 ∧
    ((word.toNat / 65536 : Nat) : ZMod mersenne31Modulus).val < 65536
  rw [ZMod.val_natCast_of_lt (lt_trans low (by decide : 65536 < mersenne31Modulus)),
    ZMod.val_natCast_of_lt (lt_trans high (by decide : 65536 < mersenne31Modulus))]
  exact ⟨low,high⟩

theorem initial_pc : initialPCKey.pc = #v[0,0] ∧ initialPCKey.time = #v[4,0] := by decide +kernel

/-- Same affine factor as the actual native register helper. The address-high
    challenge is present in the shared key but contributes zero here. -/
theorem initial_register_factor {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (index : Fin 32) :
    memoryKeyArgument embed memory (registerInitialKey index) =
      1 + memory.addressLow*embed (index.val : ZMod mersenne31Modulus) + memory.gamma := by
  simp [memoryKeyArgument,registerInitialKey]
  ring

theorem final_register_factor {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (inputs : PublicBoundary) (index : Fin 32) :
    memoryKeyArgument embed memory (registerFinalKey inputs index) =
      1 + memory.addressLow*embed (index.val : ZMod mersenne31Modulus) +
      memory.timeLow*embed (inputs.registers index).time[0] + memory.timeHigh*embed (inputs.registers index).time[1] +
      memory.valueLow*embed (publicWord (inputs.registers index).value)[0] +
      memory.valueHigh*embed (publicWord (inputs.registers index).value)[1] + memory.gamma := by
  simp only [memoryKeyArgument,registerFinalKey,map_zero,map_one,mul_zero,add_zero]
  ring

theorem multiply_fold {R : Type} [CommRing R] (values : List R) (initial : R) :
    values.foldl (·*·) initial = initial*values.prod := by
  induction values generalizing initial with
  | nil => simp
  | cons value values ih => simp only [List.foldl_cons,List.prod_cons,ih,mul_assoc]

theorem worker_fold {Setup R : Type} [Field R] (outputs : List (WorkerProofOutput Setup R)) (initial : R) :
    outputs.foldl (fun accumulator output => accumulator*output.proof.memoryClaim) initial =
      initial*(outputs.map fun output => output.proof.memoryClaim).prod := by
  induction outputs generalizing initial with
  | nil => simp
  | cons output outputs ih => simp only [List.foldl_cons,List.map_cons,List.prod_cons,ih,mul_assoc]

/-- Pure successful-inverse algebra; no cancellation of worker factors. -/
theorem clear_boundary_inverses {R : Type} [CommRing R]
    (claims initialRegisters finalRegisters initialPC finalPC inverseRegisters inversePC : R)
    (registers : finalRegisters*inverseRegisters = 1) (pc : finalPC*inversePC = 1)
    (check : claims*(initialRegisters*inverseRegisters)*(initialPC*inversePC) = 1) :
    claims*initialRegisters*initialPC = finalRegisters*finalPC := by
  calc
    claims*initialRegisters*initialPC =
        (claims*(initialRegisters*inverseRegisters)*(initialPC*inversePC))*(finalRegisters*finalPC) := by
      calc
        _ = (claims*initialRegisters*initialPC)*(finalRegisters*inverseRegisters)*(finalPC*inversePC) := by rw [registers,pc,mul_one,mul_one]
        _ = _ := by ring
    _ = _ := by rw [check,one_mul]

theorem boundary_nonzero {R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : BoundaryAccepted embed memory pc inputs inverse) :
    registerProduct embed memory (registerFinalKey inputs) ≠ 0 ∧
    pcArgument embed pc (finalPCKey inputs) ≠ 0 := by
  constructor
  · intro zero
    have equation := accepted.registers
    rw [zero,zero_mul] at equation
    exact zero_ne_one equation
  · intro zero
    have equation := accepted.pc
    rw [zero,zero_mul] at equation
    exact zero_ne_one equation

theorem public_claim_balance {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (pc : PCChallenges R) (config : WorkerConfiguration Setup)
    {mains : List R} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : UnifiedMemoryAccepted embed memory processor pc config mains batch inputs inverse) :
    mains.prod*(batch.outputs.map fun output => output.proof.memoryClaim).prod *
      registerProduct embed memory registerInitialKey * pcArgument embed pc initialPCKey =
      registerProduct embed memory (registerFinalKey inputs) * pcArgument embed pc (finalPCKey inputs) := by
  have check := accepted.accumulator
  simp only [unifiedMemoryAccumulator,multiply_fold,one_mul,worker_fold,registerContribution,pcContribution] at check
  exact clear_boundary_inverses _ _ _ _ _ _ _ accepted.boundary.registers accepted.boundary.pc check

theorem list_product_balance {α R : Type} [CommRing R] (outputs : List α) (claim read write : α → R)
    (each : ∀ output ∈ outputs, claim output*read output = write output) :
    (outputs.map claim).prod*(outputs.map read).prod = (outputs.map write).prod := by
  induction outputs with
  | nil => simp
  | cons output outputs ih =>
    have first := each output (by simp)
    have rest := ih (fun value member => each value (List.mem_cons_of_mem output member))
    simp only [List.map_cons,List.prod_cons]
    calc
      _ = (claim output*read output)*((outputs.map claim).prod*(outputs.map read).prod) := by ring
      _ = _ := by rw [first,rest]

theorem worker_products {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (config : WorkerConfiguration Setup)
    {batch : WorkerBatch Setup R} (accepted : ConfiguredWorkersAccepted embed memory processor config batch) :
    (batch.outputs.map fun output => output.proof.memoryClaim).prod * workerBatchProduct embed memory batch false =
      workerBatchProduct embed memory batch true := by
  apply list_product_balance
  intro output member
  exact AuxiliaryProofs.trace_balance embed memory processor
    (CapacityProofs.shared_acceptance embed memory processor config accepted output member).trace

theorem complete_worker_balance {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (pc : PCChallenges R) (config : WorkerConfiguration Setup)
    {mains : List R} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : UnifiedMemoryAccepted embed memory processor pc config mains batch inputs inverse) :
    mains.prod * registerProduct embed memory registerInitialKey * pcArgument embed pc initialPCKey *
      workerBatchProduct embed memory batch true =
      registerProduct embed memory (registerFinalKey inputs) * pcArgument embed pc (finalPCKey inputs) *
      workerBatchProduct embed memory batch false := by
  have claims := public_claim_balance embed memory processor pc config accepted
  have workers := worker_products embed memory processor config accepted.workers
  calc
    _ = (mains.prod * (batch.outputs.map fun output => output.proof.memoryClaim).prod *
        registerProduct embed memory registerInitialKey * pcArgument embed pc initialPCKey) *
        workerBatchProduct embed memory batch false := by rw [← workers]; ring
    _ = _ := by rw [claims]

end Airbender.ReducedMachine.NativeMemoryBoundaryProofs
