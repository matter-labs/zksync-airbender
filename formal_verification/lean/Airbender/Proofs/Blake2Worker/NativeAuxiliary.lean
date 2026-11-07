import Airbender.Review.Circuits.Blake2Worker.Auxiliary
import Mathlib.Tactic.Ring

namespace Airbender.Blake2Worker.AuxiliaryProofs
open Verification Native AuxiliaryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem same_source : auxiliaryLayoutSourceBytes = constraintsSourceBytes := by rfl

theorem geometry : auxiliaryLayout.extensionOffset = 44 ∧ auxiliaryLayout.width = 1244 ∧
    auxiliaryLayout.processing.start = 1064 ∧ auxiliaryLayout.memory.size = 43 ∧
    auxiliaryLayout.grandProduct.start = 1240 ∧ constraintsABI.traceLength-1 = 1048575 := by decide +kernel

theorem memory_columns (slot : Fin 43) : (memoryAuxiliaryColumn slot).start = 1068+4*slot.val ∧
    (memoryAuxiliaryColumn slot).start % 4 = 0 ∧
    (memoryAuxiliaryColumn slot).start+4 ≤ auxiliaryLayout.grandProduct.start := by
  fin_cases slot <;> decide +kernel

/-- Pure telescope with no division, cancellation or nonzero assumptions. -/
theorem chain_balance {R : Type} [CommRing R] (n : Nat) (a readFactor writeFactor : Nat → R)
    (steps : ∀ i < n, a (i+1)*readFactor i = a i*writeFactor i) :
    a n*(∏ i ∈ Finset.range n, readFactor i) = a 0*(∏ i ∈ Finset.range n, writeFactor i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := ih (fun i h => steps i (by omega))
    rw [Finset.prod_range_succ,Finset.prod_range_succ]
    calc
      a (n+1)*((∏ i ∈ Finset.range n, readFactor i)*readFactor n) =
          (a (n+1)*readFactor n)*(∏ i ∈ Finset.range n, readFactor i) := by ring
      _ = (a n*writeFactor n)*(∏ i ∈ Finset.range n, readFactor i) := by rw [steps n (by omega)]
      _ = (a n*(∏ i ∈ Finset.range n, readFactor i))*writeFactor n := by ring
      _ = (a 0*(∏ i ∈ Finset.range n, writeFactor i))*writeFactor n := by rw [prev]
      _ = a 0*((∏ i ∈ Finset.range n, writeFactor i)*writeFactor n) := by ring

theorem product_binding {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    (∏ i ∈ Finset.range 43, memoryFactor embed ch w write i) = memoryKeyProduct embed ch w write := by
  rw [Finset.prod_range]
  unfold memoryKeyProduct
  rw [← Fin.prod_univ_def]
  apply Finset.prod_congr rfl
  intro i _
  simp only [memoryFactor,Nat.mod_eq_of_lt i.isLt]

theorem row_balance {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R} {next : R}
    (accepted : AuxiliaryRowAccepted embed memory processor w aux next) :
    processorArgument embed processor w 1 * aux auxiliaryLayout.processing = embed (w constraintsABI.multiplicity) ∧
    memoryChainValue aux 43 * memoryKeyProduct embed memory w false = memoryKeyProduct embed memory w true ∧
    next * memoryKeyProduct embed memory w false = aux auxiliaryLayout.grandProduct * memoryKeyProduct embed memory w true := by
  have processing := accepted.processing
  simp only [processorAuxiliaryTerm,one_mul,sub_eq_zero] at processing
  have steps : ∀ i < 43, memoryChainValue aux (i+1)*memoryFactor embed memory w false i =
      memoryChainValue aux i*memoryFactor embed memory w true i := by
    intro i hi
    have step := accepted.memorySteps ⟨i,hi⟩
    simpa only [memoryAuxiliaryTerm,one_mul,sub_eq_zero,memoryChainValue,
      Nat.add_sub_cancel,Nat.add_one_ne_zero,if_false,memoryAuxiliaryColumn] using step
  have chain := chain_balance 43 (memoryChainValue aux)
    (memoryFactor embed memory w false) (memoryFactor embed memory w true) steps
  rw [product_binding,product_binding] at chain
  have initial : memoryChainValue aux 0 = 1 := rfl
  rw [initial,one_mul] at chain
  have grand := accepted.grandStep
  simp only [grandProductTerm,one_mul,sub_eq_zero] at grand
  refine ⟨processing,chain,?_⟩
  rw [grand]
  calc
    (aux auxiliaryLayout.grandProduct * memoryChainValue aux 43) * memoryKeyProduct embed memory w false =
      aux auxiliaryLayout.grandProduct * (memoryChainValue aux 43 * memoryKeyProduct embed memory w false) := by ring
    _ = _ := by rw [chain]

theorem trace_balance {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {w : Nat → Nat → ZMod mersenne31Modulus} {aux : Nat → QuarticColumn → R} {claimed : R}
    (accepted : AuxiliaryTraceAccepted embed memory processor w aux claimed) :
    claimed * (∏ i ∈ Finset.range (constraintsABI.traceLength-1), memoryKeyProduct embed memory (w i) false) =
      ∏ i ∈ Finset.range (constraintsABI.traceLength-1), memoryKeyProduct embed memory (w i) true := by
  have chain := chain_balance (constraintsABI.traceLength-1) (fun i => aux i auxiliaryLayout.grandProduct)
    (fun i => memoryKeyProduct embed memory (w i) false) (fun i => memoryKeyProduct embed memory (w i) true)
    (fun i hi => (row_balance embed memory processor (accepted.rows i hi)).2.2)
  have first := accepted.first
  have last := accepted.last
  simp only [grandBoundaryTerm,one_mul,sub_eq_zero] at first last
  simpa only [first,last,one_mul] using chain

end Airbender.Blake2Worker.AuxiliaryProofs
