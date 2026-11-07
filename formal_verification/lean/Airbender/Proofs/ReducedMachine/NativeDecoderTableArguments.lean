import Airbender.Review.Circuits.ReducedMachine.DecoderTableArguments
import Airbender.Proofs.ReducedMachine.NativeDecoderArguments
import Airbender.Proofs.Memory.DelegationSum

namespace Airbender.ReducedMachine.NativeDecoderTableArgumentProofs
open Native NativeDecoderArguments NativeDecoderTableArguments NativeMemoryBoundary Airbender.Blake2Worker
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem same_source : decoderTableLayoutSourceBytes = importedConstraintsSourceBytes ∧
    decoderTableLayoutSourceBytes = decoderAuxiliaryLayoutSourceBytes := ⟨rfl,rfl⟩

theorem geometry : decoderTableLayout.traceLength = 8388608 ∧ decoderTableLayout.witnessWidth = 107 ∧
    decoderTableLayout.setupWidth = 16 ∧ decoderTableLayout.decoderCapacity = 1048576 ∧
    decoderTableLayout.extensionOffset = 12 ∧ decoderTableLayout.width = 124 ∧
    decoderTableLayout.multiplicity.index = 9 ∧ decoderTableLayout.setupStart = 6 ∧
    decoderTableLayout.access = decoderAuxiliaryLayout.access ∧
    decoderTableLayout.tableMultiplicity.start = 88 ∧
    decoderTableLayout.traceLength = decoderAuxiliaryLayout.traceLength ∧
    decoderTableLayout.setupStart = importedConstraintsSetupColumns.decoderStart := by decide +kernel

theorem setup_column_bound (slot : Fin 10) : (setupColumn slot).index < decoderTableLayout.setupWidth := by
  change 6+slot.val < 16
  omega

theorem access_argument {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) (tau : R) (w : Nat → ZMod mersenne31Modulus) :
    argument embed ch tau w = queryArgument embed ch tau (decoderQuery w) := rfl

theorem as_sum {R : Type} [Field R] {size : Nat} {omega : R} {p : Polynomial R} {values : Nat → R}
    (accepted : DifferencePolynomialAccepted size omega p values) :
    Airbender.Delegation.SumPolynomialAccepted size omega p values 0 := by
  refine ⟨accepted.positive,accepted.primitive,accepted.degree,accepted.samples,?_⟩
  simpa only [zero_mul,Polynomial.C_0,zero_mul,add_zero] using accepted.boundary

theorem table_row {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) {proof : Proof R} (accepted : TableAccepted embed ch proof)
    (i : Nat) (ordinary : i < decoderTableLayout.traceLength-1) :
    queryArgument embed ch 1 (setupQuery proof i) * proof.main.memory.auxiliary i decoderTableLayout.tableMultiplicity =
      embed (proof.witness i decoderTableLayout.multiplicity) := by
  simpa only [accessTerm,one_mul,sub_eq_zero] using accepted.multiplicity i ordinary

theorem multiplicity_nonpole {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) {proof : Proof R} (accepted : TableAccepted embed ch proof)
    (i : Nat) (ordinary : i < decoderTableLayout.traceLength-1)
    (nonzero : proof.witness i decoderTableLayout.multiplicity ≠ 0) :
    queryArgument embed ch 1 (setupQuery proof i) ≠ 0 := by
  intro pole
  have equation := table_row embed ch accepted i ordinary
  rw [pole,zero_mul] at equation
  exact nonzero (embed.injective (by simpa only [map_zero] using equation.symm))

theorem auxiliary_sum {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) {proof : Proof R} (accepted : TableAccepted embed ch proof) :
    auxiliarySum proof true = auxiliarySum proof false := by
  have sum := Airbender.Delegation.SumProofs.ordinary_sum (as_sum accepted.polynomial)
  simp only [difference,Finset.sum_sub_distrib] at sum
  exact sub_eq_zero.mp sum

theorem polynomial_zero {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) {proof : Proof R} (accepted : TableAccepted embed ch proof) : proof.polynomial.eval 0 = 0 :=
  (Airbender.Delegation.SumProofs.boundary_values (as_sum accepted.polynomial)).1

theorem last_auxiliaries {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) {proof : Proof R} (accepted : TableAccepted embed ch proof) :
    proof.main.memory.auxiliary (decoderTableLayout.traceLength-1) decoderTableLayout.tableMultiplicity =
      proof.main.memory.auxiliary (decoderTableLayout.traceLength-1) decoderTableLayout.access := by
  have endpoint := (Airbender.Delegation.SumProofs.boundary_values (as_sum accepted.polynomial)).2
  rw [accepted.polynomial.samples _ (Nat.sub_lt accepted.polynomial.positive (by decide))] at endpoint
  exact sub_eq_zero.mp (by simpa only [difference,neg_zero] using endpoint)

theorem joint_effects {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (decoder : Challenges R)
    (config : Native.WorkerConfiguration Setup) {proofs : List (Proof R)}
    {batch : Native.WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : NativeDecoderTableArguments.Accepted embed memory ch pc decoder config proofs batch inputs inverse) :
    NativeMainArguments.Effects embed memory pc (proofs.map Proof.main) batch inputs ∧
      ∀ proof ∈ proofs, auxiliarySum proof true = auxiliarySum proof false := by
  refine ⟨(NativeDecoderArgumentProofs.joint_effects embed memory ch pc decoder config accepted.arguments).1,?_⟩
  intro proof member
  exact auxiliary_sum embed decoder (accepted.tables proof member)
end Airbender.ReducedMachine.NativeDecoderTableArgumentProofs
