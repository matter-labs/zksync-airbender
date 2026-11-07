import Airbender.Review.Circuits.ReducedMachine.DecoderTableTheorems

namespace Airbender.Tests.NativeDecoderTable
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeDecoderArguments Airbender.ReducedMachine.NativeDecoderTableArguments
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
abbrev F := ZMod mersenne31Modulus

/-- Observation DATA only; this record is not accepted main/worker proof data. -/
noncomputable def observed : Proof F :=
  ⟨⟨⟨fun _ i => (i : F),fun _ column => (column.start : F),1⟩,0,0,2⟩,
    (fun _ column => if column.index = 9 then 23 else 0),fun _ column => (column.index : F),0,0⟩

theorem separate_physical_multiplicity : observed.witness 0 decoderTableLayout.multiplicity = 23 ∧
    observed.main.memory.rows 0 9 = 9 := ⟨rfl,rfl⟩

theorem actual_setup_query : setupQuery observed 0 = #v[6,7,8,9,10,11,12,13,14,15] := by decide +kernel

theorem actual_quartic_difference : difference observed 0 = 16 := by decide +kernel

theorem all_setup_challenge_roles : queryArgument (RingHom.id F) ⟨Vector.replicate 9 1,3⟩ 2
    (setupQuery observed 0) = 213 := by decide +kernel

theorem all_ordinary_rows_retained : decoderTableLayout.traceLength-1 = 8388607 ∧
    decoderTableLayout.decoderCapacity < decoderTableLayout.traceLength-1 := by decide +kernel

theorem setup_bound (slot : Fin 10) : (setupColumn slot).index < decoderTableLayout.setupWidth :=
  NativeDecoderTableArgumentProofs.setup_column_bound slot

/-- PURE table-multiplicity equation slice: no Boolean/u16/count interpretation. -/
theorem wide_multiplicity_slice : accessTerm (1 : F) 1 700000 700000 = 0 := by decide +kernel

/-- A zero table multiplicity at a pole does not force auxiliary zero. PURE slice. -/
theorem table_pole_slice : accessTerm (1 : F) 0 0 7 = 0 := by decide +kernel

theorem difference_scaling : differenceTerm (2 : F) 11 4 = 14 := by decide +kernel

/-- Exact normalized polynomial boundary CONTROL, not a native body witness. -/
theorem nonzero_constant_rejected {R : Type} [Field R] (size : Nat) (omega : R) (values : Nat → R) :
    ¬ DifferencePolynomialAccepted size omega (Polynomial.C (1 : R)) values := by
  intro accepted
  have zero := (Airbender.Delegation.SumProofs.boundary_values
    (NativeDecoderTableArgumentProofs.as_sum accepted)).1
  exact one_ne_zero (by simpa only [Polynomial.eval_C] using zero)

/-- Pure normalized polynomial input; the primitive root is the explicit domain
    fidelity input. This is not complete table/main/worker acceptance. -/
theorem zero_difference_polynomial {R : Type} [Field R] (omega : R)
    (primitive : IsPrimitiveRoot omega decoderTableLayout.traceLength) :
    DifferencePolynomialAccepted decoderTableLayout.traceLength omega (0 : Polynomial R) (fun _ => 0) := by
  refine ⟨by decide,primitive,?_,?_,dvd_zero _⟩
  · simpa only [Polynomial.natDegree_zero] using (show 0 < decoderTableLayout.traceLength from by decide)
  · intro i _
    exact Polynomial.eval_zero

theorem complete_table_component {R : Type} [Field R] (embed : F →+* R) (ch : Challenges R)
    {proof : Proof R} (accepted : TableAccepted embed ch proof) :
    auxiliarySum proof true = auxiliarySum proof false := decoder_table_auxiliary_sum embed ch accepted

theorem last_observations {R : Type} [Field R] (embed : F →+* R) (ch : Challenges R)
    {proof : Proof R} (accepted : TableAccepted embed ch proof) :
    proof.main.memory.auxiliary (decoderTableLayout.traceLength-1) decoderTableLayout.tableMultiplicity =
      proof.main.memory.auxiliary (decoderTableLayout.traceLength-1) decoderTableLayout.access :=
  NativeDecoderTableArgumentProofs.last_auxiliaries embed ch accepted

end Airbender.Tests.NativeDecoderTable
