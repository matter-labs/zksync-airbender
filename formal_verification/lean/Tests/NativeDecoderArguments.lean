import Airbender.Review.Circuits.ReducedMachine.DecoderArgumentTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRBodyPadding

namespace Airbender.Tests.NativeDecoderArguments
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeDecoderArguments Airbender.Blake2Worker
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

abbrev F := ZMod mersenne31Modulus

def unitChallenges {R : Type} [Field R] : Challenges R := ⟨Vector.replicate 9 0,1⟩

theorem unit_argument {R : Type} [Field R] (embed : F →+* R) (w : Nat → F) :
    argument embed unitChallenges 1 w = embed (w 0)+1 := by
  simp [argument,unitChallenges,NativeDecoderArgumentProofs.query_fields]

theorem actual_geometry : decoderAuxiliaryLayout.access.start = 72 ∧
    decoderAuxiliaryLayout.traceLength-1 = 8388607 ∧
    importedConstraintsTraceColumns.execute = 4 := by decide +kernel

theorem actual_query : decoderQuery (fun i => (i : F)) = #v[0,1,5,6,7,8,9,10,11,12] := rfl

def fixtureAux (active : Bool) (column : QuarticColumn) : F :=
  if column = decoderAuxiliaryLayout.access then (if active then 1 else 0) else 0

/-- Complete original body plus this actual decoder auxiliary only. This is not
    table-multiplicity/global/native worker or physical proof acceptance. -/
theorem complete_local (active : Bool) :
    RowAccepted (RingHom.id F) unitChallenges (NativeCSRPositiveWitness.assignment active) (fixtureAux active) := by
  refine ⟨NativeCSRPositiveWitness.body active,?_⟩
  have pc : NativeCSRPositiveWitness.assignment active 0 = 0 := by cases active <;> decide +kernel
  have execute := (NativeCSRBodyPaddingProofs.observations active).1
  rw [accessTerm,unit_argument,pc,execute]
  cases active <;> simp [fixtureAux]

/-- Inactive full-body request1 admits decoder auxiliary0 for EVERY decoder
    challenge. It establishes a local interface limit, not global acceptance. -/
theorem inactive_all_challenges {R : Type} [Field R] (embed : F →+* R) (ch : Challenges R) :
    RowAccepted embed ch (NativeCSRPositiveWitness.assignment false) (fun _ => 0) :=
  NativeDecoderPaddingProofs.inactive_local embed ch

theorem inactive_request_retained {R : Type} [Field R] (embed : F →+* R) (ch : Challenges R) :
    RowAccepted embed ch (NativeCSRPositiveWitness.assignment false) (fun _ => 0) ∧
    NativeCSRPositiveWitness.assignment false importedConstraintsTraceColumns.execute = 0 ∧
    csrRequest (NativeCSRPositiveWitness.assignment false) = ⟨1,1991,some 0,3⟩ :=
  ⟨inactive_all_challenges embed ch,NativeCSRBodyPaddingProofs.observations false⟩

theorem active_denominator_nonzero : argument (RingHom.id F) unitChallenges 1
    (NativeCSRPositiveWitness.assignment true) ≠ 0 :=
  NativeDecoderArgumentProofs.active_denominator _ _ (complete_local true)
    (NativeCSRBodyPaddingProofs.observations true).1

theorem inactive_decoder_product {R : Type} [Field R] (embed : F →+* R) (ch : Challenges R) :
    argument embed ch 1 (NativeCSRPositiveWitness.assignment false) * 0 = 0 :=
  NativeDecoderArgumentProofs.inactive_product embed ch (inactive_all_challenges embed ch)
    (NativeCSRBodyPaddingProofs.observations false).1

/-- A pole may retain nonzero inactive decoder auxiliary. This PURE equation
    slice is not a complete body or global witness. -/
theorem inactive_pole : accessTerm (1 : F) 0 0 7 = 0 := by decide +kernel

theorem all_nine_roles : argument (RingHom.id F) ⟨Vector.replicate 9 1,3⟩ 2
    (fun i => (i : F)) = 141 := by decide +kernel

theorem pc_low_literal : argument (RingHom.id F) unitChallenges 2
    (fun i => if i = 0 then 5 else 0) = 11 := by decide +kernel

theorem nonunit_scaling : accessTerm (2 : F) 3 1 5 = 28 := by decide +kernel

theorem active_zero_auxiliary_rejected {R : Type} [Field R] (embed : F →+* R) (ch : Challenges R)
    (w : Nat → F) (active : w importedConstraintsTraceColumns.execute = 1) :
    ¬ RowAccepted embed ch w (fun _ => 0) := by
  intro accepted
  have equation := NativeDecoderArgumentProofs.row_equation embed ch accepted
  rw [active,map_one,mul_zero] at equation
  exact zero_ne_one equation

end Airbender.Tests.NativeDecoderArguments
