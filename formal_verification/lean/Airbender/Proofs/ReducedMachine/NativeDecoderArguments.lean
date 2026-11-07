import Airbender.Review.Circuits.ReducedMachine.DecoderArguments
import Airbender.Proofs.ReducedMachine.NativeMainArguments

namespace Airbender.ReducedMachine.NativeDecoderArgumentProofs
open Native NativeDecoderArguments NativeMemoryBoundary Airbender.Blake2Worker
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem same_source : decoderAuxiliaryLayoutSourceBytes = importedConstraintsSourceBytes ∧
    decoderAuxiliaryLayoutSourceBytes = callerAuxiliaryLayoutSourceBytes := ⟨rfl,rfl⟩

theorem geometry : decoderAuxiliaryLayout.traceLength = 8388608 ∧
    decoderAuxiliaryLayout.traceLength = callerAuxiliaryLayout.traceLength ∧
    decoderAuxiliaryLayout.extensionOffset = 12 ∧ decoderAuxiliaryLayout.width = 124 ∧
    decoderAuxiliaryLayout.access.start = 72 ∧ importedConstraintsTraceColumns.execute = 4 ∧
    importedConstraintsTraceColumns.initialPC = #v[0,1] ∧
    importedConstraintsDecoderColumns = ⟨5,6,7,8,#v[9,10],11,12⟩ := by decide +kernel

theorem query_fields (w : Nat → ZMod mersenne31Modulus) :
    decoderQuery w = #v[w 0,w 1,w 5,w 6,w 7,w 8,w 9,w 10,w 11,w 12] := rfl

theorem row_equation {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R}
    (accepted : RowAccepted embed ch w aux) :
    argument embed ch 1 w * aux decoderAuxiliaryLayout.access = embed (w importedConstraintsTraceColumns.execute) := by
  simpa only [accessTerm,one_mul,sub_eq_zero] using accepted.access

theorem active_denominator {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R}
    (accepted : RowAccepted embed ch w aux) (active : w importedConstraintsTraceColumns.execute = 1) :
    argument embed ch 1 w ≠ 0 := by
  intro zero
  have equation := row_equation embed ch accepted
  rw [active,map_one,zero,zero_mul] at equation
  exact zero_ne_one equation

theorem inactive_product {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R}
    (accepted : RowAccepted embed ch w aux) (inactive : w importedConstraintsTraceColumns.execute = 0) :
    argument embed ch 1 w * aux decoderAuxiliaryLayout.access = 0 := by
  simpa only [inactive,map_zero] using row_equation embed ch accepted

theorem joint_effects {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (decoder : Challenges R)
    (config : Native.WorkerConfiguration Setup) {mains : List (NativeMainArguments.Proof R)}
    {batch : Native.WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Accepted embed memory ch pc decoder config mains batch inputs inverse) :
    NativeMainArguments.Effects embed memory pc mains batch inputs ∧
    ∀ proof ∈ mains, ∀ i < decoderAuxiliaryLayout.traceLength-1,
      argument embed decoder 1 (proof.memory.rows i) * proof.memory.auxiliary i decoderAuxiliaryLayout.access =
        embed (proof.memory.rows i importedConstraintsTraceColumns.execute) := by
  refine ⟨NativeMainArgumentProofs.joint_effects embed memory ch pc config accepted.arguments,?_⟩
  intro proof member i ordinary
  exact row_equation embed decoder (accepted.decoderAccess proof member i ordinary)
end Airbender.ReducedMachine.NativeDecoderArgumentProofs
