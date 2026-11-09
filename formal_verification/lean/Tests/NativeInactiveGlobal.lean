import Airbender.Review.Trace.Families.ReducedMachine.InactiveGlobalTheorems

namespace Airbender.Tests.NativeInactiveGlobal
open Airbender.NativeInactiveGlobal Airbender.NativeInactiveGlobalProofs
open Airbender.NativeDelegationSupport Airbender.ReducedMachine.Native
abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem characteristic_capacity : mersenne31Modulus = 256*8388607+255 := by decide +kernel

theorem original_body : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false))
    (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) :=
  Airbender.ReducedMachine.NativeCSRPositiveWitness.body false

theorem inactive_request_kept :
    Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false importedConstraintsTraceColumns.execute = 0 ∧
    csrRequest (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) = ⟨1,1991,some 0,3⟩ := by
  decide +kernel

theorem exact_four_field_key : callerKey (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) = ⟨1991,0,7,0⟩ :=
  original_fields.2.2

theorem duplicate_positions_count : weightAt [7,7] (fun n : Nat => n) (fun _ => (1 : F)) 7 = 2 := by
  simpa using constant_weight [7,7] (fun n : Nat => n) (fun _ => (1 : F)) 7 (by simp) rfl

theorem empty_domain : weightAt ([] : List Nat) id (fun _ => (1 : F)) 7 = 0 := rfl

theorem zero_count_has_zero_weight : (((0*8388607 : Nat) : F)) = 0 := by decide +kernel

theorem one_copy_not_boolean : (((1*8388607 : Nat) : F)) ≠ 0 ∧ (((1*8388607 : Nat) : F)) ≠ 1 :=
  ⟨residue_not_bit (by decide) (by decide) (by decide : 0 ≤ 1),residue_not_bit (by decide) (by decide) (by decide : 1 ≤ 1)⟩

theorem count256_not_boolean : (((256*8388607 : Nat) : F)) ≠ 0 ∧ (((256*8388607 : Nat) : F)) ≠ 1 :=
  ⟨residue_not_bit (by decide) (by decide) (by decide : 0 ≤ 1),residue_not_bit (by decide) (by decide) (by decide : 1 ≤ 1)⟩

theorem count257_not_boolean : (((257*8388607 : Nat) : F)) ≠ 0 ∧ (((257*8388607 : Nat) : F)) ≠ 1 :=
  ⟨residue_not_bit (by decide) (by decide) (by decide : 0 ≤ 1),residue_not_bit (by decide) (by decide) (by decide : 1 ≤ 1)⟩

theorem maximum_count_not_boolean : (((8192*8388607 : Nat) : F)) ≠ 0 ∧ (((8192*8388607 : Nat) : F)) ≠ 1 :=
  ⟨residue_not_bit (by decide) (by decide) (by decide : 0 ≤ 1),residue_not_bit (by decide) (by decide) (by decide : 1 ≤ 1)⟩

theorem before_wrap : (((256*8388607 : Nat) : F)).val = 2147483392 := by decide +kernel

theorem after_wrap : (((257*8388607 : Nat) : F)).val = 8388352 := by decide +kernel






theorem original_components_remain :
    NativeInitializationComponent.Fixture (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) :=
  NativeInitializationComponentProofs.original_fixture

theorem zero_counter_rejected {R : Type} [Field R] (proof : NativeMainDecoder.Proof R) :
    ¬ NativeMainBatch.CounterAccepted (copies proof 0).main := by
  intro accepted
  have limits := (NativeMainBatchProofs.counter_iff _).mp accepted
  change 0 < 0 ∧ 0 ≤ 8192 at limits
  omega

theorem over_capacity_rejected {R : Type} [Field R] (proof : NativeMainDecoder.Proof R) :
    ¬ NativeMainBatch.CounterAccepted (copies proof 8193).main := by
  intro accepted
  have limits := (NativeMainBatchProofs.counter_iff _).mp accepted
  change 0 < 8193 ∧ 8193 ≤ 8192 at limits
  omega

end Airbender.Tests.NativeInactiveGlobal
