import Airbender.Review.Circuits.Blake2Worker.DiagonalCB
import Airbender.Proofs.ReducedMachine.NativeWorkerDiagonalFirst

namespace Airbender.NativeWorkerDiagonalCBProofs
open Airbender.Verification Airbender.NativeWorkerDiagonalCB Airbender.Blake2Worker.Native
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
@[simp] private theorem coefficient : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient8 : (17179869176 : F) = 0 := by decide +kernel
@[simp] private theorem scale256 : (549755813888 : F) = 256 := by decide +kernel
@[simp] private theorem coefficient256 : (549755813632 : F) = 0 := by decide +kernel
@[simp] private theorem scale512 : (1099511627776 : F) = 512 := by decide +kernel
private def sourceExpressions : Vector (Vector (Expression F) 3) 24 := #v[
#v[(.var ⟨468⟩),(.var ⟨464⟩),(.var ⟨470⟩)],
#v[(.var ⟨469⟩),(.var ⟨465⟩),(.var ⟨471⟩)],
#v[(.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨357⟩))) (.mul (.mul (.const (1 : F)) (.const (268435456 : F))) (.var ⟨358⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨468⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨469⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨190⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨370⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨371⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨395⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨396⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨398⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨460⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨461⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨462⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨464⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨465⟩))),(.var ⟨472⟩)],
#v[(.var ⟨473⟩),(.var ⟨466⟩),(.var ⟨475⟩)],
#v[(.var ⟨474⟩),(.var ⟨467⟩),(.var ⟨476⟩)],
#v[(.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (268435456 : F))) (.var ⟨356⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨359⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨473⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨474⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨191⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨367⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨368⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨373⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨394⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨397⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨398⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨399⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨458⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨459⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨462⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨463⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨466⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨467⟩))),(.var ⟨477⟩)],
#v[(.var ⟨512⟩),(.var ⟨508⟩),(.var ⟨514⟩)],
#v[(.var ⟨513⟩),(.var ⟨509⟩),(.var ⟨515⟩)],
#v[(.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨403⟩))) (.mul (.mul (.const (1 : F)) (.const (268435456 : F))) (.var ⟨404⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨512⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨513⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨192⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨416⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨417⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨441⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨442⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨444⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨504⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨505⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨506⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨508⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨509⟩))),(.var ⟨516⟩)],
#v[(.var ⟨517⟩),(.var ⟨510⟩),(.var ⟨519⟩)],
#v[(.var ⟨518⟩),(.var ⟨511⟩),(.var ⟨520⟩)],
#v[(.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (268435456 : F))) (.var ⟨402⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨405⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨517⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨518⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨193⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨413⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨414⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨419⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨440⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨443⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨444⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨445⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨502⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨503⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨506⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨507⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨510⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨511⟩))),(.var ⟨521⟩)],
#v[(.var ⟨556⟩),(.var ⟨552⟩),(.var ⟨558⟩)],
#v[(.var ⟨557⟩),(.var ⟨553⟩),(.var ⟨559⟩)],
#v[(.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨449⟩))) (.mul (.mul (.const (1 : F)) (.const (268435456 : F))) (.var ⟨450⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨556⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨557⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨186⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨278⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨279⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨303⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨304⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨306⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨548⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨549⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨550⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨552⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨553⟩))),(.var ⟨560⟩)],
#v[(.var ⟨561⟩),(.var ⟨554⟩),(.var ⟨563⟩)],
#v[(.var ⟨562⟩),(.var ⟨555⟩),(.var ⟨564⟩)],
#v[(.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (268435456 : F))) (.var ⟨448⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨451⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨561⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨562⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨187⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨275⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨276⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨281⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨302⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨305⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨306⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨307⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨546⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨547⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨550⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨551⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨554⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨555⟩))),(.var ⟨565⟩)],
#v[(.var ⟨600⟩),(.var ⟨596⟩),(.var ⟨602⟩)],
#v[(.var ⟨601⟩),(.var ⟨597⟩),(.var ⟨603⟩)],
#v[(.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨311⟩))) (.mul (.mul (.const (1 : F)) (.const (268435456 : F))) (.var ⟨312⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨600⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨601⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨188⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨324⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨325⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨349⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨350⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨352⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨592⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨593⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨594⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨596⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨597⟩))),(.var ⟨604⟩)],
#v[(.var ⟨605⟩),(.var ⟨598⟩),(.var ⟨607⟩)],
#v[(.var ⟨606⟩),(.var ⟨599⟩),(.var ⟨608⟩)],
#v[(.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (268435456 : F))) (.var ⟨310⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨313⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨605⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨606⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨189⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨321⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨322⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨327⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨348⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨351⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨352⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨353⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨590⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨591⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨594⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨595⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨598⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨599⟩))),(.var ⟨609⟩)]]

/-- All actual three-field source bindings precede witness evaluation. -/
private theorem shape (diagonal : Fin 4) (piece : Fin 6) (entry : Fin 3) :
    (fixedExpressions ⟨76+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[(⟨entry.val,by have := entry.isLt; omega⟩ : Fin 4)] =
    sourceExpressions[(⟨6*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 24)][entry] := by
  fin_cases diagonal <;> fin_cases piece <;> fin_cases entry <;> rfl
private theorem value0 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 6) :
    (query w diagonal piece)[0] = Expression.eval (environment w)
      sourceExpressions[(⟨6*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 24)][0] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 0)
private theorem value1 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 6) :
    (query w diagonal piece)[1] = Expression.eval (environment w)
      sourceExpressions[(⟨6*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 24)][1] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 1)
private theorem value2 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 6) :
    (query w diagonal piece)[2] = Expression.eval (environment w)
      sourceExpressions[(⟨6*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 24)][2] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 2)
private theorem cLimb_reconstruction (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) :
    cLimb w diagonal limb = (query w diagonal ⟨3*limb.val,by have := limb.isLt; omega⟩)[1] +
      8*(query w diagonal ⟨3*limb.val+1,by have := limb.isLt; omega⟩)[1] +
      4096*(query w diagonal ⟨3*limb.val+2,by have := limb.isLt; omega⟩)[1] := by
  rw [value1 w diagonal _,value1 w diagonal _,value1 w diagonal _]
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [cLimb,cInput,dLimb,dByte,carry,
      Airbender.NativeWorkerDiagonalFirst.inputLimb,Airbender.NativeWorkerDiagonalFirst.columnLimb,Airbender.NativeWorkerDiagonalFirst.sourceColumn,
      Airbender.NativeWorkerSecondCB.cLimb,Airbender.NativeWorkerSecondCB.cInput,Airbender.NativeWorkerSecondCB.dLimb,Airbender.NativeWorkerSecondCB.dByte,Airbender.NativeWorkerSecondCB.carry,
      Airbender.NativeWorkerCB.cLimb,Airbender.NativeWorkerCB.cInput,Airbender.NativeWorkerCB.dLimb,Airbender.NativeWorkerCB.dByte,Airbender.NativeWorkerCB.carry,
      Airbender.NativeWorkerInitial.observed,Airbender.NativeWorkerInitial.initialColumns,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
private theorem bInput_reconstruction (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) :
    bInput w diagonal limb = (query w diagonal ⟨3*limb.val,by have := limb.isLt; omega⟩)[0] +
      8*(query w diagonal ⟨3*limb.val+1,by have := limb.isLt; omega⟩)[0] +
      4096*(query w diagonal ⟨3*limb.val+2,by have := limb.isLt; omega⟩)[0] := by
  rw [value0 w diagonal _,value0 w diagonal _,value0 w diagonal _]
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [bInput,Airbender.NativeWorkerDiagonalFirst.inputLimb,Airbender.NativeWorkerDiagonalFirst.columnLimb,
      Airbender.NativeWorkerDiagonalFirst.sourceColumn,Airbender.NativeWorkerDiagonalFirst.bLimb,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
private theorem block1 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock1 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock1 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup) := List.sublist_append_right _ _
  exact (((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private def booleanSyntax (column : Nat) : Expression F :=
  .add (.add (.const 0) (.add (.add (.const 0) (.const 0))
    (.mul (.mul (.const 1) (.const (-1))) (.var ⟨column⟩))))
    (.mul (.mul (.mul (.const 1) (.const 1)) (.var ⟨column⟩)) (.var ⟨column⟩))
private theorem bit_shape (setup : Table F (fields 4)) (diagonal : Fin 4) (limb : Fin 2) :
    (FlatOperation.constraints (constraintsBlock1 setup)).get
      ⟨1+12*diagonal.val+limb.val,by change 1+12*diagonal.val+limb.val < 64; have := diagonal.isLt; have := limb.isLt; omega⟩ =
      booleanSyntax (462+44*diagonal.val+limb.val) := by
  fin_cases diagonal <;> fin_cases limb <;> rfl

theorem carry_bits {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (diagonal : Fin 4) (limb : Fin 2) : (carry w diagonal limb).val ≤ 1 := by
  have bit := assertion_of_holds (block1 holds)
    ⟨1+12*diagonal.val+limb.val,by change 1+12*diagonal.val+limb.val < 64; have := diagonal.isLt; have := limb.isLt; omega⟩
  rw [bit_shape] at bit
  simp [booleanSyntax,Expression.eval,environment] at bit
  obtain ⟨n,bound,same⟩ := Airbender.Arithmetic.boolean_nat (by linear_combination bit)
  change (w (462+44*diagonal.val+limb.val)).val ≤ 1
  rw [same]
  simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

private def width (piece : Fin 3) : Nat := #v[3,9,4][piece]
private theorem query_effects {w : Nat → F} (effects : LookupEffects w)
    (diagonal : Fin 4) (limb : Fin 2) (piece : Fin 3) :
    (query w diagonal ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[0].val < 2^width piece ∧
    (query w diagonal ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[1].val < 2^width piece ∧
    (query w diagonal ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2].val < 2^width piece ∧
    (query w diagonal ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2].val =
      (query w diagonal ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[0].val ^^^
      (query w diagonal ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[1].val := by
  let slot : Fin 208 := ⟨76+18*diagonal.val+(3*limb.val+piece.val),by have := diagonal.isLt; have := limb.isLt; have := piece.isLt; omega⟩
  have bound : (fixedKind slot).bound = 2^width piece := by
    dsimp only [slot]
    fin_cases diagonal <;> fin_cases limb <;> fin_cases piece <;> norm_num [fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound,width]
  exact ⟨by simpa only [bound,query,slot] using effects.leftBounds slot,
    by simpa only [bound,query,slot] using effects.rightBounds slot,
    by simpa only [bound,query,slot] using effects.outputBounds slot,effects.results slot⟩

theorem limb_bounds {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (cLimb w diagonal limb).val < 65536 ∧ (bInput w diagonal limb).val < 65536 := by
  have lo := query_effects effects diagonal limb 0
  have mid := query_effects effects diagonal limb 1
  have hi := query_effects effects diagonal limb 2
  constructor
  · exact (Airbender.NativeWorkerCBProofs.triple_value _ _ _ _ lo.2.1 mid.2.1 hi.2.1 (cLimb_reconstruction w diagonal limb)).2
  · exact (Airbender.NativeWorkerCBProofs.triple_value _ _ _ _ lo.1 mid.1 hi.1 (bInput_reconstruction w diagonal limb)).2

private theorem output_value (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) (piece : Fin 3) :
    (query w diagonal ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2] = w (470+44*diagonal.val+5*limb.val+piece.val) := by
  rw [value2]
  fin_cases diagonal <;> fin_cases limb <;> fin_cases piece <;> simp [sourceExpressions,Expression.eval,environment]

private theorem xor3 (a c : BitVec 4) (b d : BitVec 12) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem xor12 (a c : BitVec 9) (b d : BitVec 3) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem xor32 (a b c d : BitVec 16) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem half_xor {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (BitVec.ofNat 16 (bInput w diagonal limb).val ^^^ BitVec.ofNat 16 (cLimb w diagonal limb).val) =
      BitVec.append (chunk4 w diagonal limb) (BitVec.append (chunk9 w diagonal limb) (chunk3 w diagonal limb)) := by
  have lo := query_effects effects diagonal limb 0
  have mid := query_effects effects diagonal limb 1
  have hi := query_effects effects diagonal limb 2
  have b := Airbender.NativeWorkerCBProofs.triple_pack _ _ _ _ lo.1 mid.1 hi.1 (bInput_reconstruction w diagonal limb)
  have c := Airbender.NativeWorkerCBProofs.triple_pack _ _ _ _ lo.2.1 mid.2.1 hi.2.1 (cLimb_reconstruction w diagonal limb)
  have x0 := Airbender.NativeWorkerCBProofs.piece_xor 3 _ _ _ lo.1 lo.2.1 lo.2.2.1 lo.2.2.2
  have x1 := Airbender.NativeWorkerCBProofs.piece_xor 9 _ _ _ mid.1 mid.2.1 mid.2.2.1 mid.2.2.2
  have x2 := Airbender.NativeWorkerCBProofs.piece_xor 4 _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  let q0 := query w diagonal (⟨3*limb.val,by have := limb.isLt; omega⟩ : Fin 6)
  let q1 := query w diagonal (⟨3*limb.val+1,by have := limb.isLt; omega⟩ : Fin 6)
  let q2 := query w diagonal (⟨3*limb.val+2,by have := limb.isLt; omega⟩ : Fin 6)
  change BitVec.ofNat 16 (bInput w diagonal limb).val = BitVec.append (BitVec.ofNat 4 q2[0].val)
    (BitVec.append (BitVec.ofNat 9 q1[0].val) (BitVec.ofNat 3 q0[0].val)) at b
  change BitVec.ofNat 16 (cLimb w diagonal limb).val = BitVec.append (BitVec.ofNat 4 q2[1].val)
    (BitVec.append (BitVec.ofNat 9 q1[1].val) (BitVec.ofNat 3 q0[1].val)) at c
  rw [output_value] at x0 x1 x2
  change BitVec.ofNat 3 (w (470+44*diagonal.val+5*limb.val)).val =
    (BitVec.ofNat 3 q0[0].val ^^^ BitVec.ofNat 3 q0[1].val) at x0
  change BitVec.ofNat 9 (w (470+44*diagonal.val+5*limb.val+1)).val =
    (BitVec.ofNat 9 q1[0].val ^^^ BitVec.ofNat 9 q1[1].val) at x1
  change BitVec.ofNat 4 (w (470+44*diagonal.val+5*limb.val+2)).val =
    (BitVec.ofNat 4 q2[0].val ^^^ BitVec.ofNat 4 q2[1].val) at x2
  rw [show 470+44*diagonal.val+5*limb.val+1 = 471+44*diagonal.val+5*limb.val by omega] at x1
  rw [show 470+44*diagonal.val+5*limb.val+2 = 472+44*diagonal.val+5*limb.val by omega] at x2
  rw [b,c,xor3,xor12,← x0,← x1,← x2]
  rfl

theorem rotated {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) :
    bAfter w diagonal = (Airbender.NativeWorkerFirstG.pack (bInput w diagonal 0) (bInput w diagonal 1) ^^^
      Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1)).rotateRight 12 := by
  unfold bAfter Airbender.NativeWorkerFirstG.pack
  rw [xor32,half_xor effects,half_xor effects,← Airbender.NativeWorkerCBProofs.rotate12]
/-- Exact original byte-query output syntax before its witness evaluation. -/
private theorem d_shape (diagonal : Fin 4) (piece : Fin 4) :
    (fixedExpressions ⟨72+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[2] =
      .var ⟨458+44*diagonal.val+piece.val⟩ := by
  fin_cases diagonal <;> fin_cases piece <;> rfl
private theorem d_byte_bounds {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (piece : Fin 4) :
    (dByte w diagonal piece).val < 256 := by
  let slot : Fin 208 := ⟨72+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩
  have kind : fixedKind slot = .byte := by
    dsimp only [slot]
    fin_cases diagonal <;> fin_cases piece <;> norm_num [fixedKind]
  have same : (fixedQuery w slot)[2] = dByte w diagonal piece := by
    simpa [fixedQuery,dByte,slot,Expression.eval,environment] using congrArg (Expression.eval (environment w)) (d_shape diagonal piece)
  have bound := effects.outputBounds slot
  rw [same] at bound
  simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound] using bound

theorem d_bounds {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (dLimb w diagonal limb).val < 65536 := by
  have b0 := d_byte_bounds effects diagonal 0
  have b1 := d_byte_bounds effects diagonal 1
  have b2 := d_byte_bounds effects diagonal 2
  have b3 := d_byte_bounds effects diagonal 3
  fin_cases limb
  · exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 256 (by omega)
  · exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 256 (by omega)

theorem d_pack {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (dLimb w diagonal 0) (dLimb w diagonal 1) =
      Airbender.NativeWorkerDiagonalFirst.dAfter w diagonal := by
  have low := Airbender.NativeWorkerFirstGProofs.pair_bytes
    (dByte w diagonal 2+256*dByte w diagonal 3) _ _ (d_byte_bounds effects diagonal 2) (d_byte_bounds effects diagonal 3) rfl
  have high := Airbender.NativeWorkerFirstGProofs.pair_bytes
    (dByte w diagonal 0+256*dByte w diagonal 1) _ _ (d_byte_bounds effects diagonal 0) (d_byte_bounds effects diagonal 1) rfl
  change BitVec.append (BitVec.ofNat 16 (dByte w diagonal 0+256*dByte w diagonal 1).val)
    (BitVec.ofNat 16 (dByte w diagonal 2+256*dByte w diagonal 3).val) = _
  rw [low,high]
  rfl

theorem mixing {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    LocalEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  exact ⟨carry_bits holds,limb_bounds effects,rotated effects⟩

theorem addition {w : Nat → F} (prior : Airbender.NativeWorkerDiagonalFirst.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (diagonal : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1) =
      Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 2 +
        Airbender.NativeWorkerDiagonalFirst.dAfter w diagonal := by
  have cb (limb : Fin 2) : (cInput w diagonal limb).val < 65536 := prior.inputs diagonal 2 limb
  have field (limb : Fin 2) : cInput w diagonal limb + dLimb w diagonal limb + (0 : F) +
      (if limb.val = 0 then 0 else carry w diagonal 0) = cLimb w diagonal limb+65536*carry w diagonal limb := by
    unfold cLimb
    ring
  have low := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ (0 : F) (0 : F) _ _
    (cb 0) (d_bounds effects diagonal 0) (by decide +kernel) (by decide +kernel)
    ((localEffects.carries diagonal 0).trans (by decide +kernel)) (localEffects.bounds diagonal 0).1 (by simpa using field 0)
  have high := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ (0 : F) _ _ _
    (cb 1) (d_bounds effects diagonal 1) (by decide +kernel)
    ((localEffects.carries diagonal 0).trans (by decide +kernel)) ((localEffects.carries diagonal 1).trans (by decide +kernel))
    (localEffects.bounds diagonal 1).1 (by simpa using field 1)
  simp only [ZMod.val_zero,Nat.add_zero] at low high
  rw [← d_pack effects diagonal]
  change Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1) =
    Airbender.NativeWorkerFirstG.pack (cInput w diagonal 0) (cInput w diagonal 1) +
      Airbender.NativeWorkerFirstG.pack (dLimb w diagonal 0) (dLimb w diagonal 1)
  rw [Airbender.NativeWorkerAdditionProofs.pack_value _ _ (localEffects.bounds diagonal 0).1 (localEffects.bounds diagonal 1).1,
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (cb 0) (cb 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (d_bounds effects diagonal 0) (d_bounds effects diagonal 1)]
  simpa using Airbender.NativeWorkerAdditionProofs.wide_add _ _ _ _ 0 0 _ _ _ _ low high

theorem half {w : Nat → F} (prior : Airbender.NativeWorkerDiagonalFirst.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (diagonal : Fin 4) :
    halfResult w diagonal = firstHalf
      (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 0)
      (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 1)
      (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 2)
      (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 3)
      (Airbender.NativeWorkerAddition.messageWord w ⟨8+2*diagonal.val,by have := diagonal.isLt; omega⟩) := by
  have a1 := prior.added diagonal
  have d1 := prior.mixing.rotated diagonal
  have c1 := addition prior effects localEffects diagonal
  have b1 := localEffects.rotated diagonal
  change bAfter w diagonal = (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 1 ^^^
    Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1)).rotateRight 12 at b1
  simp only [halfResult,firstHalf,b1,c1,d1,a1]

theorem row {w : Nat → F} (prior : Airbender.NativeWorkerDiagonalFirst.RowEffects w)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerDiagonalCB.RowEffects w := by
  have localEffects := mixing holds
  exact ⟨prior,localEffects,addition prior (Airbender.Blake2Worker.QueryProofs.lookup_effects holds) localEffects,
    half prior (Airbender.Blake2Worker.QueryProofs.lookup_effects holds) localEffects⟩
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary
theorem counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeMixedReplay.Effects batch workers inputs ∧
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerDiagonalCB.RowEffects w := by
  have prior := Airbender.NativeWorkerDiagonalFirstProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior.1,fun w member => row (prior.2 w member) (processing w member).body⟩
end Airbender.NativeWorkerDiagonalCBProofs
