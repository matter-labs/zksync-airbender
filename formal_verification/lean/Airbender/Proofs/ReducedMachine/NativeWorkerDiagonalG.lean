import Airbender.Review.Circuits.Blake2Worker.DiagonalG
import Airbender.Proofs.ReducedMachine.NativeWorkerDiagonalAD

namespace Airbender.NativeWorkerDiagonalGProofs
open Airbender.Verification Airbender.NativeWorkerDiagonalG Airbender.NativeWorkerInitial Airbender.Blake2Worker.Native
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
@[simp] private theorem coefficient : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient_one : (2147483648 : F) = 1 := by decide +kernel
private def sourceExpressions : Vector (Vector (Expression F) 3) 16 := #v[
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨472⟩))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨475⟩))),(.var ⟨490⟩),(.var ⟨492⟩)],
#v[(.var ⟨476⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨190⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨370⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨371⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨395⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨396⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨398⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨460⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨461⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨462⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨485⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨486⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨488⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨490⟩))),(.var ⟨493⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨470⟩))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨477⟩))),(.var ⟨491⟩),(.var ⟨494⟩)],
#v[(.var ⟨471⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨191⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨367⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨368⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨373⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨394⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨397⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨398⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨399⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨458⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨459⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨462⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨463⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨484⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨487⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨488⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨489⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨491⟩))),(.var ⟨495⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨516⟩))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨519⟩))),(.var ⟨534⟩),(.var ⟨536⟩)],
#v[(.var ⟨520⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨192⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨416⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨417⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨441⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨442⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨444⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨504⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨505⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨506⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨529⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨530⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨532⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨534⟩))),(.var ⟨537⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨514⟩))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨521⟩))),(.var ⟨535⟩),(.var ⟨538⟩)],
#v[(.var ⟨515⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨193⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨413⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨414⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨419⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨440⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨443⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨444⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨445⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨502⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨503⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨506⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨507⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨528⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨531⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨532⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨533⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨535⟩))),(.var ⟨539⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨560⟩))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨563⟩))),(.var ⟨578⟩),(.var ⟨580⟩)],
#v[(.var ⟨564⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨186⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨278⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨279⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨303⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨304⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨306⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨548⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨549⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨550⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨573⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨574⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨576⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨578⟩))),(.var ⟨581⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨558⟩))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨565⟩))),(.var ⟨579⟩),(.var ⟨582⟩)],
#v[(.var ⟨559⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨187⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨275⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨276⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨281⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨302⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨305⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨306⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨307⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨546⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨547⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨550⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨551⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨572⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨575⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨576⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨577⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨579⟩))),(.var ⟨583⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨604⟩))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨607⟩))),(.var ⟨622⟩),(.var ⟨624⟩)],
#v[(.var ⟨608⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨188⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨324⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨325⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨349⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨350⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨352⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨592⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨593⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨594⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨617⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨618⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨620⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨622⟩))),(.var ⟨625⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨602⟩))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨609⟩))),(.var ⟨623⟩),(.var ⟨626⟩)],
#v[(.var ⟨603⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨189⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨321⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨322⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨327⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨348⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨351⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨352⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨353⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨590⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨591⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨594⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨595⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨616⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨619⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨620⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨621⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨623⟩))),(.var ⟨627⟩)]]

/-- Exact actual query syntax is bound BEFORE witness evaluation. -/
private theorem shape (diagonal : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (fixedExpressions ⟨86+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[(⟨entry.val,by have := entry.isLt; omega⟩ : Fin 4)] =
    sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][entry] := by
  fin_cases diagonal <;> fin_cases piece <;> fin_cases entry <;> rfl
private theorem value (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (query w diagonal piece)[entry.val]'(by have := entry.isLt; omega) =
    Expression.eval (environment w) sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][entry] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece entry)

private theorem value0 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[0] = Expression.eval (environment w)
      sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][0] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 0)

private theorem value1 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[1] = Expression.eval (environment w)
      sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][1] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 1)

private theorem value2 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[2] = Expression.eval (environment w)
      sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][2] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 2)


private theorem c_reconstruction (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) :
    cLimb w diagonal limb = (query w diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩)[1] +
      128*(query w diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[1] := by
  rw [value1 w diagonal _,value1 w diagonal _]
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [cLimb,cInput,dLimb,dByte,carry,Airbender.NativeWorkerDiagonalCB.cLimb,
      Airbender.NativeWorkerDiagonalCB.cInput,Airbender.NativeWorkerDiagonalCB.dLimb,
      Airbender.NativeWorkerDiagonalCB.dByte,Airbender.NativeWorkerDiagonalCB.carry,
      Airbender.NativeWorkerDiagonalFirst.inputLimb,Airbender.NativeWorkerDiagonalFirst.columnLimb,Airbender.NativeWorkerDiagonalFirst.sourceColumn,
      Airbender.NativeWorkerSecondCB.cLimb,Airbender.NativeWorkerSecondCB.cInput,Airbender.NativeWorkerSecondCB.dLimb,Airbender.NativeWorkerSecondCB.dByte,Airbender.NativeWorkerSecondCB.carry,
      Airbender.NativeWorkerCB.cLimb,Airbender.NativeWorkerCB.cInput,Airbender.NativeWorkerCB.dLimb,Airbender.NativeWorkerCB.dByte,Airbender.NativeWorkerCB.carry,
      observed,initialColumns,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
private theorem b_reconstruction (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) :
    bInput w diagonal limb = (query w diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩)[0] +
      128*(query w diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[0] := by
  rw [value0 w diagonal _,value0 w diagonal _]
  fin_cases diagonal <;> fin_cases limb <;>
    simp [bInput,Airbender.NativeWorkerDiagonalAD.bInput,sourceExpressions,Expression.eval,environment] <;> ring
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
      ⟨7+12*diagonal.val+limb.val,by change 7+12*diagonal.val+limb.val < 64; have := diagonal.isLt; have := limb.isLt; omega⟩ =
      booleanSyntax (488+44*diagonal.val+limb.val) := by
  fin_cases diagonal <;> fin_cases limb <;> rfl

theorem carry_bits {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (diagonal : Fin 4) (limb : Fin 2) : (carry w diagonal limb).val ≤ 1 := by
  have bit := assertion_of_holds (block1 holds)
    ⟨7+12*diagonal.val+limb.val,by change 7+12*diagonal.val+limb.val < 64; have := diagonal.isLt; have := limb.isLt; omega⟩
  rw [bit_shape] at bit
  simp [booleanSyntax,Expression.eval,environment] at bit
  obtain ⟨n,bound,same⟩ := Airbender.Arithmetic.boolean_nat (by linear_combination bit)
  change (w (488+44*diagonal.val+limb.val)).val ≤ 1
  rw [same]
  simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

private def width (piece : Fin 2) : Nat := #v[7,9][piece]
private theorem query_effects {w : Nat → F} (effects : LookupEffects w)
    (diagonal : Fin 4) (limb : Fin 2) (piece : Fin 2) :
    (query w diagonal ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[0].val < 2^width piece ∧
    (query w diagonal ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[1].val < 2^width piece ∧
    (query w diagonal ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2].val < 2^width piece ∧
    (query w diagonal ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2].val =
      (query w diagonal ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[0].val ^^^
      (query w diagonal ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[1].val := by
  let slot : Fin 208 := ⟨86+18*diagonal.val+(2*limb.val+piece.val),by have := diagonal.isLt; have := limb.isLt; have := piece.isLt; omega⟩
  have bound : (fixedKind slot).bound = 2^width piece := by
    dsimp only [slot]
    fin_cases diagonal <;> fin_cases limb <;> fin_cases piece <;> norm_num [fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound,width]
  exact ⟨by simpa only [bound,query,slot] using effects.leftBounds slot,
    by simpa only [bound,query,slot] using effects.rightBounds slot,
    by simpa only [bound,query,slot] using effects.outputBounds slot,effects.results slot⟩

theorem limb_bounds {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (cLimb w diagonal limb).val < 65536 := by
  have lo := query_effects effects diagonal limb 0
  have hi := query_effects effects diagonal limb 1
  have lb : (query w diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩)[1].val < 128 := lo.2.1
  have hb : (query w diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[1].val < 512 := hi.2.1
  rw [c_reconstruction]
  exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 128 (by omega)

private theorem output_value (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) (piece : Fin 2) :
    (query w diagonal ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2] = w (492+44*diagonal.val+2*limb.val+piece.val) := by
  rw [value2]
  fin_cases diagonal <;> fin_cases limb <;> fin_cases piece <;> simp [sourceExpressions,Expression.eval,environment]
private theorem xor16 (a c : BitVec 9) (b d : BitVec 7) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem xor32 (a b c d : BitVec 16) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem half_xor {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (BitVec.ofNat 16 (bInput w diagonal limb).val ^^^ BitVec.ofNat 16 (cLimb w diagonal limb).val) =
      BitVec.append (chunk9 w diagonal limb) (chunk7 w diagonal limb) := by
  have lo := query_effects effects diagonal limb 0
  have hi := query_effects effects diagonal limb 1
  have b := Airbender.NativeWorkerSecondCBProofs.pair_pack _ _ _ lo.1 hi.1 (b_reconstruction w diagonal limb)
  have c := Airbender.NativeWorkerSecondCBProofs.pair_pack _ _ _ lo.2.1 hi.2.1 (c_reconstruction w diagonal limb)
  have x0 := Airbender.NativeWorkerCBProofs.piece_xor 7 _ _ _ lo.1 lo.2.1 lo.2.2.1 lo.2.2.2
  have x1 := Airbender.NativeWorkerCBProofs.piece_xor 9 _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  let q0 := query w diagonal (⟨2*limb.val,by have := limb.isLt; omega⟩ : Fin 4)
  let q1 := query w diagonal (⟨2*limb.val+1,by have := limb.isLt; omega⟩ : Fin 4)
  change BitVec.ofNat 16 (bInput w diagonal limb).val = BitVec.append (BitVec.ofNat 9 q1[0].val) (BitVec.ofNat 7 q0[0].val) at b
  change BitVec.ofNat 16 (cLimb w diagonal limb).val = BitVec.append (BitVec.ofNat 9 q1[1].val) (BitVec.ofNat 7 q0[1].val) at c
  rw [output_value] at x0 x1
  change BitVec.ofNat 7 (w (492+44*diagonal.val+2*limb.val)).val =
    (BitVec.ofNat 7 q0[0].val ^^^ BitVec.ofNat 7 q0[1].val) at x0
  change BitVec.ofNat 9 (w (492+44*diagonal.val+2*limb.val+1)).val =
    (BitVec.ofNat 9 q1[0].val ^^^ BitVec.ofNat 9 q1[1].val) at x1
  rw [show 492+44*diagonal.val+2*limb.val+1 = 493+44*diagonal.val+2*limb.val by omega] at x1
  rw [b,c,xor16,← x0,← x1]
  rfl

theorem rotated {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) :
    bAfter w diagonal = (Airbender.NativeWorkerFirstG.pack (bInput w diagonal 0) (bInput w diagonal 1) ^^^
      Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1)).rotateRight 7 := by
  unfold bAfter Airbender.NativeWorkerFirstG.pack
  rw [xor32,half_xor effects,half_xor effects,← Airbender.NativeWorkerSecondCBProofs.rotate7]



/-- Exact original second D-output syntax, before witness evaluation. -/
private theorem d_shape (diagonal : Fin 4) (piece : Fin 4) :
    (fixedExpressions ⟨82+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[2] =
      .var ⟨484+44*diagonal.val+piece.val⟩ := by
  fin_cases diagonal <;> fin_cases piece <;> rfl
private theorem d_byte_bounds {w : Nat → F} (effects : LookupEffects w)
    (diagonal : Fin 4) (piece : Fin 4) : (dByte w diagonal piece).val < 256 := by
  let slot : Fin 208 := ⟨82+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩
  have kind : fixedKind slot = .byte := by
    dsimp only [slot]
    fin_cases diagonal <;> fin_cases piece <;> norm_num [fixedKind]
  have same : (fixedQuery w slot)[2] = dByte w diagonal piece := by
    simpa [fixedQuery,dByte,slot,Expression.eval,environment] using congrArg (Expression.eval (environment w)) (d_shape diagonal piece)
  have h := effects.outputBounds slot
  rw [same] at h
  simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound] using h

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
    Airbender.NativeWorkerFirstG.pack (dLimb w diagonal 0) (dLimb w diagonal 1) = Airbender.NativeWorkerDiagonalAD.dAfter w diagonal := by
  have low := Airbender.NativeWorkerFirstGProofs.pair_bytes
    (dByte w diagonal 1+256*dByte w diagonal 2) _ _ (d_byte_bounds effects diagonal 1) (d_byte_bounds effects diagonal 2) rfl
  have high := Airbender.NativeWorkerFirstGProofs.pair_bytes
    (dByte w diagonal 3+256*dByte w diagonal 0) _ _ (d_byte_bounds effects diagonal 3) (d_byte_bounds effects diagonal 0) rfl
  change BitVec.append (BitVec.ofNat 16 (dByte w diagonal 3+256*dByte w diagonal 0).val)
    (BitVec.ofNat 16 (dByte w diagonal 1+256*dByte w diagonal 2).val) = _
  rw [low,high]
  rfl

theorem mixing {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  exact ⟨carry_bits holds,limb_bounds effects,rotated effects⟩

theorem addition {w : Nat → F} (prior : Airbender.NativeWorkerDiagonalAD.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (diagonal : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1) =
      Airbender.NativeWorkerFirstG.pack (Airbender.NativeWorkerDiagonalCB.cLimb w diagonal 0) (Airbender.NativeWorkerDiagonalCB.cLimb w diagonal 1) +
        Airbender.NativeWorkerDiagonalAD.dAfter w diagonal := by
  have cb (limb : Fin 2) : (cInput w diagonal limb).val < 65536 := (prior.prior.mixing.bounds diagonal limb).1
  have field (limb : Fin 2) : cInput w diagonal limb+dLimb w diagonal limb+(0 : F)+
      (if limb.val = 0 then 0 else carry w diagonal 0) = cLimb w diagonal limb+65536*carry w diagonal limb := by
    unfold cLimb
    ring
  have low := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ (0 : F) (0 : F) _ _
    (cb 0) (d_bounds effects diagonal 0) (by decide +kernel) (by decide +kernel)
    ((localEffects.carries diagonal 0).trans (by decide +kernel)) (localEffects.bounds diagonal 0) (by simpa using field 0)
  have high := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ (0 : F) _ _ _
    (cb 1) (d_bounds effects diagonal 1) (by decide +kernel)
    ((localEffects.carries diagonal 0).trans (by decide +kernel)) ((localEffects.carries diagonal 1).trans (by decide +kernel))
    (localEffects.bounds diagonal 1) (by simpa using field 1)
  simp only [ZMod.val_zero,Nat.add_zero] at low high
  rw [← d_pack effects diagonal]
  change Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1) =
    Airbender.NativeWorkerFirstG.pack (cInput w diagonal 0) (cInput w diagonal 1) + Airbender.NativeWorkerFirstG.pack (dLimb w diagonal 0) (dLimb w diagonal 1)
  rw [Airbender.NativeWorkerAdditionProofs.pack_value _ _ (localEffects.bounds diagonal 0) (localEffects.bounds diagonal 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (cb 0) (cb 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (d_bounds effects diagonal 0) (d_bounds effects diagonal 1)]
  simpa using Airbender.NativeWorkerAdditionProofs.wide_add _ _ _ _ 0 0 _ _ _ _ low high

theorem chained_rotated {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) :
    bAfter w diagonal = (Airbender.NativeWorkerDiagonalCB.bAfter w diagonal ^^^
      Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1)).rotateRight 7 := by
  rw [← (Airbender.NativeWorkerDiagonalADProofs.b_halves effects diagonal).2.2]
  exact rotated effects diagonal

theorem diagonal {w : Nat → F} (prior : Airbender.NativeWorkerDiagonalAD.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (diagonal : Fin 4) :
    diagonalResult w diagonal = Airbender.NativeWorkerSecondCB.g
      (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 0)
      (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 1)
      (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 2)
      (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 3)
      (Airbender.NativeWorkerAddition.messageWord w ⟨8+2*diagonal.val,by have := diagonal.isLt; omega⟩)
      (Airbender.NativeWorkerAddition.messageWord w ⟨9+2*diagonal.val,by have := diagonal.isLt; omega⟩) := by
  have a1 := prior.prior.prior.added diagonal
  have d1 := prior.prior.prior.mixing.rotated diagonal
  have c1 := prior.prior.added diagonal
  have b1 := prior.prior.mixing.rotated diagonal
  have a2 := prior.added diagonal
  have d2 := prior.chained diagonal
  have c2 := addition prior effects localEffects diagonal
  have b2 := chained_rotated effects diagonal
  change Airbender.NativeWorkerDiagonalCB.bAfter w diagonal =
    (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 1 ^^^
      Airbender.NativeWorkerFirstG.pack (Airbender.NativeWorkerDiagonalCB.cLimb w diagonal 0) (Airbender.NativeWorkerDiagonalCB.cLimb w diagonal 1)).rotateRight 12 at b1
  simp only [diagonalResult,Airbender.NativeWorkerSecondCB.g,b2,c2,d2,a2,b1,c1,d1,a1]

theorem row {w : Nat → F} (prior : Airbender.NativeWorkerDiagonalAD.RowEffects w)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerDiagonalG.RowEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have localEffects := mixing holds
  exact ⟨prior,localEffects,addition prior effects localEffects,chained_rotated effects,diagonal prior effects localEffects⟩
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerDiagonalG.RowEffects w := by
  have prior := Airbender.NativeWorkerDiagonalADProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior.1,fun w member => row (prior.2 w member) (processing w member).body⟩
end Airbender.NativeWorkerDiagonalGProofs
