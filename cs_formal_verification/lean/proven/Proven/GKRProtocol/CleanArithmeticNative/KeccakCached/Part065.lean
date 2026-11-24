module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part064
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.KeccakCached
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCached
public import Proven.GKRProtocol.CleanPlacementNative.KeccakCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch65Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch65Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding177 :
    CleanExpression.inputs native.expression177 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 177 [] := by kernel_rfl

theorem native.checked177 :
    equal (CleanExpression.polynomial native.placement native.expression177)
        (combination native.relations native.witness177) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression177 native.witness177
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    177 (by decide +kernel) native.idealCodeBinding177 native.idealRelationsBinding native.idealWitnessBinding177

theorem native.preserved177 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression177).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression177 native.placement native.relations native.witness177
    native.checked177 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression178 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨239⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨239⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness178 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨210, by decide⟩)]

theorem native.idealCodeBinding178 :
    CleanIdealChecks.encode native.placement native.expression178 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 178 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding178 :
    NumericPolynomialChecks.encodeCombination native.witness178 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 178 [] := by kernel_rfl

theorem native.idealInputsBinding178 :
    CleanExpression.inputs native.expression178 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 178 [] := by kernel_rfl

theorem native.checked178 :
    equal (CleanExpression.polynomial native.placement native.expression178)
        (combination native.relations native.witness178) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression178 native.witness178
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    178 (by decide +kernel) native.idealCodeBinding178 native.idealRelationsBinding native.idealWitnessBinding178

theorem native.preserved178 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression178).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression178 native.placement native.relations native.witness178
    native.checked178 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression179 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨242⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨242⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness179 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨211, by decide⟩)]

theorem native.idealCodeBinding179 :
    CleanIdealChecks.encode native.placement native.expression179 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 179 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding179 :
    NumericPolynomialChecks.encodeCombination native.witness179 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 179 [] := by kernel_rfl

theorem native.idealInputsBinding179 :
    CleanExpression.inputs native.expression179 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 179 [] := by kernel_rfl

theorem native.checked179 :
    equal (CleanExpression.polynomial native.placement native.expression179)
        (combination native.relations native.witness179) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression179 native.witness179
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    179 (by decide +kernel) native.idealCodeBinding179 native.idealRelationsBinding native.idealWitnessBinding179

theorem native.preserved179 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression179).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression179 native.placement native.relations native.witness179
    native.checked179 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression180 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨245⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨245⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness180 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨212, by decide⟩)]

theorem native.idealCodeBinding180 :
    CleanIdealChecks.encode native.placement native.expression180 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 180 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding180 :
    NumericPolynomialChecks.encodeCombination native.witness180 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 180 [] := by kernel_rfl

theorem native.idealInputsBinding180 :
    CleanExpression.inputs native.expression180 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 180 [] := by kernel_rfl

theorem native.checked180 :
    equal (CleanExpression.polynomial native.placement native.expression180)
        (combination native.relations native.witness180) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression180 native.witness180
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    180 (by decide +kernel) native.idealCodeBinding180 native.idealRelationsBinding native.idealWitnessBinding180

theorem native.preserved180 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression180).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression180 native.placement native.relations native.witness180
    native.checked180 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
