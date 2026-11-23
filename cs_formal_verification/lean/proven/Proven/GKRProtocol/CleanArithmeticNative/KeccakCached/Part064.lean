module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part063
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

local instance generatedBatch64Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch64Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness174 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨206, by decide⟩)]

theorem native.idealCodeBinding174 :
    CleanIdealChecks.encode native.placement native.expression174 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 174 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding174 :
    NumericPolynomialChecks.encodeCombination native.witness174 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 174 [] := by kernel_rfl

theorem native.idealInputsBinding174 :
    CleanExpression.inputs native.expression174 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 174 [] := by kernel_rfl

theorem native.checked174 :
    equal (CleanExpression.polynomial native.placement native.expression174)
        (combination native.relations native.witness174) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression174 native.witness174
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    174 (by decide +kernel) native.idealCodeBinding174 native.idealRelationsBinding native.idealWitnessBinding174

theorem native.preserved174 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression174).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression174 native.placement native.relations native.witness174
    native.checked174 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression175 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨230⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨230⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness175 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨207, by decide⟩)]

theorem native.idealCodeBinding175 :
    CleanIdealChecks.encode native.placement native.expression175 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 175 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding175 :
    NumericPolynomialChecks.encodeCombination native.witness175 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 175 [] := by kernel_rfl

theorem native.idealInputsBinding175 :
    CleanExpression.inputs native.expression175 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 175 [] := by kernel_rfl

theorem native.checked175 :
    equal (CleanExpression.polynomial native.placement native.expression175)
        (combination native.relations native.witness175) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression175 native.witness175
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    175 (by decide +kernel) native.idealCodeBinding175 native.idealRelationsBinding native.idealWitnessBinding175

theorem native.preserved175 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression175).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression175 native.placement native.relations native.witness175
    native.checked175 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression176 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨233⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨233⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness176 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨208, by decide⟩)]

theorem native.idealCodeBinding176 :
    CleanIdealChecks.encode native.placement native.expression176 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 176 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding176 :
    NumericPolynomialChecks.encodeCombination native.witness176 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 176 [] := by kernel_rfl

theorem native.idealInputsBinding176 :
    CleanExpression.inputs native.expression176 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 176 [] := by kernel_rfl

theorem native.checked176 :
    equal (CleanExpression.polynomial native.placement native.expression176)
        (combination native.relations native.witness176) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression176 native.witness176
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    176 (by decide +kernel) native.idealCodeBinding176 native.idealRelationsBinding native.idealWitnessBinding176

theorem native.preserved176 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression176).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression176 native.placement native.relations native.witness176
    native.checked176 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression177 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨236⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨236⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness177 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨209, by decide⟩)]

theorem native.idealCodeBinding177 :
    CleanIdealChecks.encode native.placement native.expression177 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 177 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding177 :
    NumericPolynomialChecks.encodeCombination native.witness177 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 177 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
