module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part059
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

local instance generatedBatch60Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch60Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding160 :
    NumericPolynomialChecks.encodeCombination native.witness160 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 160 [] := by kernel_rfl

theorem native.idealInputsBinding160 :
    CleanExpression.inputs native.expression160 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 160 [] := by kernel_rfl

theorem native.checked160 :
    equal (CleanExpression.polynomial native.placement native.expression160)
        (combination native.relations native.witness160) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression160 native.witness160
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    160 (by decide +kernel) native.idealCodeBinding160 native.idealRelationsBinding native.idealWitnessBinding160

theorem native.preserved160 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression160).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression160 native.placement native.relations native.witness160
    native.checked160 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression161 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨68⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨68⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness161 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨193, by decide⟩)]

theorem native.idealCodeBinding161 :
    CleanIdealChecks.encode native.placement native.expression161 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 161 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding161 :
    NumericPolynomialChecks.encodeCombination native.witness161 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 161 [] := by kernel_rfl

theorem native.idealInputsBinding161 :
    CleanExpression.inputs native.expression161 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 161 [] := by kernel_rfl

theorem native.checked161 :
    equal (CleanExpression.polynomial native.placement native.expression161)
        (combination native.relations native.witness161) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression161 native.witness161
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    161 (by decide +kernel) native.idealCodeBinding161 native.idealRelationsBinding native.idealWitnessBinding161

theorem native.preserved161 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression161).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression161 native.placement native.relations native.witness161
    native.checked161 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression162 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨69⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨69⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness162 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨194, by decide⟩)]

theorem native.idealCodeBinding162 :
    CleanIdealChecks.encode native.placement native.expression162 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 162 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding162 :
    NumericPolynomialChecks.encodeCombination native.witness162 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 162 [] := by kernel_rfl

theorem native.idealInputsBinding162 :
    CleanExpression.inputs native.expression162 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 162 [] := by kernel_rfl

theorem native.checked162 :
    equal (CleanExpression.polynomial native.placement native.expression162)
        (combination native.relations native.witness162) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression162 native.witness162
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    162 (by decide +kernel) native.idealCodeBinding162 native.idealRelationsBinding native.idealWitnessBinding162

theorem native.preserved162 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression162).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression162 native.placement native.relations native.witness162
    native.checked162 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression163 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨70⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨70⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness163 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨195, by decide⟩)]

theorem native.idealCodeBinding163 :
    CleanIdealChecks.encode native.placement native.expression163 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 163 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding163 :
    NumericPolynomialChecks.encodeCombination native.witness163 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 163 [] := by kernel_rfl

theorem native.idealInputsBinding163 :
    CleanExpression.inputs native.expression163 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 163 [] := by kernel_rfl

theorem native.checked163 :
    equal (CleanExpression.polynomial native.placement native.expression163)
        (combination native.relations native.witness163) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression163 native.witness163
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    163 (by decide +kernel) native.idealCodeBinding163 native.idealRelationsBinding native.idealWitnessBinding163
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
