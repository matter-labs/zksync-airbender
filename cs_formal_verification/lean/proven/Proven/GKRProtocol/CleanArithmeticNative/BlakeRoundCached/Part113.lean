module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part112
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BlakeRoundCached
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCached
public import Proven.GKRProtocol.CleanPlacementNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch113Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch113Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding197 :
    CleanExpression.inputs native.expression197 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 197 [] := by kernel_rfl

theorem native.checked197 :
    equal (CleanExpression.polynomial native.placement native.expression197)
        (combination native.relations native.witness197) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression197 native.witness197
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 197 (by decide +kernel) native.idealCodeBinding197
    native.idealRelationsBinding native.idealWitnessBinding197

theorem native.preserved197 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression197).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression197 native.placement native.relations native.witness197
    native.checked197 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression198 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨697⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨697⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness198 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨288, by decide⟩)]

theorem native.idealCodeBinding198 :
    CleanIdealChecks.encode native.placement native.expression198 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 198 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding198 :
    NumericPolynomialChecks.encodeCombination native.witness198 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 198 [] := by kernel_rfl

theorem native.idealInputsBinding198 :
    CleanExpression.inputs native.expression198 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 198 [] := by kernel_rfl

theorem native.checked198 :
    equal (CleanExpression.polynomial native.placement native.expression198)
        (combination native.relations native.witness198) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression198 native.witness198
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 198 (by decide +kernel) native.idealCodeBinding198
    native.idealRelationsBinding native.idealWitnessBinding198

theorem native.preserved198 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression198).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression198 native.placement native.relations native.witness198
    native.checked198 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression199 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨700⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨700⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness199 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨289, by decide⟩)]

theorem native.idealCodeBinding199 :
    CleanIdealChecks.encode native.placement native.expression199 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 199 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding199 :
    NumericPolynomialChecks.encodeCombination native.witness199 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 199 [] := by kernel_rfl

theorem native.idealInputsBinding199 :
    CleanExpression.inputs native.expression199 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 199 [] := by kernel_rfl

theorem native.checked199 :
    equal (CleanExpression.polynomial native.placement native.expression199)
        (combination native.relations native.witness199) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression199 native.witness199
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 199 (by decide +kernel) native.idealCodeBinding199
    native.idealRelationsBinding native.idealWitnessBinding199

theorem native.preserved199 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression199).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression199 native.placement native.relations native.witness199
    native.checked199 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression200 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨703⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨703⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness200 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨290, by decide⟩)]

theorem native.idealCodeBinding200 :
    CleanIdealChecks.encode native.placement native.expression200 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 200 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding200 :
    NumericPolynomialChecks.encodeCombination native.witness200 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 200 [] := by kernel_rfl

theorem native.idealInputsBinding200 :
    CleanExpression.inputs native.expression200 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 200 [] := by kernel_rfl

theorem native.checked200 :
    equal (CleanExpression.polynomial native.placement native.expression200)
        (combination native.relations native.witness200) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression200 native.witness200
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 200 (by decide +kernel) native.idealCodeBinding200
    native.idealRelationsBinding native.idealWitnessBinding200

theorem native.preserved200 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression200).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression200 native.placement native.relations native.witness200
    native.checked200 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
