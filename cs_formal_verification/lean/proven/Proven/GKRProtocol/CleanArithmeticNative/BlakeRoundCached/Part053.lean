module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part052
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

local instance generatedBatch53Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch53Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding64 :
    NumericPolynomialChecks.encodeCombination native.witness64 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 64 [] := by kernel_rfl

theorem native.idealInputsBinding64 :
    CleanExpression.inputs native.expression64 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 64 [] := by kernel_rfl

theorem native.checked64 :
    equal (CleanExpression.polynomial native.placement native.expression64)
        (combination native.relations native.witness64) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression64 native.witness64
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 64 (by decide +kernel) native.idealCodeBinding64
    native.idealRelationsBinding native.idealWitnessBinding64

theorem native.preserved64 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression64).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression64 native.placement native.relations native.witness64
    native.checked64 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression65 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨143⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨215⟩))

noncomputable def native.witness65 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨155, by decide⟩)]

theorem native.idealCodeBinding65 :
    CleanIdealChecks.encode native.placement native.expression65 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 65 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding65 :
    NumericPolynomialChecks.encodeCombination native.witness65 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 65 [] := by kernel_rfl

theorem native.idealInputsBinding65 :
    CleanExpression.inputs native.expression65 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 65 [] := by kernel_rfl

theorem native.checked65 :
    equal (CleanExpression.polynomial native.placement native.expression65)
        (combination native.relations native.witness65) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression65 native.witness65
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 65 (by decide +kernel) native.idealCodeBinding65
    native.idealRelationsBinding native.idealWitnessBinding65

theorem native.preserved65 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression65).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression65 native.placement native.relations native.witness65
    native.checked65 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression66 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨144⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨216⟩))

noncomputable def native.witness66 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨156, by decide⟩)]

theorem native.idealCodeBinding66 :
    CleanIdealChecks.encode native.placement native.expression66 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 66 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding66 :
    NumericPolynomialChecks.encodeCombination native.witness66 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 66 [] := by kernel_rfl

theorem native.idealInputsBinding66 :
    CleanExpression.inputs native.expression66 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 66 [] := by kernel_rfl

theorem native.checked66 :
    equal (CleanExpression.polynomial native.placement native.expression66)
        (combination native.relations native.witness66) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression66 native.witness66
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 66 (by decide +kernel) native.idealCodeBinding66
    native.idealRelationsBinding native.idealWitnessBinding66

theorem native.preserved66 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression66).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression66 native.placement native.relations native.witness66
    native.checked66 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression67 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨145⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨217⟩))

noncomputable def native.witness67 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨157, by decide⟩)]

theorem native.idealCodeBinding67 :
    CleanIdealChecks.encode native.placement native.expression67 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 67 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding67 :
    NumericPolynomialChecks.encodeCombination native.witness67 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 67 [] := by kernel_rfl

theorem native.idealInputsBinding67 :
    CleanExpression.inputs native.expression67 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 67 [] := by kernel_rfl

theorem native.checked67 :
    equal (CleanExpression.polynomial native.placement native.expression67)
        (combination native.relations native.witness67) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression67 native.witness67
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 67 (by decide +kernel) native.idealCodeBinding67
    native.idealRelationsBinding native.idealWitnessBinding67
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
