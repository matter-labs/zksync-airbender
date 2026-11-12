module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part088
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

local instance generatedBatch89Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch89Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding115 :
    CleanIdealChecks.encode native.placement native.expression115 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 115 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding115 :
    NumericPolynomialChecks.encodeCombination native.witness115 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 115 [] := by kernel_rfl

theorem native.idealInputsBinding115 :
    CleanExpression.inputs native.expression115 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 115 [] := by kernel_rfl

theorem native.checked115 :
    equal (CleanExpression.polynomial native.placement native.expression115)
        (combination native.relations native.witness115) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression115 native.witness115
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 115 (by decide +kernel) native.idealCodeBinding115
    native.idealRelationsBinding native.idealWitnessBinding115

theorem native.preserved115 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression115).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression115 native.placement native.relations native.witness115
    native.checked115 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression116 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨588⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                (Airbender.Expression.var ⟨589⟩))))
          (Airbender.Expression.var ⟨152⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨152⟩))))
        (Airbender.Expression.var ⟨21⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨23⟩))

noncomputable def native.witness116 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨206, by decide⟩)]

theorem native.idealCodeBinding116 :
    CleanIdealChecks.encode native.placement native.expression116 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 116 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding116 :
    NumericPolynomialChecks.encodeCombination native.witness116 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 116 [] := by kernel_rfl

theorem native.idealInputsBinding116 :
    CleanExpression.inputs native.expression116 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 116 [] := by kernel_rfl

theorem native.checked116 :
    equal (CleanExpression.polynomial native.placement native.expression116)
        (combination native.relations native.witness116) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression116 native.witness116
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 116 (by decide +kernel) native.idealCodeBinding116
    native.idealRelationsBinding native.idealWitnessBinding116

theorem native.preserved116 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression116).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression116 native.placement native.relations native.witness116
    native.checked116 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression117 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨594⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                (Airbender.Expression.var ⟨595⟩))))
          (Airbender.Expression.var ⟨152⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨152⟩))))
        (Airbender.Expression.var ⟨22⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨24⟩))

noncomputable def native.witness117 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨207, by decide⟩)]

theorem native.idealCodeBinding117 :
    CleanIdealChecks.encode native.placement native.expression117 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 117 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding117 :
    NumericPolynomialChecks.encodeCombination native.witness117 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 117 [] := by kernel_rfl

theorem native.idealInputsBinding117 :
    CleanExpression.inputs native.expression117 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 117 [] := by kernel_rfl

theorem native.checked117 :
    equal (CleanExpression.polynomial native.placement native.expression117)
        (combination native.relations native.witness117) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression117 native.witness117
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 117 (by decide +kernel) native.idealCodeBinding117
    native.idealRelationsBinding native.idealWitnessBinding117

theorem native.preserved117 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression117).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression117 native.placement native.relations native.witness117
    native.checked117 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression118 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨600⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                (Airbender.Expression.var ⟨601⟩))))
          (Airbender.Expression.var ⟨152⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨152⟩))))
        (Airbender.Expression.var ⟨25⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨27⟩))

noncomputable def native.witness118 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨208, by decide⟩)]

theorem native.idealCodeBinding118 :
    CleanIdealChecks.encode native.placement native.expression118 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 118 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding118 :
    NumericPolynomialChecks.encodeCombination native.witness118 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 118 [] := by kernel_rfl

theorem native.idealInputsBinding118 :
    CleanExpression.inputs native.expression118 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 118 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
