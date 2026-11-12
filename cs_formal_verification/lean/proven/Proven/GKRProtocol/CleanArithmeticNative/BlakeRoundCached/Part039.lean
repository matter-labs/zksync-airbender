module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part038
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

local instance generatedBatch39Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch39Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding16 :
    NumericPolynomialChecks.encodeCombination native.witness16 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 16 [] := by kernel_rfl

theorem native.idealInputsBinding16 :
    CleanExpression.inputs native.expression16 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 16 [] := by kernel_rfl

theorem native.checked16 :
    equal (CleanExpression.polynomial native.placement native.expression16)
        (combination native.relations native.witness16) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression16 native.witness16
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 16 (by decide +kernel) native.idealCodeBinding16
    native.idealRelationsBinding native.idealWitnessBinding16

theorem native.preserved16 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression16).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression16 native.placement native.relations native.witness16
    native.checked16 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression17 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨166⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨49⟩)))))
      (Airbender.Expression.var ⟨49⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨167⟩))

noncomputable def native.witness17 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨107, by decide⟩)]

theorem native.idealCodeBinding17 :
    CleanIdealChecks.encode native.placement native.expression17 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 17 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding17 :
    NumericPolynomialChecks.encodeCombination native.witness17 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 17 [] := by kernel_rfl

theorem native.idealInputsBinding17 :
    CleanExpression.inputs native.expression17 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 17 [] := by kernel_rfl

theorem native.checked17 :
    equal (CleanExpression.polynomial native.placement native.expression17)
        (combination native.relations native.witness17) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression17 native.witness17
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 17 (by decide +kernel) native.idealCodeBinding17
    native.idealRelationsBinding native.idealWitnessBinding17

theorem native.preserved17 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression17).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression17 native.placement native.relations native.witness17
    native.checked17 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression18 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 42319) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨18⟩)))))
      (Airbender.Expression.var ⟨18⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨168⟩))

noncomputable def native.witness18 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨108, by decide⟩)]

theorem native.idealCodeBinding18 :
    CleanIdealChecks.encode native.placement native.expression18 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 18 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding18 :
    NumericPolynomialChecks.encodeCombination native.witness18 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 18 [] := by kernel_rfl

theorem native.idealInputsBinding18 :
    CleanExpression.inputs native.expression18 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 18 [] := by kernel_rfl

theorem native.checked18 :
    equal (CleanExpression.polynomial native.placement native.expression18)
        (combination native.relations native.witness18) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression18 native.witness18
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 18 (by decide +kernel) native.idealCodeBinding18
    native.idealRelationsBinding native.idealWitnessBinding18

theorem native.preserved18 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression18).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression18 native.placement native.relations native.witness18
    native.checked18 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression19 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨168⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨50⟩)))))
      (Airbender.Expression.var ⟨50⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨169⟩))

noncomputable def native.witness19 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨109, by decide⟩)]

theorem native.idealCodeBinding19 :
    CleanIdealChecks.encode native.placement native.expression19 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 19 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding19 :
    NumericPolynomialChecks.encodeCombination native.witness19 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 19 [] := by kernel_rfl

theorem native.idealInputsBinding19 :
    CleanExpression.inputs native.expression19 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 19 [] := by kernel_rfl

theorem native.checked19 :
    equal (CleanExpression.polynomial native.placement native.expression19)
        (combination native.relations native.witness19) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression19 native.witness19
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 19 (by decide +kernel) native.idealCodeBinding19
    native.idealRelationsBinding native.idealWitnessBinding19
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
