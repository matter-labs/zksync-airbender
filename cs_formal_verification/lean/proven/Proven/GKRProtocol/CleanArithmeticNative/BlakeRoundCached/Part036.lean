module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part035
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

local instance generatedBatch36Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch36Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness6 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨96, by decide⟩)]

theorem native.idealCodeBinding6 :
    CleanIdealChecks.encode native.placement native.expression6 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 6 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding6 :
    NumericPolynomialChecks.encodeCombination native.witness6 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 6 [] := by kernel_rfl

theorem native.idealInputsBinding6 :
    CleanExpression.inputs native.expression6 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 6 [] := by kernel_rfl

theorem native.checked6 :
    equal (CleanExpression.polynomial native.placement native.expression6)
        (combination native.relations native.witness6) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression6 native.witness6
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 6 (by decide +kernel) native.idealCodeBinding6
    native.idealRelationsBinding native.idealWitnessBinding6

theorem native.preserved6 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression6).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression6 native.placement native.relations native.witness6
    native.checked6 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression7 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨156⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨38⟩)))))
      (Airbender.Expression.var ⟨38⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨157⟩))

noncomputable def native.witness7 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨97, by decide⟩)]

theorem native.idealCodeBinding7 :
    CleanIdealChecks.encode native.placement native.expression7 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 7 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding7 :
    NumericPolynomialChecks.encodeCombination native.witness7 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 7 [] := by kernel_rfl

theorem native.idealInputsBinding7 :
    CleanExpression.inputs native.expression7 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 7 [] := by kernel_rfl

theorem native.checked7 :
    equal (CleanExpression.polynomial native.placement native.expression7)
        (combination native.relations native.witness7) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression7 native.witness7
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 7 (by decide +kernel) native.idealCodeBinding7
    native.idealRelationsBinding native.idealWitnessBinding7

theorem native.preserved7 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression7).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression7 native.placement native.relations native.witness7
    native.checked7 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression8 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 44677) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨9⟩)))))
      (Airbender.Expression.var ⟨9⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨158⟩))

noncomputable def native.witness8 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨98, by decide⟩)]

theorem native.idealCodeBinding8 :
    CleanIdealChecks.encode native.placement native.expression8 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 8 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding8 :
    NumericPolynomialChecks.encodeCombination native.witness8 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 8 [] := by kernel_rfl

theorem native.idealInputsBinding8 :
    CleanExpression.inputs native.expression8 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 8 [] := by kernel_rfl

theorem native.checked8 :
    equal (CleanExpression.polynomial native.placement native.expression8)
        (combination native.relations native.witness8) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression8 native.witness8
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 8 (by decide +kernel) native.idealCodeBinding8
    native.idealRelationsBinding native.idealWitnessBinding8

theorem native.preserved8 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression8).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression8 native.placement native.relations native.witness8
    native.checked8 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression9 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨158⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨41⟩)))))
      (Airbender.Expression.var ⟨41⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨159⟩))

noncomputable def native.witness9 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨99, by decide⟩)]

theorem native.idealCodeBinding9 :
    CleanIdealChecks.encode native.placement native.expression9 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 9 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding9 :
    NumericPolynomialChecks.encodeCombination native.witness9 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 9 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
