module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part086
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

local instance generatedBatch87Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch87Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding108 :
    NumericPolynomialChecks.encodeCombination native.witness108 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 108 [] := by kernel_rfl

theorem native.idealInputsBinding108 :
    CleanExpression.inputs native.expression108 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 108 [] := by kernel_rfl

theorem native.checked108 :
    equal (CleanExpression.polynomial native.placement native.expression108)
        (combination native.relations native.witness108) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression108 native.witness108
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 108 (by decide +kernel) native.idealCodeBinding108
    native.idealRelationsBinding native.idealWitnessBinding108

theorem native.preserved108 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression108).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression108 native.placement native.relations native.witness108
    native.checked108 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression109 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨546⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 128) : Source.BaseField)))
                (Airbender.Expression.var ⟨547⟩))))
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
        (Airbender.Expression.var ⟨6⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨8⟩))

noncomputable def native.witness109 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨199, by decide⟩)]

theorem native.idealCodeBinding109 :
    CleanIdealChecks.encode native.placement native.expression109 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 109 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding109 :
    NumericPolynomialChecks.encodeCombination native.witness109 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 109 [] := by kernel_rfl

theorem native.idealInputsBinding109 :
    CleanExpression.inputs native.expression109 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 109 [] := by kernel_rfl

theorem native.checked109 :
    equal (CleanExpression.polynomial native.placement native.expression109)
        (combination native.relations native.witness109) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression109 native.witness109
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 109 (by decide +kernel) native.idealCodeBinding109
    native.idealRelationsBinding native.idealWitnessBinding109

theorem native.preserved109 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression109).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression109 native.placement native.relations native.witness109
    native.checked109 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression110 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨552⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 128) : Source.BaseField)))
                (Airbender.Expression.var ⟨553⟩))))
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
        (Airbender.Expression.var ⟨9⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨11⟩))

noncomputable def native.witness110 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨200, by decide⟩)]

theorem native.idealCodeBinding110 :
    CleanIdealChecks.encode native.placement native.expression110 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 110 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding110 :
    NumericPolynomialChecks.encodeCombination native.witness110 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 110 [] := by kernel_rfl

theorem native.idealInputsBinding110 :
    CleanExpression.inputs native.expression110 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 110 [] := by kernel_rfl

theorem native.checked110 :
    equal (CleanExpression.polynomial native.placement native.expression110)
        (combination native.relations native.witness110) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression110 native.witness110
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 110 (by decide +kernel) native.idealCodeBinding110
    native.idealRelationsBinding native.idealWitnessBinding110

theorem native.preserved110 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression110).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression110 native.placement native.relations native.witness110
    native.checked110 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression111 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨558⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 128) : Source.BaseField)))
                (Airbender.Expression.var ⟨559⟩))))
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
        (Airbender.Expression.var ⟨10⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨12⟩))

noncomputable def native.witness111 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨201, by decide⟩)]

theorem native.idealCodeBinding111 :
    CleanIdealChecks.encode native.placement native.expression111 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 111 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding111 :
    NumericPolynomialChecks.encodeCombination native.witness111 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 111 [] := by kernel_rfl

theorem native.idealInputsBinding111 :
    CleanExpression.inputs native.expression111 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 111 [] := by kernel_rfl

theorem native.checked111 :
    equal (CleanExpression.polynomial native.placement native.expression111)
        (combination native.relations native.witness111) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression111 native.witness111
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 111 (by decide +kernel) native.idealCodeBinding111
    native.idealRelationsBinding native.idealWitnessBinding111
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
