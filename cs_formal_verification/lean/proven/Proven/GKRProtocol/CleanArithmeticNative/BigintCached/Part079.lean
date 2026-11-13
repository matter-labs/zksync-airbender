module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part078
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BigintCached
public import Proven.GKRProtocol.FullArithmeticNative.BigintCached
public import Proven.GKRProtocol.CleanPlacementNative.BigintCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch79Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch79Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked109 :
    equal (CleanExpression.polynomial native.placement native.expression109)
        (combination native.relations native.witness109) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression109 native.witness109
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    109 (by decide +kernel) native.idealCodeBinding109 native.idealRelationsBinding native.idealWitnessBinding109

theorem native.preserved109 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression109).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression109 native.placement native.relations native.witness109
    native.checked109 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression110 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨94⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨94⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness110 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨151, by decide⟩)]

theorem native.idealCodeBinding110 :
    CleanIdealChecks.encode native.placement native.expression110 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 110 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding110 :
    NumericPolynomialChecks.encodeCombination native.witness110 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 110 [] := by kernel_rfl

theorem native.idealInputsBinding110 :
    CleanExpression.inputs native.expression110 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 110 [] := by kernel_rfl

theorem native.checked110 :
    equal (CleanExpression.polynomial native.placement native.expression110)
        (combination native.relations native.witness110) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression110 native.witness110
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    110 (by decide +kernel) native.idealCodeBinding110 native.idealRelationsBinding native.idealWitnessBinding110

theorem native.preserved110 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression110).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression110 native.placement native.relations native.witness110
    native.checked110 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression111 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨95⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨95⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness111 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨152, by decide⟩)]

theorem native.idealCodeBinding111 :
    CleanIdealChecks.encode native.placement native.expression111 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 111 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding111 :
    NumericPolynomialChecks.encodeCombination native.witness111 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 111 [] := by kernel_rfl

theorem native.idealInputsBinding111 :
    CleanExpression.inputs native.expression111 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 111 [] := by kernel_rfl

theorem native.checked111 :
    equal (CleanExpression.polynomial native.placement native.expression111)
        (combination native.relations native.witness111) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression111 native.witness111
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    111 (by decide +kernel) native.idealCodeBinding111 native.idealRelationsBinding native.idealWitnessBinding111

theorem native.preserved111 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression111).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression111 native.placement native.relations native.witness111
    native.checked111 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression112 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨96⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨96⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness112 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨153, by decide⟩)]

theorem native.idealCodeBinding112 :
    CleanIdealChecks.encode native.placement native.expression112 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 112 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding112 :
    NumericPolynomialChecks.encodeCombination native.witness112 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 112 [] := by kernel_rfl

theorem native.idealInputsBinding112 :
    CleanExpression.inputs native.expression112 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 112 [] := by kernel_rfl

theorem native.checked112 :
    equal (CleanExpression.polynomial native.placement native.expression112)
        (combination native.relations native.witness112) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression112 native.witness112
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    112 (by decide +kernel) native.idealCodeBinding112 native.idealRelationsBinding native.idealWitnessBinding112

theorem native.preserved112 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression112).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression112 native.placement native.relations native.witness112
    native.checked112 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression113 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨97⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨97⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
end Airbender.Compiler.CleanArithmeticNative.BigintCached
