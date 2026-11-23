module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part047
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

local instance generatedBatch48Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch48Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding119 :
    CleanIdealChecks.encode native.placement native.expression119 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 119 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding119 :
    NumericPolynomialChecks.encodeCombination native.witness119 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 119 [] := by kernel_rfl

theorem native.idealInputsBinding119 :
    CleanExpression.inputs native.expression119 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 119 [] := by kernel_rfl

theorem native.checked119 :
    equal (CleanExpression.polynomial native.placement native.expression119)
        (combination native.relations native.witness119) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression119 native.witness119
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    119 (by decide +kernel) native.idealCodeBinding119 native.idealRelationsBinding native.idealWitnessBinding119

theorem native.preserved119 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression119).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression119 native.placement native.relations native.witness119
    native.checked119 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression120 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨55⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨57⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness120 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨152, by decide⟩)]

theorem native.idealCodeBinding120 :
    CleanIdealChecks.encode native.placement native.expression120 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 120 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding120 :
    NumericPolynomialChecks.encodeCombination native.witness120 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 120 [] := by kernel_rfl

theorem native.idealInputsBinding120 :
    CleanExpression.inputs native.expression120 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 120 [] := by kernel_rfl

theorem native.checked120 :
    equal (CleanExpression.polynomial native.placement native.expression120)
        (combination native.relations native.witness120) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression120 native.witness120
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    120 (by decide +kernel) native.idealCodeBinding120 native.idealRelationsBinding native.idealWitnessBinding120

theorem native.preserved120 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression120).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression120 native.placement native.relations native.witness120
    native.checked120 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression121 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨56⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨58⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness121 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨153, by decide⟩)]

theorem native.idealCodeBinding121 :
    CleanIdealChecks.encode native.placement native.expression121 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 121 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding121 :
    NumericPolynomialChecks.encodeCombination native.witness121 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 121 [] := by kernel_rfl

theorem native.idealInputsBinding121 :
    CleanExpression.inputs native.expression121 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 121 [] := by kernel_rfl

theorem native.checked121 :
    equal (CleanExpression.polynomial native.placement native.expression121)
        (combination native.relations native.witness121) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression121 native.witness121
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    121 (by decide +kernel) native.idealCodeBinding121 native.idealRelationsBinding native.idealWitnessBinding121

theorem native.preserved121 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression121).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression121 native.placement native.relations native.witness121
    native.checked121 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression122 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨59⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨61⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness122 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨154, by decide⟩)]

theorem native.idealCodeBinding122 :
    CleanIdealChecks.encode native.placement native.expression122 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 122 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding122 :
    NumericPolynomialChecks.encodeCombination native.witness122 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 122 [] := by kernel_rfl

theorem native.idealInputsBinding122 :
    CleanExpression.inputs native.expression122 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 122 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
