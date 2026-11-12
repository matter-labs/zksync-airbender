module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part049
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

local instance generatedBatch50Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch50Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness126 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨158, by decide⟩)]

theorem native.idealCodeBinding126 :
    CleanIdealChecks.encode native.placement native.expression126 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 126 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding126 :
    NumericPolynomialChecks.encodeCombination native.witness126 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 126 [] := by kernel_rfl

theorem native.idealInputsBinding126 :
    CleanExpression.inputs native.expression126 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 126 [] := by kernel_rfl

theorem native.checked126 :
    equal (CleanExpression.polynomial native.placement native.expression126)
        (combination native.relations native.witness126) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression126 native.witness126
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    126 (by decide +kernel) native.idealCodeBinding126 native.idealRelationsBinding native.idealWitnessBinding126

theorem native.preserved126 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression126).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression126 native.placement native.relations native.witness126
    native.checked126 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression127 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨60⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨62⟩))))
    (Airbender.Expression.var ⟨66⟩)

noncomputable def native.witness127 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨159, by decide⟩)]

theorem native.idealCodeBinding127 :
    CleanIdealChecks.encode native.placement native.expression127 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 127 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding127 :
    NumericPolynomialChecks.encodeCombination native.witness127 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 127 [] := by kernel_rfl

theorem native.idealInputsBinding127 :
    CleanExpression.inputs native.expression127 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 127 [] := by kernel_rfl

theorem native.checked127 :
    equal (CleanExpression.polynomial native.placement native.expression127)
        (combination native.relations native.witness127) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression127 native.witness127
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    127 (by decide +kernel) native.idealCodeBinding127 native.idealRelationsBinding native.idealWitnessBinding127

theorem native.preserved127 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression127).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression127 native.placement native.relations native.witness127
    native.checked127 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression128 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨55⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨57⟩))))
    (Airbender.Expression.var ⟨67⟩)

noncomputable def native.witness128 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨160, by decide⟩)]

theorem native.idealCodeBinding128 :
    CleanIdealChecks.encode native.placement native.expression128 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 128 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding128 :
    NumericPolynomialChecks.encodeCombination native.witness128 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 128 [] := by kernel_rfl

theorem native.idealInputsBinding128 :
    CleanExpression.inputs native.expression128 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 128 [] := by kernel_rfl

theorem native.checked128 :
    equal (CleanExpression.polynomial native.placement native.expression128)
        (combination native.relations native.witness128) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression128 native.witness128
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    128 (by decide +kernel) native.idealCodeBinding128 native.idealRelationsBinding native.idealWitnessBinding128

theorem native.preserved128 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression128).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression128 native.placement native.relations native.witness128
    native.checked128 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression129 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨56⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨58⟩))))
    (Airbender.Expression.var ⟨67⟩)

noncomputable def native.witness129 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨161, by decide⟩)]

theorem native.idealCodeBinding129 :
    CleanIdealChecks.encode native.placement native.expression129 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 129 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding129 :
    NumericPolynomialChecks.encodeCombination native.witness129 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 129 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
