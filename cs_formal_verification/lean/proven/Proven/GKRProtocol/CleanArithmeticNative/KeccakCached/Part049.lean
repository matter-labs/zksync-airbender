module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part048
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

local instance generatedBatch49Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch49Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked122 :
    equal (CleanExpression.polynomial native.placement native.expression122)
        (combination native.relations native.witness122) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression122 native.witness122
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    122 (by decide +kernel) native.idealCodeBinding122 native.idealRelationsBinding native.idealWitnessBinding122

theorem native.preserved122 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression122).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression122 native.placement native.relations native.witness122
    native.checked122 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression123 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨60⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨62⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness123 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨155, by decide⟩)]

theorem native.idealCodeBinding123 :
    CleanIdealChecks.encode native.placement native.expression123 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 123 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding123 :
    NumericPolynomialChecks.encodeCombination native.witness123 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 123 [] := by kernel_rfl

theorem native.idealInputsBinding123 :
    CleanExpression.inputs native.expression123 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 123 [] := by kernel_rfl

theorem native.checked123 :
    equal (CleanExpression.polynomial native.placement native.expression123)
        (combination native.relations native.witness123) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression123 native.witness123
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    123 (by decide +kernel) native.idealCodeBinding123 native.idealRelationsBinding native.idealWitnessBinding123

theorem native.preserved123 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression123).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression123 native.placement native.relations native.witness123
    native.checked123 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression124 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨55⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨57⟩))))
    (Airbender.Expression.var ⟨66⟩)

noncomputable def native.witness124 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨156, by decide⟩)]

theorem native.idealCodeBinding124 :
    CleanIdealChecks.encode native.placement native.expression124 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 124 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding124 :
    NumericPolynomialChecks.encodeCombination native.witness124 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 124 [] := by kernel_rfl

theorem native.idealInputsBinding124 :
    CleanExpression.inputs native.expression124 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 124 [] := by kernel_rfl

theorem native.checked124 :
    equal (CleanExpression.polynomial native.placement native.expression124)
        (combination native.relations native.witness124) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression124 native.witness124
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    124 (by decide +kernel) native.idealCodeBinding124 native.idealRelationsBinding native.idealWitnessBinding124

theorem native.preserved124 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression124).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression124 native.placement native.relations native.witness124
    native.checked124 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression125 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨56⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨58⟩))))
    (Airbender.Expression.var ⟨66⟩)

noncomputable def native.witness125 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨157, by decide⟩)]

theorem native.idealCodeBinding125 :
    CleanIdealChecks.encode native.placement native.expression125 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 125 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding125 :
    NumericPolynomialChecks.encodeCombination native.witness125 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 125 [] := by kernel_rfl

theorem native.idealInputsBinding125 :
    CleanExpression.inputs native.expression125 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 125 [] := by kernel_rfl

theorem native.checked125 :
    equal (CleanExpression.polynomial native.placement native.expression125)
        (combination native.relations native.witness125) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression125 native.witness125
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    125 (by decide +kernel) native.idealCodeBinding125 native.idealRelationsBinding native.idealWitnessBinding125

theorem native.preserved125 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression125).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression125 native.placement native.relations native.witness125
    native.checked125 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression126 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨59⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨61⟩))))
    (Airbender.Expression.var ⟨66⟩)
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
