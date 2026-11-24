module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part046
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

local instance generatedBatch47Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch47Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved115 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression115).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression115 native.placement native.relations native.witness115
    native.checked115 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression116 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨31⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨33⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness116 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨148, by decide⟩)]

theorem native.idealCodeBinding116 :
    CleanIdealChecks.encode native.placement native.expression116 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 116 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding116 :
    NumericPolynomialChecks.encodeCombination native.witness116 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 116 [] := by kernel_rfl

theorem native.idealInputsBinding116 :
    CleanExpression.inputs native.expression116 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 116 [] := by kernel_rfl

theorem native.checked116 :
    equal (CleanExpression.polynomial native.placement native.expression116)
        (combination native.relations native.witness116) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression116 native.witness116
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    116 (by decide +kernel) native.idealCodeBinding116 native.idealRelationsBinding native.idealWitnessBinding116

theorem native.preserved116 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression116).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression116 native.placement native.relations native.witness116
    native.checked116 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression117 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨32⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨34⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness117 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨149, by decide⟩)]

theorem native.idealCodeBinding117 :
    CleanIdealChecks.encode native.placement native.expression117 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 117 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding117 :
    NumericPolynomialChecks.encodeCombination native.witness117 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 117 [] := by kernel_rfl

theorem native.idealInputsBinding117 :
    CleanExpression.inputs native.expression117 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 117 [] := by kernel_rfl

theorem native.checked117 :
    equal (CleanExpression.polynomial native.placement native.expression117)
        (combination native.relations native.witness117) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression117 native.witness117
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    117 (by decide +kernel) native.idealCodeBinding117 native.idealRelationsBinding native.idealWitnessBinding117

theorem native.preserved117 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression117).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression117 native.placement native.relations native.witness117
    native.checked117 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression118 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨35⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨37⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness118 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨150, by decide⟩)]

theorem native.idealCodeBinding118 :
    CleanIdealChecks.encode native.placement native.expression118 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 118 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding118 :
    NumericPolynomialChecks.encodeCombination native.witness118 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 118 [] := by kernel_rfl

theorem native.idealInputsBinding118 :
    CleanExpression.inputs native.expression118 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 118 [] := by kernel_rfl

theorem native.checked118 :
    equal (CleanExpression.polynomial native.placement native.expression118)
        (combination native.relations native.witness118) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression118 native.witness118
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    118 (by decide +kernel) native.idealCodeBinding118 native.idealRelationsBinding native.idealWitnessBinding118

theorem native.preserved118 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression118).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression118 native.placement native.relations native.witness118
    native.checked118 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression119 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨36⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨38⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness119 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨151, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
