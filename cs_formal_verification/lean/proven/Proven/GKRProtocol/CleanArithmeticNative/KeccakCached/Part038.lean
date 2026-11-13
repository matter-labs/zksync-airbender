module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
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

local instance generatedBatch38Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch38Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression85 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨24⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨26⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness85 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨117, by decide⟩)]

theorem native.idealCodeBinding85 :
    CleanIdealChecks.encode native.placement native.expression85 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 85 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding85 :
    NumericPolynomialChecks.encodeCombination native.witness85 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 85 [] := by kernel_rfl

theorem native.idealInputsBinding85 :
    CleanExpression.inputs native.expression85 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 85 [] := by kernel_rfl

theorem native.checked85 :
    equal (CleanExpression.polynomial native.placement native.expression85)
        (combination native.relations native.witness85) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression85 native.witness85
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 85
    (by decide +kernel) native.idealCodeBinding85 native.idealRelationsBinding native.idealWitnessBinding85

theorem native.preserved85 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression85).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression85 native.placement native.relations native.witness85
    native.checked85 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression86 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨27⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨29⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness86 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨118, by decide⟩)]

theorem native.idealCodeBinding86 :
    CleanIdealChecks.encode native.placement native.expression86 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 86 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding86 :
    NumericPolynomialChecks.encodeCombination native.witness86 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 86 [] := by kernel_rfl

theorem native.idealInputsBinding86 :
    CleanExpression.inputs native.expression86 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 86 [] := by kernel_rfl

theorem native.checked86 :
    equal (CleanExpression.polynomial native.placement native.expression86)
        (combination native.relations native.witness86) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression86 native.witness86
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 86
    (by decide +kernel) native.idealCodeBinding86 native.idealRelationsBinding native.idealWitnessBinding86

theorem native.preserved86 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression86).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression86 native.placement native.relations native.witness86
    native.checked86 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression87 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨28⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨30⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness87 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨119, by decide⟩)]

theorem native.idealCodeBinding87 :
    CleanIdealChecks.encode native.placement native.expression87 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 87 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding87 :
    NumericPolynomialChecks.encodeCombination native.witness87 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 87 [] := by kernel_rfl

theorem native.idealInputsBinding87 :
    CleanExpression.inputs native.expression87 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 87 [] := by kernel_rfl

theorem native.checked87 :
    equal (CleanExpression.polynomial native.placement native.expression87)
        (combination native.relations native.witness87) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression87 native.witness87
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 87
    (by decide +kernel) native.idealCodeBinding87 native.idealRelationsBinding native.idealWitnessBinding87

theorem native.preserved87 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression87).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression87 native.placement native.relations native.witness87
    native.checked87 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression88 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨31⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨33⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness88 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨120, by decide⟩)]

theorem native.idealCodeBinding88 :
    CleanIdealChecks.encode native.placement native.expression88 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 88 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
