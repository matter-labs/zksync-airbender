module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part061
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

local instance generatedBatch62Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch62Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding167 :
    CleanIdealChecks.encode native.placement native.expression167 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 167 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding167 :
    NumericPolynomialChecks.encodeCombination native.witness167 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 167 [] := by kernel_rfl

theorem native.idealInputsBinding167 :
    CleanExpression.inputs native.expression167 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 167 [] := by kernel_rfl

theorem native.checked167 :
    equal (CleanExpression.polynomial native.placement native.expression167)
        (combination native.relations native.witness167) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression167 native.witness167
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    167 (by decide +kernel) native.idealCodeBinding167 native.idealRelationsBinding native.idealWitnessBinding167

theorem native.preserved167 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression167).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression167 native.placement native.relations native.witness167
    native.checked167 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression168 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨75⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨75⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness168 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨200, by decide⟩)]

theorem native.idealCodeBinding168 :
    CleanIdealChecks.encode native.placement native.expression168 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 168 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding168 :
    NumericPolynomialChecks.encodeCombination native.witness168 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 168 [] := by kernel_rfl

theorem native.idealInputsBinding168 :
    CleanExpression.inputs native.expression168 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 168 [] := by kernel_rfl

theorem native.checked168 :
    equal (CleanExpression.polynomial native.placement native.expression168)
        (combination native.relations native.witness168) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression168 native.witness168
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    168 (by decide +kernel) native.idealCodeBinding168 native.idealRelationsBinding native.idealWitnessBinding168

theorem native.preserved168 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression168).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression168 native.placement native.relations native.witness168
    native.checked168 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression169 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨76⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨76⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness169 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨201, by decide⟩)]

theorem native.idealCodeBinding169 :
    CleanIdealChecks.encode native.placement native.expression169 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 169 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding169 :
    NumericPolynomialChecks.encodeCombination native.witness169 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 169 [] := by kernel_rfl

theorem native.idealInputsBinding169 :
    CleanExpression.inputs native.expression169 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 169 [] := by kernel_rfl

theorem native.checked169 :
    equal (CleanExpression.polynomial native.placement native.expression169)
        (combination native.relations native.witness169) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression169 native.witness169
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    169 (by decide +kernel) native.idealCodeBinding169 native.idealRelationsBinding native.idealWitnessBinding169

theorem native.preserved169 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression169).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression169 native.placement native.relations native.witness169
    native.checked169 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression170 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨77⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨77⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness170 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨202, by decide⟩)]

theorem native.idealCodeBinding170 :
    CleanIdealChecks.encode native.placement native.expression170 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 170 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding170 :
    NumericPolynomialChecks.encodeCombination native.witness170 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 170 [] := by kernel_rfl

theorem native.idealInputsBinding170 :
    CleanExpression.inputs native.expression170 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 170 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
