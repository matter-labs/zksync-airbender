module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part062
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

local instance generatedBatch63Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch63Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked170 :
    equal (CleanExpression.polynomial native.placement native.expression170)
        (combination native.relations native.witness170) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression170 native.witness170
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    170 (by decide +kernel) native.idealCodeBinding170 native.idealRelationsBinding native.idealWitnessBinding170

theorem native.preserved170 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression170).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression170 native.placement native.relations native.witness170
    native.checked170 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression171 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨78⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨78⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness171 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨203, by decide⟩)]

theorem native.idealCodeBinding171 :
    CleanIdealChecks.encode native.placement native.expression171 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 171 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding171 :
    NumericPolynomialChecks.encodeCombination native.witness171 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 171 [] := by kernel_rfl

theorem native.idealInputsBinding171 :
    CleanExpression.inputs native.expression171 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 171 [] := by kernel_rfl

theorem native.checked171 :
    equal (CleanExpression.polynomial native.placement native.expression171)
        (combination native.relations native.witness171) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression171 native.witness171
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    171 (by decide +kernel) native.idealCodeBinding171 native.idealRelationsBinding native.idealWitnessBinding171

theorem native.preserved171 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression171).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression171 native.placement native.relations native.witness171
    native.checked171 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression172 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨79⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨79⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness172 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨204, by decide⟩)]

theorem native.idealCodeBinding172 :
    CleanIdealChecks.encode native.placement native.expression172 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 172 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding172 :
    NumericPolynomialChecks.encodeCombination native.witness172 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 172 [] := by kernel_rfl

theorem native.idealInputsBinding172 :
    CleanExpression.inputs native.expression172 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 172 [] := by kernel_rfl

theorem native.checked172 :
    equal (CleanExpression.polynomial native.placement native.expression172)
        (combination native.relations native.witness172) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression172 native.witness172
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    172 (by decide +kernel) native.idealCodeBinding172 native.idealRelationsBinding native.idealWitnessBinding172

theorem native.preserved172 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression172).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression172 native.placement native.relations native.witness172
    native.checked172 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression173 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨224⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨224⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness173 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨205, by decide⟩)]

theorem native.idealCodeBinding173 :
    CleanIdealChecks.encode native.placement native.expression173 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 173 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding173 :
    NumericPolynomialChecks.encodeCombination native.witness173 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 173 [] := by kernel_rfl

theorem native.idealInputsBinding173 :
    CleanExpression.inputs native.expression173 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 173 [] := by kernel_rfl

theorem native.checked173 :
    equal (CleanExpression.polynomial native.placement native.expression173)
        (combination native.relations native.witness173) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression173 native.witness173
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    173 (by decide +kernel) native.idealCodeBinding173 native.idealRelationsBinding native.idealWitnessBinding173

theorem native.preserved173 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression173).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression173 native.placement native.relations native.witness173
    native.checked173 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression174 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨227⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨227⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
