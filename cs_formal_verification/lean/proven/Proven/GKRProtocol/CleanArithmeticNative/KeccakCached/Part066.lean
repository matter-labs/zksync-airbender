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

local instance generatedBatch66Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch66Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression181 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨248⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨248⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness181 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨213, by decide⟩)]

theorem native.idealCodeBinding181 :
    CleanIdealChecks.encode native.placement native.expression181 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 181 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding181 :
    NumericPolynomialChecks.encodeCombination native.witness181 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 181 [] := by kernel_rfl

theorem native.idealInputsBinding181 :
    CleanExpression.inputs native.expression181 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 181 [] := by kernel_rfl

theorem native.checked181 :
    equal (CleanExpression.polynomial native.placement native.expression181)
        (combination native.relations native.witness181) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression181 native.witness181
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    181 (by decide +kernel) native.idealCodeBinding181 native.idealRelationsBinding native.idealWitnessBinding181

theorem native.preserved181 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression181).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression181 native.placement native.relations native.witness181
    native.checked181 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression182 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨251⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨251⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness182 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨214, by decide⟩)]

theorem native.idealCodeBinding182 :
    CleanIdealChecks.encode native.placement native.expression182 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 182 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding182 :
    NumericPolynomialChecks.encodeCombination native.witness182 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 182 [] := by kernel_rfl

theorem native.idealInputsBinding182 :
    CleanExpression.inputs native.expression182 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 182 [] := by kernel_rfl

theorem native.checked182 :
    equal (CleanExpression.polynomial native.placement native.expression182)
        (combination native.relations native.witness182) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression182 native.witness182
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    182 (by decide +kernel) native.idealCodeBinding182 native.idealRelationsBinding native.idealWitnessBinding182

theorem native.preserved182 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression182).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression182 native.placement native.relations native.witness182
    native.checked182 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression183 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨254⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨254⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness183 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨215, by decide⟩)]

theorem native.idealCodeBinding183 :
    CleanIdealChecks.encode native.placement native.expression183 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 183 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding183 :
    NumericPolynomialChecks.encodeCombination native.witness183 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 183 [] := by kernel_rfl

theorem native.idealInputsBinding183 :
    CleanExpression.inputs native.expression183 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 183 [] := by kernel_rfl

theorem native.checked183 :
    equal (CleanExpression.polynomial native.placement native.expression183)
        (combination native.relations native.witness183) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression183 native.witness183
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    183 (by decide +kernel) native.idealCodeBinding183 native.idealRelationsBinding native.idealWitnessBinding183

theorem native.preserved183 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression183).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression183 native.placement native.relations native.witness183
    native.checked183 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression184 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨257⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨257⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness184 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨216, by decide⟩)]

theorem native.idealCodeBinding184 :
    CleanIdealChecks.encode native.placement native.expression184 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 184 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
