module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part055
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

local instance generatedBatch56Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch56Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked146 :
    equal (CleanExpression.polynomial native.placement native.expression146)
        (combination native.relations native.witness146) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression146 native.witness146
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    146 (by decide +kernel) native.idealCodeBinding146 native.idealRelationsBinding native.idealWitnessBinding146

theorem native.preserved146 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression146).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression146 native.placement native.relations native.witness146
    native.checked146 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression147 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨44⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨46⟩))))
    (Airbender.Expression.var ⟨69⟩)

noncomputable def native.witness147 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨179, by decide⟩)]

theorem native.idealCodeBinding147 :
    CleanIdealChecks.encode native.placement native.expression147 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 147 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding147 :
    NumericPolynomialChecks.encodeCombination native.witness147 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 147 [] := by kernel_rfl

theorem native.idealInputsBinding147 :
    CleanExpression.inputs native.expression147 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 147 [] := by kernel_rfl

theorem native.checked147 :
    equal (CleanExpression.polynomial native.placement native.expression147)
        (combination native.relations native.witness147) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression147 native.witness147
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    147 (by decide +kernel) native.idealCodeBinding147 native.idealRelationsBinding native.idealWitnessBinding147

theorem native.preserved147 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression147).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression147 native.placement native.relations native.witness147
    native.checked147 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression148 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨47⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨49⟩))))
    (Airbender.Expression.var ⟨69⟩)

noncomputable def native.witness148 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨180, by decide⟩)]

theorem native.idealCodeBinding148 :
    CleanIdealChecks.encode native.placement native.expression148 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 148 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding148 :
    NumericPolynomialChecks.encodeCombination native.witness148 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 148 [] := by kernel_rfl

theorem native.idealInputsBinding148 :
    CleanExpression.inputs native.expression148 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 148 [] := by kernel_rfl

theorem native.checked148 :
    equal (CleanExpression.polynomial native.placement native.expression148)
        (combination native.relations native.witness148) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression148 native.witness148
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    148 (by decide +kernel) native.idealCodeBinding148 native.idealRelationsBinding native.idealWitnessBinding148

theorem native.preserved148 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression148).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression148 native.placement native.relations native.witness148
    native.checked148 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression149 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨48⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨50⟩))))
    (Airbender.Expression.var ⟨69⟩)

noncomputable def native.witness149 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨181, by decide⟩)]

theorem native.idealCodeBinding149 :
    CleanIdealChecks.encode native.placement native.expression149 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 149 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding149 :
    NumericPolynomialChecks.encodeCombination native.witness149 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 149 [] := by kernel_rfl

theorem native.idealInputsBinding149 :
    CleanExpression.inputs native.expression149 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 149 [] := by kernel_rfl

theorem native.checked149 :
    equal (CleanExpression.polynomial native.placement native.expression149)
        (combination native.relations native.witness149) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression149 native.witness149
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    149 (by decide +kernel) native.idealCodeBinding149 native.idealRelationsBinding native.idealWitnessBinding149

theorem native.preserved149 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression149).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression149 native.placement native.relations native.witness149
    native.checked149 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression150 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨51⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨53⟩))))
    (Airbender.Expression.var ⟨69⟩)
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
