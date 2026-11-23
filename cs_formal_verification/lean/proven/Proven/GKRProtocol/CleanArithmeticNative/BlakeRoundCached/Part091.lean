module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part090
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BlakeRoundCached
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCached
public import Proven.GKRProtocol.CleanPlacementNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch91Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch91Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness122 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨212, by decide⟩)]

theorem native.idealCodeBinding122 :
    CleanIdealChecks.encode native.placement native.expression122 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 122 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding122 :
    NumericPolynomialChecks.encodeCombination native.witness122 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 122 [] := by kernel_rfl

theorem native.idealInputsBinding122 :
    CleanExpression.inputs native.expression122 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 122 [] := by kernel_rfl

theorem native.checked122 :
    equal (CleanExpression.polynomial native.placement native.expression122)
        (combination native.relations native.witness122) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression122 native.witness122
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 122 (by decide +kernel) native.idealCodeBinding122
    native.idealRelationsBinding native.idealWitnessBinding122

theorem native.preserved122 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression122).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression122 native.placement native.relations native.witness122
    native.checked122 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression123 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨630⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                (Airbender.Expression.var ⟨631⟩))))
          (Airbender.Expression.var ⟨152⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨152⟩))))
        (Airbender.Expression.var ⟨34⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨36⟩))

noncomputable def native.witness123 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨213, by decide⟩)]

theorem native.idealCodeBinding123 :
    CleanIdealChecks.encode native.placement native.expression123 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 123 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding123 :
    NumericPolynomialChecks.encodeCombination native.witness123 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 123 [] := by kernel_rfl

theorem native.idealInputsBinding123 :
    CleanExpression.inputs native.expression123 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 123 [] := by kernel_rfl

theorem native.checked123 :
    equal (CleanExpression.polynomial native.placement native.expression123)
        (combination native.relations native.witness123) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression123 native.witness123
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 123 (by decide +kernel) native.idealCodeBinding123
    native.idealRelationsBinding native.idealWitnessBinding123

theorem native.preserved123 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression123).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression123 native.placement native.relations native.witness123
    native.checked123 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression124 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨139⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨139⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness124 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨214, by decide⟩)]

theorem native.idealCodeBinding124 :
    CleanIdealChecks.encode native.placement native.expression124 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 124 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding124 :
    NumericPolynomialChecks.encodeCombination native.witness124 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 124 [] := by kernel_rfl

theorem native.idealInputsBinding124 :
    CleanExpression.inputs native.expression124 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 124 [] := by kernel_rfl

theorem native.checked124 :
    equal (CleanExpression.polynomial native.placement native.expression124)
        (combination native.relations native.witness124) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression124 native.witness124
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 124 (by decide +kernel) native.idealCodeBinding124
    native.idealRelationsBinding native.idealWitnessBinding124

theorem native.preserved124 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression124).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression124 native.placement native.relations native.witness124
    native.checked124 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression125 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨140⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨140⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness125 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨215, by decide⟩)]

theorem native.idealCodeBinding125 :
    CleanIdealChecks.encode native.placement native.expression125 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 125 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding125 :
    NumericPolynomialChecks.encodeCombination native.witness125 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 125 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
