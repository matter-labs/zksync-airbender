module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part110
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

local instance generatedBatch111Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch111Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked190 :
    equal (CleanExpression.polynomial native.placement native.expression190)
        (combination native.relations native.witness190) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression190 native.witness190
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 190 (by decide +kernel) native.idealCodeBinding190
    native.idealRelationsBinding native.idealWitnessBinding190

theorem native.preserved190 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression190).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression190 native.placement native.relations native.witness190
    native.checked190 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression191 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨676⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨676⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness191 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨281, by decide⟩)]

theorem native.idealCodeBinding191 :
    CleanIdealChecks.encode native.placement native.expression191 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 191 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding191 :
    NumericPolynomialChecks.encodeCombination native.witness191 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 191 [] := by kernel_rfl

theorem native.idealInputsBinding191 :
    CleanExpression.inputs native.expression191 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 191 [] := by kernel_rfl

theorem native.checked191 :
    equal (CleanExpression.polynomial native.placement native.expression191)
        (combination native.relations native.witness191) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression191 native.witness191
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 191 (by decide +kernel) native.idealCodeBinding191
    native.idealRelationsBinding native.idealWitnessBinding191

theorem native.preserved191 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression191).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression191 native.placement native.relations native.witness191
    native.checked191 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression192 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨679⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨679⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness192 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨282, by decide⟩)]

theorem native.idealCodeBinding192 :
    CleanIdealChecks.encode native.placement native.expression192 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 192 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding192 :
    NumericPolynomialChecks.encodeCombination native.witness192 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 192 [] := by kernel_rfl

theorem native.idealInputsBinding192 :
    CleanExpression.inputs native.expression192 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 192 [] := by kernel_rfl

theorem native.checked192 :
    equal (CleanExpression.polynomial native.placement native.expression192)
        (combination native.relations native.witness192) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression192 native.witness192
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 192 (by decide +kernel) native.idealCodeBinding192
    native.idealRelationsBinding native.idealWitnessBinding192

theorem native.preserved192 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression192).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression192 native.placement native.relations native.witness192
    native.checked192 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression193 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨682⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨682⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness193 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨283, by decide⟩)]

theorem native.idealCodeBinding193 :
    CleanIdealChecks.encode native.placement native.expression193 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 193 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding193 :
    NumericPolynomialChecks.encodeCombination native.witness193 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 193 [] := by kernel_rfl

theorem native.idealInputsBinding193 :
    CleanExpression.inputs native.expression193 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 193 [] := by kernel_rfl

theorem native.checked193 :
    equal (CleanExpression.polynomial native.placement native.expression193)
        (combination native.relations native.witness193) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression193 native.witness193
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 193 (by decide +kernel) native.idealCodeBinding193
    native.idealRelationsBinding native.idealWitnessBinding193

theorem native.preserved193 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression193).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression193 native.placement native.relations native.witness193
    native.checked193 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression194 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨685⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨685⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
