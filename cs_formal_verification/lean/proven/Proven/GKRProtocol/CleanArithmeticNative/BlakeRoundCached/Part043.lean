module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part042
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

local instance generatedBatch43Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch43Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness30 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨120, by decide⟩)]

theorem native.idealCodeBinding30 :
    CleanIdealChecks.encode native.placement native.expression30 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 30 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding30 :
    NumericPolynomialChecks.encodeCombination native.witness30 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 30 [] := by kernel_rfl

theorem native.idealInputsBinding30 :
    CleanExpression.inputs native.expression30 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 30 [] := by kernel_rfl

theorem native.checked30 :
    equal (CleanExpression.polynomial native.placement native.expression30)
        (combination native.relations native.witness30) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression30 native.witness30
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 30 (by decide +kernel) native.idealCodeBinding30
    native.idealRelationsBinding native.idealWitnessBinding30

theorem native.preserved30 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression30).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression30 native.placement native.relations native.witness30
    native.checked30 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression31 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨180⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨62⟩)))))
      (Airbender.Expression.var ⟨62⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨181⟩))

noncomputable def native.witness31 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨121, by decide⟩)]

theorem native.idealCodeBinding31 :
    CleanIdealChecks.encode native.placement native.expression31 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 31 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding31 :
    NumericPolynomialChecks.encodeCombination native.witness31 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 31 [] := by kernel_rfl

theorem native.idealInputsBinding31 :
    CleanExpression.inputs native.expression31 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 31 [] := by kernel_rfl

theorem native.checked31 :
    equal (CleanExpression.polynomial native.placement native.expression31)
        (combination native.relations native.witness31) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression31 native.witness31
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 31 (by decide +kernel) native.idealCodeBinding31
    native.idealRelationsBinding native.idealWitnessBinding31

theorem native.preserved31 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression31).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression31 native.placement native.relations native.witness31
    native.checked31 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression32 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 52505) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨33⟩)))))
      (Airbender.Expression.var ⟨33⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨182⟩))

noncomputable def native.witness32 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨122, by decide⟩)]

theorem native.idealCodeBinding32 :
    CleanIdealChecks.encode native.placement native.expression32 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 32 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding32 :
    NumericPolynomialChecks.encodeCombination native.witness32 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 32 [] := by kernel_rfl

theorem native.idealInputsBinding32 :
    CleanExpression.inputs native.expression32 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 32 [] := by kernel_rfl

theorem native.checked32 :
    equal (CleanExpression.polynomial native.placement native.expression32)
        (combination native.relations native.witness32) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression32 native.witness32
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 32 (by decide +kernel) native.idealCodeBinding32
    native.idealRelationsBinding native.idealWitnessBinding32

theorem native.preserved32 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression32).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression32 native.placement native.relations native.witness32
    native.checked32 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression33 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨182⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨65⟩)))))
      (Airbender.Expression.var ⟨65⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨183⟩))

noncomputable def native.witness33 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨123, by decide⟩)]

theorem native.idealCodeBinding33 :
    CleanIdealChecks.encode native.placement native.expression33 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 33 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding33 :
    NumericPolynomialChecks.encodeCombination native.witness33 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 33 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
