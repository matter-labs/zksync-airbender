module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
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

local instance generatedBatch38Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch38Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression13 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨162⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨45⟩)))))
      (Airbender.Expression.var ⟨45⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨163⟩))

noncomputable def native.witness13 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨103, by decide⟩)]

theorem native.idealCodeBinding13 :
    CleanIdealChecks.encode native.placement native.expression13 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 13 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding13 :
    NumericPolynomialChecks.encodeCombination native.witness13 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 13 [] := by kernel_rfl

theorem native.idealInputsBinding13 :
    CleanExpression.inputs native.expression13 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 13 [] := by kernel_rfl

theorem native.checked13 :
    equal (CleanExpression.polynomial native.placement native.expression13)
        (combination native.relations native.witness13) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression13 native.witness13
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 13 (by decide +kernel) native.idealCodeBinding13
    native.idealRelationsBinding native.idealWitnessBinding13

theorem native.preserved13 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression13).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression13 native.placement native.relations native.witness13
    native.checked13 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression14 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 15470) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨14⟩)))))
      (Airbender.Expression.var ⟨14⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨164⟩))

noncomputable def native.witness14 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨104, by decide⟩)]

theorem native.idealCodeBinding14 :
    CleanIdealChecks.encode native.placement native.expression14 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 14 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding14 :
    NumericPolynomialChecks.encodeCombination native.witness14 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 14 [] := by kernel_rfl

theorem native.idealInputsBinding14 :
    CleanExpression.inputs native.expression14 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 14 [] := by kernel_rfl

theorem native.checked14 :
    equal (CleanExpression.polynomial native.placement native.expression14)
        (combination native.relations native.witness14) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression14 native.witness14
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 14 (by decide +kernel) native.idealCodeBinding14
    native.idealRelationsBinding native.idealWitnessBinding14

theorem native.preserved14 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression14).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression14 native.placement native.relations native.witness14
    native.checked14 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression15 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨164⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨46⟩)))))
      (Airbender.Expression.var ⟨46⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨165⟩))

noncomputable def native.witness15 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨105, by decide⟩)]

theorem native.idealCodeBinding15 :
    CleanIdealChecks.encode native.placement native.expression15 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 15 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding15 :
    NumericPolynomialChecks.encodeCombination native.witness15 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 15 [] := by kernel_rfl

theorem native.idealInputsBinding15 :
    CleanExpression.inputs native.expression15 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 15 [] := by kernel_rfl

theorem native.checked15 :
    equal (CleanExpression.polynomial native.placement native.expression15)
        (combination native.relations native.witness15) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression15 native.witness15
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 15 (by decide +kernel) native.idealCodeBinding15
    native.idealRelationsBinding native.idealWitnessBinding15

theorem native.preserved15 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression15).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression15 native.placement native.relations native.witness15
    native.checked15 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression16 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 62778) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨17⟩)))))
      (Airbender.Expression.var ⟨17⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨166⟩))

noncomputable def native.witness16 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨106, by decide⟩)]

theorem native.idealCodeBinding16 :
    CleanIdealChecks.encode native.placement native.expression16 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 16 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
