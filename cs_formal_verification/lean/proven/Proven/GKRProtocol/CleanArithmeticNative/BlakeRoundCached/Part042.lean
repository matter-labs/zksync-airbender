module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part041
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

local instance generatedBatch42Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch42Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked26 :
    equal (CleanExpression.polynomial native.placement native.expression26)
        (combination native.relations native.witness26) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression26 native.witness26
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 26 (by decide +kernel) native.idealCodeBinding26
    native.idealRelationsBinding native.idealWitnessBinding26

theorem native.preserved26 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression26).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression26 native.placement native.relations native.witness26
    native.checked26 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression27 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨176⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨58⟩)))))
      (Airbender.Expression.var ⟨58⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨177⟩))

noncomputable def native.witness27 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨117, by decide⟩)]

theorem native.idealCodeBinding27 :
    CleanIdealChecks.encode native.placement native.expression27 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 27 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding27 :
    NumericPolynomialChecks.encodeCombination native.witness27 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 27 [] := by kernel_rfl

theorem native.idealInputsBinding27 :
    CleanExpression.inputs native.expression27 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 27 [] := by kernel_rfl

theorem native.checked27 :
    equal (CleanExpression.polynomial native.placement native.expression27)
        (combination native.relations native.witness27) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression27 native.witness27
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 27 (by decide +kernel) native.idealCodeBinding27
    native.idealRelationsBinding native.idealWitnessBinding27

theorem native.preserved27 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression27).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression27 native.placement native.relations native.witness27
    native.checked27 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression28 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 55723) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨29⟩)))))
      (Airbender.Expression.var ⟨29⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨178⟩))

noncomputable def native.witness28 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨118, by decide⟩)]

theorem native.idealCodeBinding28 :
    CleanIdealChecks.encode native.placement native.expression28 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 28 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding28 :
    NumericPolynomialChecks.encodeCombination native.witness28 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 28 [] := by kernel_rfl

theorem native.idealInputsBinding28 :
    CleanExpression.inputs native.expression28 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 28 [] := by kernel_rfl

theorem native.checked28 :
    equal (CleanExpression.polynomial native.placement native.expression28)
        (combination native.relations native.witness28) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression28 native.witness28
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 28 (by decide +kernel) native.idealCodeBinding28
    native.idealRelationsBinding native.idealWitnessBinding28

theorem native.preserved28 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression28).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression28 native.placement native.relations native.witness28
    native.checked28 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression29 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨178⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨61⟩)))))
      (Airbender.Expression.var ⟨61⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨179⟩))

noncomputable def native.witness29 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨119, by decide⟩)]

theorem native.idealCodeBinding29 :
    CleanIdealChecks.encode native.placement native.expression29 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 29 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding29 :
    NumericPolynomialChecks.encodeCombination native.witness29 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 29 [] := by kernel_rfl

theorem native.idealInputsBinding29 :
    CleanExpression.inputs native.expression29 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 29 [] := by kernel_rfl

theorem native.checked29 :
    equal (CleanExpression.polynomial native.placement native.expression29)
        (combination native.relations native.witness29) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression29 native.witness29
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 29 (by decide +kernel) native.idealCodeBinding29
    native.idealRelationsBinding native.idealWitnessBinding29

theorem native.preserved29 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression29).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression29 native.placement native.relations native.witness29
    native.checked29 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression30 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 8067) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨30⟩)))))
      (Airbender.Expression.var ⟨30⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨180⟩))
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
