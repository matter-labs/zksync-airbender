module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part040
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

local instance generatedBatch41Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch41Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding23 :
    CleanIdealChecks.encode native.placement native.expression23 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 23 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding23 :
    NumericPolynomialChecks.encodeCombination native.witness23 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 23 [] := by kernel_rfl

theorem native.idealInputsBinding23 :
    CleanExpression.inputs native.expression23 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 23 [] := by kernel_rfl

theorem native.checked23 :
    equal (CleanExpression.polynomial native.placement native.expression23)
        (combination native.relations native.witness23) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression23 native.witness23
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 23 (by decide +kernel) native.idealCodeBinding23
    native.idealRelationsBinding native.idealWitnessBinding23

theorem native.preserved23 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression23).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression23 native.placement native.relations native.witness23
    native.checked23 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression24 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 26764) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨25⟩)))))
      (Airbender.Expression.var ⟨25⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨174⟩))

noncomputable def native.witness24 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨114, by decide⟩)]

theorem native.idealCodeBinding24 :
    CleanIdealChecks.encode native.placement native.expression24 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 24 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding24 :
    NumericPolynomialChecks.encodeCombination native.witness24 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 24 [] := by kernel_rfl

theorem native.idealInputsBinding24 :
    CleanExpression.inputs native.expression24 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 24 [] := by kernel_rfl

theorem native.checked24 :
    equal (CleanExpression.polynomial native.placement native.expression24)
        (combination native.relations native.witness24) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression24 native.witness24
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 24 (by decide +kernel) native.idealCodeBinding24
    native.idealRelationsBinding native.idealWitnessBinding24

theorem native.preserved24 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression24).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression24 native.placement native.relations native.witness24
    native.checked24 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression25 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨174⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨57⟩)))))
      (Airbender.Expression.var ⟨57⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨175⟩))

noncomputable def native.witness25 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨115, by decide⟩)]

theorem native.idealCodeBinding25 :
    CleanIdealChecks.encode native.placement native.expression25 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 25 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding25 :
    NumericPolynomialChecks.encodeCombination native.witness25 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 25 [] := by kernel_rfl

theorem native.idealInputsBinding25 :
    CleanExpression.inputs native.expression25 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 25 [] := by kernel_rfl

theorem native.checked25 :
    equal (CleanExpression.polynomial native.placement native.expression25)
        (combination native.relations native.witness25) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression25 native.witness25
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 25 (by decide +kernel) native.idealCodeBinding25
    native.idealRelationsBinding native.idealWitnessBinding25

theorem native.preserved25 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression25).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression25 native.placement native.relations native.witness25
    native.checked25 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression26 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 39685) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨26⟩)))))
      (Airbender.Expression.var ⟨26⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨176⟩))

noncomputable def native.witness26 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨116, by decide⟩)]

theorem native.idealCodeBinding26 :
    CleanIdealChecks.encode native.placement native.expression26 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 26 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding26 :
    NumericPolynomialChecks.encodeCombination native.witness26 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 26 [] := by kernel_rfl

theorem native.idealInputsBinding26 :
    CleanExpression.inputs native.expression26 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 26 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
