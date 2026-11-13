module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part039
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

local instance generatedBatch40Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch40Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved19 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression19).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression19 native.placement native.relations native.witness19
    native.checked19 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression20 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 21119) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨21⟩)))))
      (Airbender.Expression.var ⟨21⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨170⟩))

noncomputable def native.witness20 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨110, by decide⟩)]

theorem native.idealCodeBinding20 :
    CleanIdealChecks.encode native.placement native.expression20 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 20 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding20 :
    NumericPolynomialChecks.encodeCombination native.witness20 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 20 [] := by kernel_rfl

theorem native.idealInputsBinding20 :
    CleanExpression.inputs native.expression20 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 20 [] := by kernel_rfl

theorem native.checked20 :
    equal (CleanExpression.polynomial native.placement native.expression20)
        (combination native.relations native.witness20) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression20 native.witness20
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 20 (by decide +kernel) native.idealCodeBinding20
    native.idealRelationsBinding native.idealWitnessBinding20

theorem native.preserved20 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression20).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression20 native.placement native.relations native.witness20
    native.checked20 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression21 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨170⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨53⟩)))))
      (Airbender.Expression.var ⟨53⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨171⟩))

noncomputable def native.witness21 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨111, by decide⟩)]

theorem native.idealCodeBinding21 :
    CleanIdealChecks.encode native.placement native.expression21 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 21 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding21 :
    NumericPolynomialChecks.encodeCombination native.witness21 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 21 [] := by kernel_rfl

theorem native.idealInputsBinding21 :
    CleanExpression.inputs native.expression21 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 21 [] := by kernel_rfl

theorem native.checked21 :
    equal (CleanExpression.polynomial native.placement native.expression21)
        (combination native.relations native.witness21) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression21 native.witness21
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 21 (by decide +kernel) native.idealCodeBinding21
    native.idealRelationsBinding native.idealWitnessBinding21

theorem native.preserved21 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression21).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression21 native.placement native.relations native.witness21
    native.checked21 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression22 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 20750) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨22⟩)))))
      (Airbender.Expression.var ⟨22⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨172⟩))

noncomputable def native.witness22 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨112, by decide⟩)]

theorem native.idealCodeBinding22 :
    CleanIdealChecks.encode native.placement native.expression22 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 22 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding22 :
    NumericPolynomialChecks.encodeCombination native.witness22 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 22 [] := by kernel_rfl

theorem native.idealInputsBinding22 :
    CleanExpression.inputs native.expression22 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 22 [] := by kernel_rfl

theorem native.checked22 :
    equal (CleanExpression.polynomial native.placement native.expression22)
        (combination native.relations native.witness22) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression22 native.witness22
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 22 (by decide +kernel) native.idealCodeBinding22
    native.idealRelationsBinding native.idealWitnessBinding22

theorem native.preserved22 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression22).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression22 native.placement native.relations native.witness22
    native.checked22 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression23 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨172⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨54⟩)))))
      (Airbender.Expression.var ⟨54⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨173⟩))

noncomputable def native.witness23 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨113, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
