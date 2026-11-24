module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part036
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

local instance generatedBatch37Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch37Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding9 :
    CleanExpression.inputs native.expression9 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 9 [] := by kernel_rfl

theorem native.checked9 :
    equal (CleanExpression.polynomial native.placement native.expression9)
        (combination native.relations native.witness9) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression9 native.witness9
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 9 (by decide +kernel) native.idealCodeBinding9
    native.idealRelationsBinding native.idealWitnessBinding9

theorem native.preserved9 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression9).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression9 native.placement native.relations native.witness9
    native.checked9 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression10 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 47975) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨10⟩)))))
      (Airbender.Expression.var ⟨10⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨160⟩))

noncomputable def native.witness10 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨100, by decide⟩)]

theorem native.idealCodeBinding10 :
    CleanIdealChecks.encode native.placement native.expression10 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 10 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding10 :
    NumericPolynomialChecks.encodeCombination native.witness10 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 10 [] := by kernel_rfl

theorem native.idealInputsBinding10 :
    CleanExpression.inputs native.expression10 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 10 [] := by kernel_rfl

theorem native.checked10 :
    equal (CleanExpression.polynomial native.placement native.expression10)
        (combination native.relations native.witness10) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression10 native.witness10
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 10 (by decide +kernel) native.idealCodeBinding10
    native.idealRelationsBinding native.idealWitnessBinding10

theorem native.preserved10 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression10).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression10 native.placement native.relations native.witness10
    native.checked10 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression11 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨160⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨42⟩)))))
      (Airbender.Expression.var ⟨42⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨161⟩))

noncomputable def native.witness11 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨101, by decide⟩)]

theorem native.idealCodeBinding11 :
    CleanIdealChecks.encode native.placement native.expression11 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 11 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding11 :
    NumericPolynomialChecks.encodeCombination native.witness11 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 11 [] := by kernel_rfl

theorem native.idealInputsBinding11 :
    CleanExpression.inputs native.expression11 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 11 [] := by kernel_rfl

theorem native.checked11 :
    equal (CleanExpression.polynomial native.placement native.expression11)
        (combination native.relations native.witness11) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression11 native.witness11
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 11 (by decide +kernel) native.idealCodeBinding11
    native.idealRelationsBinding native.idealWitnessBinding11

theorem native.preserved11 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression11).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression11 native.placement native.relations native.witness11
    native.checked11 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression12 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 62322) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨13⟩)))))
      (Airbender.Expression.var ⟨13⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨162⟩))

noncomputable def native.witness12 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨102, by decide⟩)]

theorem native.idealCodeBinding12 :
    CleanIdealChecks.encode native.placement native.expression12 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 12 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding12 :
    NumericPolynomialChecks.encodeCombination native.witness12 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 12 [] := by kernel_rfl

theorem native.idealInputsBinding12 :
    CleanExpression.inputs native.expression12 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 12 [] := by kernel_rfl

theorem native.checked12 :
    equal (CleanExpression.polynomial native.placement native.expression12)
        (combination native.relations native.witness12) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression12 native.witness12
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 12 (by decide +kernel) native.idealCodeBinding12
    native.idealRelationsBinding native.idealWitnessBinding12

theorem native.preserved12 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression12).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression12 native.placement native.relations native.witness12
    native.checked12 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
