module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part047
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

local instance generatedBatch48Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch48Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding47 :
    CleanIdealChecks.encode native.placement native.expression47 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 47 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding47 :
    NumericPolynomialChecks.encodeCombination native.witness47 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 47 [] := by kernel_rfl

theorem native.idealInputsBinding47 :
    CleanExpression.inputs native.expression47 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 47 [] := by kernel_rfl

theorem native.checked47 :
    equal (CleanExpression.polynomial native.placement native.expression47)
        (combination native.relations native.witness47) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression47 native.witness47
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 47 (by decide +kernel) native.idealCodeBinding47
    native.idealRelationsBinding native.idealWitnessBinding47

theorem native.preserved47 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression47).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression47 native.placement native.relations native.witness47
    native.checked47 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression48 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                  (Airbender.Expression.var ⟨142⟩))))
            (Airbender.Expression.var ⟨85⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨153⟩))
          (Airbender.Expression.var ⟨85⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.var ⟨141⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 21055) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨198⟩))

noncomputable def native.witness48 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨138, by decide⟩)]

theorem native.idealCodeBinding48 :
    CleanIdealChecks.encode native.placement native.expression48 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 48 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding48 :
    NumericPolynomialChecks.encodeCombination native.witness48 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 48 [] := by kernel_rfl

theorem native.idealInputsBinding48 :
    CleanExpression.inputs native.expression48 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 48 [] := by kernel_rfl

theorem native.checked48 :
    equal (CleanExpression.polynomial native.placement native.expression48)
        (combination native.relations native.witness48) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression48 native.witness48
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 48 (by decide +kernel) native.idealCodeBinding48
    native.idealRelationsBinding native.idealWitnessBinding48

theorem native.preserved48 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression48).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression48 native.placement native.relations native.witness48
    native.checked48 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression49 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                  (Airbender.Expression.var ⟨142⟩))))
            (Airbender.Expression.var ⟨86⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨153⟩))
          (Airbender.Expression.var ⟨86⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.var ⟨141⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 20750) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨199⟩))

noncomputable def native.witness49 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨139, by decide⟩)]

theorem native.idealCodeBinding49 :
    CleanIdealChecks.encode native.placement native.expression49 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 49 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding49 :
    NumericPolynomialChecks.encodeCombination native.witness49 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 49 [] := by kernel_rfl

theorem native.idealInputsBinding49 :
    CleanExpression.inputs native.expression49 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 49 [] := by kernel_rfl

theorem native.checked49 :
    equal (CleanExpression.polynomial native.placement native.expression49)
        (combination native.relations native.witness49) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression49 native.witness49
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 49 (by decide +kernel) native.idealCodeBinding49
    native.idealRelationsBinding native.idealWitnessBinding49

theorem native.preserved49 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression49).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression49 native.placement native.relations native.witness49
    native.checked49 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression50 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                  (Airbender.Expression.var ⟨142⟩))))
            (Airbender.Expression.var ⟨93⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨153⟩))
          (Airbender.Expression.var ⟨93⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.var ⟨141⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 9812) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨200⟩))

noncomputable def native.witness50 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨140, by decide⟩)]

theorem native.idealCodeBinding50 :
    CleanIdealChecks.encode native.placement native.expression50 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 50 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding50 :
    NumericPolynomialChecks.encodeCombination native.witness50 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 50 [] := by kernel_rfl

theorem native.idealInputsBinding50 :
    CleanExpression.inputs native.expression50 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 50 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
