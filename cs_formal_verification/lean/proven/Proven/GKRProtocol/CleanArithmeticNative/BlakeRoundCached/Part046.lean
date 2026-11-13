module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part045
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

local instance generatedBatch46Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch46Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding40 :
    NumericPolynomialChecks.encodeCombination native.witness40 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 40 [] := by kernel_rfl

theorem native.idealInputsBinding40 :
    CleanExpression.inputs native.expression40 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 40 [] := by kernel_rfl

theorem native.checked40 :
    equal (CleanExpression.polynomial native.placement native.expression40)
        (combination native.relations native.witness40) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression40 native.witness40
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 40 (by decide +kernel) native.idealCodeBinding40
    native.idealRelationsBinding native.idealWitnessBinding40

theorem native.preserved40 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression40).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression40 native.placement native.relations native.witness40
    native.checked40 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression41 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                (Airbender.Expression.var ⟨142⟩))))
          (Airbender.Expression.var ⟨78⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 15470) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨191⟩))

noncomputable def native.witness41 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨131, by decide⟩)]

theorem native.idealCodeBinding41 :
    CleanIdealChecks.encode native.placement native.expression41 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 41 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding41 :
    NumericPolynomialChecks.encodeCombination native.witness41 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 41 [] := by kernel_rfl

theorem native.idealInputsBinding41 :
    CleanExpression.inputs native.expression41 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 41 [] := by kernel_rfl

theorem native.checked41 :
    equal (CleanExpression.polynomial native.placement native.expression41)
        (combination native.relations native.witness41) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression41 native.witness41
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 41 (by decide +kernel) native.idealCodeBinding41
    native.idealRelationsBinding native.idealWitnessBinding41

theorem native.preserved41 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression41).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression41 native.placement native.relations native.witness41
    native.checked41 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression42 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                (Airbender.Expression.var ⟨142⟩))))
          (Airbender.Expression.var ⟨81⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 62778) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨192⟩))

noncomputable def native.witness42 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨132, by decide⟩)]

theorem native.idealCodeBinding42 :
    CleanIdealChecks.encode native.placement native.expression42 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 42 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding42 :
    NumericPolynomialChecks.encodeCombination native.witness42 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 42 [] := by kernel_rfl

theorem native.idealInputsBinding42 :
    CleanExpression.inputs native.expression42 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 42 [] := by kernel_rfl

theorem native.checked42 :
    equal (CleanExpression.polynomial native.placement native.expression42)
        (combination native.relations native.witness42) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression42 native.witness42
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 42 (by decide +kernel) native.idealCodeBinding42
    native.idealRelationsBinding native.idealWitnessBinding42

theorem native.preserved42 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression42).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression42 native.placement native.relations native.witness42
    native.checked42 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression43 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                (Airbender.Expression.var ⟨142⟩))))
          (Airbender.Expression.var ⟨82⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 42319) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨193⟩))

noncomputable def native.witness43 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨133, by decide⟩)]

theorem native.idealCodeBinding43 :
    CleanIdealChecks.encode native.placement native.expression43 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 43 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding43 :
    NumericPolynomialChecks.encodeCombination native.witness43 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 43 [] := by kernel_rfl

theorem native.idealInputsBinding43 :
    CleanExpression.inputs native.expression43 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 43 [] := by kernel_rfl

theorem native.checked43 :
    equal (CleanExpression.polynomial native.placement native.expression43)
        (combination native.relations native.witness43) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression43 native.witness43
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 43 (by decide +kernel) native.idealCodeBinding43
    native.idealRelationsBinding native.idealWitnessBinding43
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
