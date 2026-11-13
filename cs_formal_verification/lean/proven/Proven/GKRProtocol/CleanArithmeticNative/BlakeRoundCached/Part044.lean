module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part043
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

local instance generatedBatch44Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch44Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding33 :
    CleanExpression.inputs native.expression33 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 33 [] := by kernel_rfl

theorem native.checked33 :
    equal (CleanExpression.polynomial native.placement native.expression33)
        (combination native.relations native.witness33) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression33 native.witness33
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 33 (by decide +kernel) native.idealCodeBinding33
    native.idealRelationsBinding native.idealWitnessBinding33

theorem native.preserved33 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression33).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression33 native.placement native.relations native.witness33
    native.checked33 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression34 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 23520) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨34⟩)))))
      (Airbender.Expression.var ⟨34⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨184⟩))

noncomputable def native.witness34 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨124, by decide⟩)]

theorem native.idealCodeBinding34 :
    CleanIdealChecks.encode native.placement native.expression34 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 34 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding34 :
    NumericPolynomialChecks.encodeCombination native.witness34 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 34 [] := by kernel_rfl

theorem native.idealInputsBinding34 :
    CleanExpression.inputs native.expression34 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 34 [] := by kernel_rfl

theorem native.checked34 :
    equal (CleanExpression.polynomial native.placement native.expression34)
        (combination native.relations native.witness34) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression34 native.witness34
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 34 (by decide +kernel) native.idealCodeBinding34
    native.idealRelationsBinding native.idealWitnessBinding34

theorem native.preserved34 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression34).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression34 native.placement native.relations native.witness34
    native.checked34 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression35 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨184⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨66⟩)))))
      (Airbender.Expression.var ⟨66⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨185⟩))

noncomputable def native.witness35 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨125, by decide⟩)]

theorem native.idealCodeBinding35 :
    CleanIdealChecks.encode native.placement native.expression35 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 35 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding35 :
    NumericPolynomialChecks.encodeCombination native.witness35 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 35 [] := by kernel_rfl

theorem native.idealInputsBinding35 :
    CleanExpression.inputs native.expression35 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 35 [] := by kernel_rfl

theorem native.checked35 :
    equal (CleanExpression.polynomial native.placement native.expression35)
        (combination native.relations native.witness35) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression35 native.witness35
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 35 (by decide +kernel) native.idealCodeBinding35
    native.idealRelationsBinding native.idealWitnessBinding35

theorem native.preserved35 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression35).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression35 native.placement native.relations native.witness35
    native.checked35 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression36 : Airbender.Expression Source.BaseField :=
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
          (Airbender.Expression.var ⟨69⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 58983) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨186⟩))

noncomputable def native.witness36 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨126, by decide⟩)]

theorem native.idealCodeBinding36 :
    CleanIdealChecks.encode native.placement native.expression36 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 36 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding36 :
    NumericPolynomialChecks.encodeCombination native.witness36 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 36 [] := by kernel_rfl

theorem native.idealInputsBinding36 :
    CleanExpression.inputs native.expression36 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 36 [] := by kernel_rfl

theorem native.checked36 :
    equal (CleanExpression.polynomial native.placement native.expression36)
        (combination native.relations native.witness36) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression36 native.witness36
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 36 (by decide +kernel) native.idealCodeBinding36
    native.idealRelationsBinding native.idealWitnessBinding36

theorem native.preserved36 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression36).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression36 native.placement native.relations native.witness36
    native.checked36 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
