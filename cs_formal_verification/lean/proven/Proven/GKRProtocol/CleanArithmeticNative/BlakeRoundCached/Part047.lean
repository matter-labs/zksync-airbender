module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part046
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

local instance generatedBatch47Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch47Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved43 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression43).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression43 native.placement native.relations native.witness43
    native.checked43 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression44 : Airbender.Expression Source.BaseField :=
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
          (Airbender.Expression.var ⟨89⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 26764) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨194⟩))

noncomputable def native.witness44 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨134, by decide⟩)]

theorem native.idealCodeBinding44 :
    CleanIdealChecks.encode native.placement native.expression44 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 44 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding44 :
    NumericPolynomialChecks.encodeCombination native.witness44 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 44 [] := by kernel_rfl

theorem native.idealInputsBinding44 :
    CleanExpression.inputs native.expression44 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 44 [] := by kernel_rfl

theorem native.checked44 :
    equal (CleanExpression.polynomial native.placement native.expression44)
        (combination native.relations native.witness44) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression44 native.witness44
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 44 (by decide +kernel) native.idealCodeBinding44
    native.idealRelationsBinding native.idealWitnessBinding44

theorem native.preserved44 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression44).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression44 native.placement native.relations native.witness44
    native.checked44 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression45 : Airbender.Expression Source.BaseField :=
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
          (Airbender.Expression.var ⟨90⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 39685) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨195⟩))

noncomputable def native.witness45 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨135, by decide⟩)]

theorem native.idealCodeBinding45 :
    CleanIdealChecks.encode native.placement native.expression45 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 45 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding45 :
    NumericPolynomialChecks.encodeCombination native.witness45 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 45 [] := by kernel_rfl

theorem native.idealInputsBinding45 :
    CleanExpression.inputs native.expression45 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 45 [] := by kernel_rfl

theorem native.checked45 :
    equal (CleanExpression.polynomial native.placement native.expression45)
        (combination native.relations native.witness45) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression45 native.witness45
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 45 (by decide +kernel) native.idealCodeBinding45
    native.idealRelationsBinding native.idealWitnessBinding45

theorem native.preserved45 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression45).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression45 native.placement native.relations native.witness45
    native.checked45 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression46 : Airbender.Expression Source.BaseField :=
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
          (Airbender.Expression.var ⟨97⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 52505) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨196⟩))

noncomputable def native.witness46 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨136, by decide⟩)]

theorem native.idealCodeBinding46 :
    CleanIdealChecks.encode native.placement native.expression46 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 46 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding46 :
    NumericPolynomialChecks.encodeCombination native.witness46 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 46 [] := by kernel_rfl

theorem native.idealInputsBinding46 :
    CleanExpression.inputs native.expression46 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 46 [] := by kernel_rfl

theorem native.checked46 :
    equal (CleanExpression.polynomial native.placement native.expression46)
        (combination native.relations native.witness46) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression46 native.witness46
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 46 (by decide +kernel) native.idealCodeBinding46
    native.idealRelationsBinding native.idealWitnessBinding46

theorem native.preserved46 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression46).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression46 native.placement native.relations native.witness46
    native.checked46 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression47 : Airbender.Expression Source.BaseField :=
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
          (Airbender.Expression.var ⟨98⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 23520) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨197⟩))

noncomputable def native.witness47 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨137, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
