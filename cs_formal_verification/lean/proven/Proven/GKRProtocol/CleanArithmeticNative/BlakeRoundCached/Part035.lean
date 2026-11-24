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

local instance generatedBatch35Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch35Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked2 :
    equal (CleanExpression.polynomial native.placement native.expression2)
        (combination native.relations native.witness2) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression2 native.witness2
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 2 (by decide +kernel) native.idealCodeBinding2
    native.idealRelationsBinding native.idealWitnessBinding2

theorem native.preserved2 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression2).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression2 native.placement native.relations native.witness2
    native.checked2 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression3 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
            (Airbender.Expression.var ⟨141⟩)))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨153⟩))

noncomputable def native.witness3 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨93, by decide⟩)]

theorem native.idealCodeBinding3 :
    CleanIdealChecks.encode native.placement native.expression3 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 3 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding3 :
    NumericPolynomialChecks.encodeCombination native.witness3 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 3 [] := by kernel_rfl

theorem native.idealInputsBinding3 :
    CleanExpression.inputs native.expression3 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 3 [] := by kernel_rfl

theorem native.checked3 :
    equal (CleanExpression.polynomial native.placement native.expression3)
        (combination native.relations native.witness3) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression3 native.witness3
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 3 (by decide +kernel) native.idealCodeBinding3
    native.idealRelationsBinding native.idealWitnessBinding3

theorem native.preserved3 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression3).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression3 native.placement native.relations native.witness3
    native.checked3 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression4 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 58951) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨5⟩)))))
      (Airbender.Expression.var ⟨5⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨154⟩))

noncomputable def native.witness4 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨94, by decide⟩)]

theorem native.idealCodeBinding4 :
    CleanIdealChecks.encode native.placement native.expression4 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 4 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding4 :
    NumericPolynomialChecks.encodeCombination native.witness4 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 4 [] := by kernel_rfl

theorem native.idealInputsBinding4 :
    CleanExpression.inputs native.expression4 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 4 [] := by kernel_rfl

theorem native.checked4 :
    equal (CleanExpression.polynomial native.placement native.expression4)
        (combination native.relations native.witness4) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression4 native.witness4
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 4 (by decide +kernel) native.idealCodeBinding4
    native.idealRelationsBinding native.idealWitnessBinding4

theorem native.preserved4 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression4).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression4 native.placement native.relations native.witness4
    native.checked4 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression5 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨154⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨37⟩)))))
      (Airbender.Expression.var ⟨37⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨155⟩))

noncomputable def native.witness5 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨95, by decide⟩)]

theorem native.idealCodeBinding5 :
    CleanIdealChecks.encode native.placement native.expression5 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 5 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding5 :
    NumericPolynomialChecks.encodeCombination native.witness5 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 5 [] := by kernel_rfl

theorem native.idealInputsBinding5 :
    CleanExpression.inputs native.expression5 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 5 [] := by kernel_rfl

theorem native.checked5 :
    equal (CleanExpression.polynomial native.placement native.expression5)
        (combination native.relations native.witness5) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression5 native.witness5
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 5 (by decide +kernel) native.idealCodeBinding5
    native.idealRelationsBinding native.idealWitnessBinding5

theorem native.preserved5 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression5).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression5 native.placement native.relations native.witness5
    native.checked5 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression6 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 27400) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨6⟩)))))
      (Airbender.Expression.var ⟨6⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨156⟩))
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
