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

local instance generatedBatch52Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch52Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression61 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨149⟩))
        (Airbender.Expression.var ⟨203⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨211⟩))

noncomputable def native.witness61 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨151, by decide⟩)]

theorem native.idealCodeBinding61 :
    CleanIdealChecks.encode native.placement native.expression61 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 61 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding61 :
    NumericPolynomialChecks.encodeCombination native.witness61 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 61 [] := by kernel_rfl

theorem native.idealInputsBinding61 :
    CleanExpression.inputs native.expression61 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 61 [] := by kernel_rfl

theorem native.checked61 :
    equal (CleanExpression.polynomial native.placement native.expression61)
        (combination native.relations native.witness61) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression61 native.witness61
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 61 (by decide +kernel) native.idealCodeBinding61
    native.idealRelationsBinding native.idealWitnessBinding61

theorem native.preserved61 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression61).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression61 native.placement native.relations native.witness61
    native.checked61 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression62 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨150⟩))
        (Airbender.Expression.var ⟨203⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨212⟩))

noncomputable def native.witness62 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨152, by decide⟩)]

theorem native.idealCodeBinding62 :
    CleanIdealChecks.encode native.placement native.expression62 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 62 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding62 :
    NumericPolynomialChecks.encodeCombination native.witness62 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 62 [] := by kernel_rfl

theorem native.idealInputsBinding62 :
    CleanExpression.inputs native.expression62 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 62 [] := by kernel_rfl

theorem native.checked62 :
    equal (CleanExpression.polynomial native.placement native.expression62)
        (combination native.relations native.witness62) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression62 native.witness62
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 62 (by decide +kernel) native.idealCodeBinding62
    native.idealRelationsBinding native.idealWitnessBinding62

theorem native.preserved62 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression62).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression62 native.placement native.relations native.witness62
    native.checked62 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression63 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨151⟩))
        (Airbender.Expression.var ⟨203⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨213⟩))

noncomputable def native.witness63 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨153, by decide⟩)]

theorem native.idealCodeBinding63 :
    CleanIdealChecks.encode native.placement native.expression63 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 63 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding63 :
    NumericPolynomialChecks.encodeCombination native.witness63 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 63 [] := by kernel_rfl

theorem native.idealInputsBinding63 :
    CleanExpression.inputs native.expression63 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 63 [] := by kernel_rfl

theorem native.checked63 :
    equal (CleanExpression.polynomial native.placement native.expression63)
        (combination native.relations native.witness63) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression63 native.witness63
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 63 (by decide +kernel) native.idealCodeBinding63
    native.idealRelationsBinding native.idealWitnessBinding63

theorem native.preserved63 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression63).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression63 native.placement native.relations native.witness63
    native.checked63 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression64 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨214⟩))

noncomputable def native.witness64 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨154, by decide⟩)]

theorem native.idealCodeBinding64 :
    CleanIdealChecks.encode native.placement native.expression64 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 64 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
