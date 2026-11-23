module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part100
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

local instance generatedBatch101Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch101Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding156 :
    NumericPolynomialChecks.encodeCombination native.witness156 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 156 [] := by kernel_rfl

theorem native.idealInputsBinding156 :
    CleanExpression.inputs native.expression156 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 156 [] := by kernel_rfl

theorem native.checked156 :
    equal (CleanExpression.polynomial native.placement native.expression156)
        (combination native.relations native.witness156) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression156 native.witness156
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 156 (by decide +kernel) native.idealCodeBinding156
    native.idealRelationsBinding native.idealWitnessBinding156

theorem native.preserved156 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression156).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression156 native.placement native.relations native.witness156
    native.checked156 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression157 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨486⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨486⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness157 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨247, by decide⟩)]

theorem native.idealCodeBinding157 :
    CleanIdealChecks.encode native.placement native.expression157 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 157 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding157 :
    NumericPolynomialChecks.encodeCombination native.witness157 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 157 [] := by kernel_rfl

theorem native.idealInputsBinding157 :
    CleanExpression.inputs native.expression157 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 157 [] := by kernel_rfl

theorem native.checked157 :
    equal (CleanExpression.polynomial native.placement native.expression157)
        (combination native.relations native.witness157) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression157 native.witness157
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 157 (by decide +kernel) native.idealCodeBinding157
    native.idealRelationsBinding native.idealWitnessBinding157

theorem native.preserved157 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression157).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression157 native.placement native.relations native.witness157
    native.checked157 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression158 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨489⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨489⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness158 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨248, by decide⟩)]

theorem native.idealCodeBinding158 :
    CleanIdealChecks.encode native.placement native.expression158 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 158 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding158 :
    NumericPolynomialChecks.encodeCombination native.witness158 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 158 [] := by kernel_rfl

theorem native.idealInputsBinding158 :
    CleanExpression.inputs native.expression158 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 158 [] := by kernel_rfl

theorem native.checked158 :
    equal (CleanExpression.polynomial native.placement native.expression158)
        (combination native.relations native.witness158) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression158 native.witness158
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 158 (by decide +kernel) native.idealCodeBinding158
    native.idealRelationsBinding native.idealWitnessBinding158

theorem native.preserved158 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression158).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression158 native.placement native.relations native.witness158
    native.checked158 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression159 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨516⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨516⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness159 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨249, by decide⟩)]

theorem native.idealCodeBinding159 :
    CleanIdealChecks.encode native.placement native.expression159 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 159 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding159 :
    NumericPolynomialChecks.encodeCombination native.witness159 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 159 [] := by kernel_rfl

theorem native.idealInputsBinding159 :
    CleanExpression.inputs native.expression159 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 159 [] := by kernel_rfl

theorem native.checked159 :
    equal (CleanExpression.polynomial native.placement native.expression159)
        (combination native.relations native.witness159) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression159 native.witness159
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 159 (by decide +kernel) native.idealCodeBinding159
    native.idealRelationsBinding native.idealWitnessBinding159
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
