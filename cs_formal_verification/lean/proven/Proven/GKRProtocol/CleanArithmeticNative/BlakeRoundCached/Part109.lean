module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part108
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

local instance generatedBatch109Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch109Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved183 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression183).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression183 native.placement native.relations native.witness183
    native.checked183 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression184 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨655⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨655⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness184 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨274, by decide⟩)]

theorem native.idealCodeBinding184 :
    CleanIdealChecks.encode native.placement native.expression184 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 184 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding184 :
    NumericPolynomialChecks.encodeCombination native.witness184 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 184 [] := by kernel_rfl

theorem native.idealInputsBinding184 :
    CleanExpression.inputs native.expression184 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 184 [] := by kernel_rfl

theorem native.checked184 :
    equal (CleanExpression.polynomial native.placement native.expression184)
        (combination native.relations native.witness184) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression184 native.witness184
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 184 (by decide +kernel) native.idealCodeBinding184
    native.idealRelationsBinding native.idealWitnessBinding184

theorem native.preserved184 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression184).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression184 native.placement native.relations native.witness184
    native.checked184 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression185 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨658⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨658⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness185 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨275, by decide⟩)]

theorem native.idealCodeBinding185 :
    CleanIdealChecks.encode native.placement native.expression185 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 185 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding185 :
    NumericPolynomialChecks.encodeCombination native.witness185 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 185 [] := by kernel_rfl

theorem native.idealInputsBinding185 :
    CleanExpression.inputs native.expression185 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 185 [] := by kernel_rfl

theorem native.checked185 :
    equal (CleanExpression.polynomial native.placement native.expression185)
        (combination native.relations native.witness185) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression185 native.witness185
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 185 (by decide +kernel) native.idealCodeBinding185
    native.idealRelationsBinding native.idealWitnessBinding185

theorem native.preserved185 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression185).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression185 native.placement native.relations native.witness185
    native.checked185 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression186 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨661⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨661⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness186 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨276, by decide⟩)]

theorem native.idealCodeBinding186 :
    CleanIdealChecks.encode native.placement native.expression186 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 186 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding186 :
    NumericPolynomialChecks.encodeCombination native.witness186 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 186 [] := by kernel_rfl

theorem native.idealInputsBinding186 :
    CleanExpression.inputs native.expression186 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 186 [] := by kernel_rfl

theorem native.checked186 :
    equal (CleanExpression.polynomial native.placement native.expression186)
        (combination native.relations native.witness186) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression186 native.witness186
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 186 (by decide +kernel) native.idealCodeBinding186
    native.idealRelationsBinding native.idealWitnessBinding186

theorem native.preserved186 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression186).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression186 native.placement native.relations native.witness186
    native.checked186 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression187 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨664⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨664⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness187 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨277, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
