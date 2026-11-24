module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part089
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

local instance generatedBatch90Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch90Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked118 :
    equal (CleanExpression.polynomial native.placement native.expression118)
        (combination native.relations native.witness118) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression118 native.witness118
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 118 (by decide +kernel) native.idealCodeBinding118
    native.idealRelationsBinding native.idealWitnessBinding118

theorem native.preserved118 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression118).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression118 native.placement native.relations native.witness118
    native.checked118 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression119 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨606⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                (Airbender.Expression.var ⟨607⟩))))
          (Airbender.Expression.var ⟨152⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨152⟩))))
        (Airbender.Expression.var ⟨26⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨28⟩))

noncomputable def native.witness119 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨209, by decide⟩)]

theorem native.idealCodeBinding119 :
    CleanIdealChecks.encode native.placement native.expression119 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 119 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding119 :
    NumericPolynomialChecks.encodeCombination native.witness119 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 119 [] := by kernel_rfl

theorem native.idealInputsBinding119 :
    CleanExpression.inputs native.expression119 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 119 [] := by kernel_rfl

theorem native.checked119 :
    equal (CleanExpression.polynomial native.placement native.expression119)
        (combination native.relations native.witness119) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression119 native.witness119
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 119 (by decide +kernel) native.idealCodeBinding119
    native.idealRelationsBinding native.idealWitnessBinding119

theorem native.preserved119 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression119).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression119 native.placement native.relations native.witness119
    native.checked119 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression120 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨612⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                (Airbender.Expression.var ⟨613⟩))))
          (Airbender.Expression.var ⟨152⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨152⟩))))
        (Airbender.Expression.var ⟨29⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨31⟩))

noncomputable def native.witness120 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨210, by decide⟩)]

theorem native.idealCodeBinding120 :
    CleanIdealChecks.encode native.placement native.expression120 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 120 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding120 :
    NumericPolynomialChecks.encodeCombination native.witness120 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 120 [] := by kernel_rfl

theorem native.idealInputsBinding120 :
    CleanExpression.inputs native.expression120 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 120 [] := by kernel_rfl

theorem native.checked120 :
    equal (CleanExpression.polynomial native.placement native.expression120)
        (combination native.relations native.witness120) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression120 native.witness120
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 120 (by decide +kernel) native.idealCodeBinding120
    native.idealRelationsBinding native.idealWitnessBinding120

theorem native.preserved120 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression120).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression120 native.placement native.relations native.witness120
    native.checked120 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression121 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨618⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                (Airbender.Expression.var ⟨619⟩))))
          (Airbender.Expression.var ⟨152⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨152⟩))))
        (Airbender.Expression.var ⟨30⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨32⟩))

noncomputable def native.witness121 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨211, by decide⟩)]

theorem native.idealCodeBinding121 :
    CleanIdealChecks.encode native.placement native.expression121 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 121 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding121 :
    NumericPolynomialChecks.encodeCombination native.witness121 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 121 [] := by kernel_rfl

theorem native.idealInputsBinding121 :
    CleanExpression.inputs native.expression121 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 121 [] := by kernel_rfl

theorem native.checked121 :
    equal (CleanExpression.polynomial native.placement native.expression121)
        (combination native.relations native.witness121) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression121 native.witness121
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 121 (by decide +kernel) native.idealCodeBinding121
    native.idealRelationsBinding native.idealWitnessBinding121

theorem native.preserved121 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression121).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression121 native.placement native.relations native.witness121
    native.checked121 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression122 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨624⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                (Airbender.Expression.var ⟨625⟩))))
          (Airbender.Expression.var ⟨152⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨152⟩))))
        (Airbender.Expression.var ⟨33⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨35⟩))
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
