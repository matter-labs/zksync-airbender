module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part048
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

local instance generatedBatch49Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch49Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked50 :
    equal (CleanExpression.polynomial native.placement native.expression50)
        (combination native.relations native.witness50) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression50 native.witness50
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 50 (by decide +kernel) native.idealCodeBinding50
    native.idealRelationsBinding native.idealWitnessBinding50

theorem native.preserved50 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression50).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression50 native.placement native.relations native.witness50
    native.checked50 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression51 : Airbender.Expression Source.BaseField :=
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
            (Airbender.Expression.var ⟨94⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨153⟩))
          (Airbender.Expression.var ⟨94⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨142⟩))
          (Airbender.Expression.var ⟨141⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 57468) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨201⟩))

noncomputable def native.witness51 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨141, by decide⟩)]

theorem native.idealCodeBinding51 :
    CleanIdealChecks.encode native.placement native.expression51 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 51 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding51 :
    NumericPolynomialChecks.encodeCombination native.witness51 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 51 [] := by kernel_rfl

theorem native.idealInputsBinding51 :
    CleanExpression.inputs native.expression51 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 51 [] := by kernel_rfl

theorem native.checked51 :
    equal (CleanExpression.polynomial native.placement native.expression51)
        (combination native.relations native.witness51) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression51 native.witness51
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 51 (by decide +kernel) native.idealCodeBinding51
    native.idealRelationsBinding native.idealWitnessBinding51

theorem native.preserved51 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression51).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression51 native.placement native.relations native.witness51
    native.checked51 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression52 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨141⟩))
        (Airbender.Expression.var ⟨140⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨202⟩))

noncomputable def native.witness52 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨142, by decide⟩)]

theorem native.idealCodeBinding52 :
    CleanIdealChecks.encode native.placement native.expression52 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 52 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding52 :
    NumericPolynomialChecks.encodeCombination native.witness52 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 52 [] := by kernel_rfl

theorem native.idealInputsBinding52 :
    CleanExpression.inputs native.expression52 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 52 [] := by kernel_rfl

theorem native.checked52 :
    equal (CleanExpression.polynomial native.placement native.expression52)
        (combination native.relations native.witness52) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression52 native.witness52
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 52 (by decide +kernel) native.idealCodeBinding52
    native.idealRelationsBinding native.idealWitnessBinding52

theorem native.preserved52 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression52).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression52 native.placement native.relations native.witness52
    native.checked52 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression53 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨141⟩))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
            (Airbender.Expression.var ⟨140⟩)))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨203⟩))

noncomputable def native.witness53 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨143, by decide⟩)]

theorem native.idealCodeBinding53 :
    CleanIdealChecks.encode native.placement native.expression53 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 53 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding53 :
    NumericPolynomialChecks.encodeCombination native.witness53 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 53 [] := by kernel_rfl

theorem native.idealInputsBinding53 :
    CleanExpression.inputs native.expression53 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 53 [] := by kernel_rfl

theorem native.checked53 :
    equal (CleanExpression.polynomial native.placement native.expression53)
        (combination native.relations native.witness53) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression53 native.witness53
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 53 (by decide +kernel) native.idealCodeBinding53
    native.idealRelationsBinding native.idealWitnessBinding53

theorem native.preserved53 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression53).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression53 native.placement native.relations native.witness53
    native.checked53 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression54 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.var ⟨203⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨204⟩))
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
