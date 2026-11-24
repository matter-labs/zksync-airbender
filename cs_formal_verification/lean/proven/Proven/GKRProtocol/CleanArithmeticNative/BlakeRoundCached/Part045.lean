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

local instance generatedBatch45Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch45Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression37 : Airbender.Expression Source.BaseField :=
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
          (Airbender.Expression.var ⟨70⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 27145) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨187⟩))

noncomputable def native.witness37 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨127, by decide⟩)]

theorem native.idealCodeBinding37 :
    CleanIdealChecks.encode native.placement native.expression37 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 37 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding37 :
    NumericPolynomialChecks.encodeCombination native.witness37 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 37 [] := by kernel_rfl

theorem native.idealInputsBinding37 :
    CleanExpression.inputs native.expression37 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 37 [] := by kernel_rfl

theorem native.checked37 :
    equal (CleanExpression.polynomial native.placement native.expression37)
        (combination native.relations native.witness37) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression37 native.witness37
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 37 (by decide +kernel) native.idealCodeBinding37
    native.idealRelationsBinding native.idealWitnessBinding37

theorem native.preserved37 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression37).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression37 native.placement native.relations native.witness37
    native.checked37 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression38 : Airbender.Expression Source.BaseField :=
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
          (Airbender.Expression.var ⟨73⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 44677) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨188⟩))

noncomputable def native.witness38 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨128, by decide⟩)]

theorem native.idealCodeBinding38 :
    CleanIdealChecks.encode native.placement native.expression38 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 38 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding38 :
    NumericPolynomialChecks.encodeCombination native.witness38 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 38 [] := by kernel_rfl

theorem native.idealInputsBinding38 :
    CleanExpression.inputs native.expression38 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 38 [] := by kernel_rfl

theorem native.checked38 :
    equal (CleanExpression.polynomial native.placement native.expression38)
        (combination native.relations native.witness38) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression38 native.witness38
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 38 (by decide +kernel) native.idealCodeBinding38
    native.idealRelationsBinding native.idealWitnessBinding38

theorem native.preserved38 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression38).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression38 native.placement native.relations native.witness38
    native.checked38 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression39 : Airbender.Expression Source.BaseField :=
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
          (Airbender.Expression.var ⟨74⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 47975) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨189⟩))

noncomputable def native.witness39 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨129, by decide⟩)]

theorem native.idealCodeBinding39 :
    CleanIdealChecks.encode native.placement native.expression39 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 39 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding39 :
    NumericPolynomialChecks.encodeCombination native.witness39 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 39 [] := by kernel_rfl

theorem native.idealInputsBinding39 :
    CleanExpression.inputs native.expression39 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 39 [] := by kernel_rfl

theorem native.checked39 :
    equal (CleanExpression.polynomial native.placement native.expression39)
        (combination native.relations native.witness39) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression39 native.witness39
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 39 (by decide +kernel) native.idealCodeBinding39
    native.idealRelationsBinding native.idealWitnessBinding39

theorem native.preserved39 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression39).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression39 native.placement native.relations native.witness39
    native.checked39 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression40 : Airbender.Expression Source.BaseField :=
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
          (Airbender.Expression.var ⟨77⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨142⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 62322) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨190⟩))

noncomputable def native.witness40 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨130, by decide⟩)]

theorem native.idealCodeBinding40 :
    CleanIdealChecks.encode native.placement native.expression40 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 40 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
