module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part042
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.KeccakCached
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCached
public import Proven.GKRProtocol.CleanPlacementNative.KeccakCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch43Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch43Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness102 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨134, by decide⟩)]

theorem native.idealCodeBinding102 :
    CleanIdealChecks.encode native.placement native.expression102 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 102 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding102 :
    NumericPolynomialChecks.encodeCombination native.witness102 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 102 [] := by kernel_rfl

theorem native.idealInputsBinding102 :
    CleanExpression.inputs native.expression102 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 102 [] := by kernel_rfl

theorem native.checked102 :
    equal (CleanExpression.polynomial native.placement native.expression102)
        (combination native.relations native.witness102) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression102 native.witness102
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    102 (by decide +kernel) native.idealCodeBinding102 native.idealRelationsBinding native.idealWitnessBinding102

theorem native.preserved102 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression102).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression102 native.placement native.relations native.witness102
    native.checked102 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression103 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨28⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨30⟩))))
    (Airbender.Expression.var ⟨64⟩)

noncomputable def native.witness103 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨135, by decide⟩)]

theorem native.idealCodeBinding103 :
    CleanIdealChecks.encode native.placement native.expression103 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 103 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding103 :
    NumericPolynomialChecks.encodeCombination native.witness103 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 103 [] := by kernel_rfl

theorem native.idealInputsBinding103 :
    CleanExpression.inputs native.expression103 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 103 [] := by kernel_rfl

theorem native.checked103 :
    equal (CleanExpression.polynomial native.placement native.expression103)
        (combination native.relations native.witness103) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression103 native.witness103
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    103 (by decide +kernel) native.idealCodeBinding103 native.idealRelationsBinding native.idealWitnessBinding103

theorem native.preserved103 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression103).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression103 native.placement native.relations native.witness103
    native.checked103 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression104 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨39⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨41⟩))))
    (Airbender.Expression.var ⟨64⟩)

noncomputable def native.witness104 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨136, by decide⟩)]

theorem native.idealCodeBinding104 :
    CleanIdealChecks.encode native.placement native.expression104 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 104 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding104 :
    NumericPolynomialChecks.encodeCombination native.witness104 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 104 [] := by kernel_rfl

theorem native.idealInputsBinding104 :
    CleanExpression.inputs native.expression104 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 104 [] := by kernel_rfl

theorem native.checked104 :
    equal (CleanExpression.polynomial native.placement native.expression104)
        (combination native.relations native.witness104) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression104 native.witness104
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    104 (by decide +kernel) native.idealCodeBinding104 native.idealRelationsBinding native.idealWitnessBinding104

theorem native.preserved104 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression104).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression104 native.placement native.relations native.witness104
    native.checked104 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression105 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨40⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨42⟩))))
    (Airbender.Expression.var ⟨64⟩)

noncomputable def native.witness105 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨137, by decide⟩)]

theorem native.idealCodeBinding105 :
    CleanIdealChecks.encode native.placement native.expression105 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 105 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding105 :
    NumericPolynomialChecks.encodeCombination native.witness105 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 105 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
