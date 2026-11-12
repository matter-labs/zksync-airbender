module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
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

local instance generatedBatch34Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch34Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

def native.environment (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Environment Source.BaseField :=
  ⟨fun index =>
    base ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address (native.placement index)),
    data⟩

theorem native.relations_hold (base : GKRAddress → Source.BaseField)
    (holds :
      ∀ gate ∈ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact).gates,
        gate.expressionResidual
            (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address) =
          0) :
    Satisfies native.relations
      (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address) :=
  by
  intro polynomial member
  obtain ⟨gate, included, same⟩ := List.mem_map.mp member
  rw [← same,
    gate.checked_value
      (List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked gate
        included)]
  exact holds gate included

theorem native.idealRelationsBinding :
    (native.relations).map NumericPolynomialChecks.encode =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).relations.toList := by kernel_rfl

theorem native.idealCountBinding : (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.size = 220 := by kernel_rfl

theorem native.idealScopeLimitBinding :
    (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).scopeLimit = 763 := by kernel_rfl

noncomputable def native.expression0 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨0⟩))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField))))
    (Airbender.Expression.var ⟨0⟩)

noncomputable def native.witness0 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨90, by decide⟩)]

theorem native.idealCodeBinding0 :
    CleanIdealChecks.encode native.placement native.expression0 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 0 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding0 :
    NumericPolynomialChecks.encodeCombination native.witness0 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 0 [] := by kernel_rfl

theorem native.idealInputsBinding0 :
    CleanExpression.inputs native.expression0 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 0 [] := by kernel_rfl

theorem native.checked0 :
    equal (CleanExpression.polynomial native.placement native.expression0)
        (combination native.relations native.witness0) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression0 native.witness0
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 0 (by decide +kernel) native.idealCodeBinding0
    native.idealRelationsBinding native.idealWitnessBinding0

theorem native.preserved0 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression0).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression0 native.placement native.relations native.witness0
    native.checked0 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression1 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.add
                        (Airbender.Expression.add
                          (Airbender.Expression.add
                            (Airbender.Expression.add
                              (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                              (Airbender.Expression.var ⟨139⟩))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.var ⟨140⟩))
                              (Airbender.Expression.const (Int.cast (Int.ofNat 2) : Source.BaseField))))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.var ⟨141⟩))
                            (Airbender.Expression.const (Int.cast (Int.ofNat 4) : Source.BaseField))))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨142⟩))
                          (Airbender.Expression.const (Int.cast (Int.ofNat 8) : Source.BaseField))))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨143⟩))
                        (Airbender.Expression.const (Int.cast (Int.ofNat 16) : Source.BaseField))))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨144⟩))
                      (Airbender.Expression.const (Int.cast (Int.ofNat 32) : Source.BaseField))))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨145⟩))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 64) : Source.BaseField))))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨146⟩))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 128) : Source.BaseField))))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨147⟩))
                (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField))))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨148⟩))
              (Airbender.Expression.const (Int.cast (Int.ofNat 512) : Source.BaseField))))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨149⟩))
            (Airbender.Expression.const (Int.cast (Int.ofNat 1024) : Source.BaseField))))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨150⟩))
          (Airbender.Expression.const (Int.cast (Int.ofNat 2048) : Source.BaseField))))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨151⟩))
        (Airbender.Expression.const (Int.cast (Int.ofNat 4096) : Source.BaseField))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨136⟩))

noncomputable def native.witness1 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨91, by decide⟩)]

theorem native.idealCodeBinding1 :
    CleanIdealChecks.encode native.placement native.expression1 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 1 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding1 :
    NumericPolynomialChecks.encodeCombination native.witness1 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 1 [] := by kernel_rfl

theorem native.idealInputsBinding1 :
    CleanExpression.inputs native.expression1 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 1 [] := by kernel_rfl

theorem native.checked1 :
    equal (CleanExpression.polynomial native.placement native.expression1)
        (combination native.relations native.witness1) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression1 native.witness1
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 1 (by decide +kernel) native.idealCodeBinding1
    native.idealRelationsBinding native.idealWitnessBinding1

theorem native.preserved1 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression1).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression1 native.placement native.relations native.witness1
    native.checked1 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression2 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨151⟩))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨148⟩))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.var ⟨139⟩))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
            (Airbender.Expression.var ⟨151⟩)))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨152⟩))

noncomputable def native.witness2 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨92, by decide⟩)]

theorem native.idealCodeBinding2 :
    CleanIdealChecks.encode native.placement native.expression2 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 2 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding2 :
    NumericPolynomialChecks.encodeCombination native.witness2 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 2 [] := by kernel_rfl

theorem native.idealInputsBinding2 :
    CleanExpression.inputs native.expression2 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 2 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
