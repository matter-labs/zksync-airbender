module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part033
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

local instance generatedBatch34Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch34Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding71 :
    CleanIdealChecks.encode native.placement native.expression71 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 71 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding71 :
    NumericPolynomialChecks.encodeCombination native.witness71 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 71 [] := by kernel_rfl

theorem native.idealInputsBinding71 :
    CleanExpression.inputs native.expression71 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 71 [] := by kernel_rfl

theorem native.checked71 :
    equal (CleanExpression.polynomial native.placement native.expression71)
        (combination native.relations native.witness71) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression71 native.witness71
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 71
    (by decide +kernel) native.idealCodeBinding71 native.idealRelationsBinding native.idealWitnessBinding71

theorem native.preserved71 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression71).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression71 native.placement native.relations native.witness71
    native.checked71 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression72 : Airbender.Expression Source.BaseField :=
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
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.add
                        (Airbender.Expression.add
                          (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                          (Airbender.Expression.var ⟨81⟩))
                        (Airbender.Expression.var ⟨84⟩))
                      (Airbender.Expression.var ⟨80⟩))
                    (Airbender.Expression.var ⟨82⟩))
                  (Airbender.Expression.var ⟨83⟩)))))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨198⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
              (Airbender.Expression.var ⟨199⟩)))))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.var ⟨81⟩))
                  (Airbender.Expression.var ⟨84⟩))
                (Airbender.Expression.var ⟨80⟩))
              (Airbender.Expression.var ⟨82⟩))
            (Airbender.Expression.var ⟨83⟩)))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.var ⟨198⟩))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.negSucc 65535) : Source.BaseField)))
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨80⟩))
                        (Airbender.Expression.const (Int.cast (Int.ofNat 2) : Source.BaseField))))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨81⟩))
                      (Airbender.Expression.const (Int.cast (Int.ofNat 2) : Source.BaseField))))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨82⟩))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 13) : Source.BaseField))))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨83⟩))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 8) : Source.BaseField))))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨84⟩))
                (Airbender.Expression.const (Int.cast (Int.ofNat 14) : Source.BaseField))))))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨98⟩))
                      (Airbender.Expression.var ⟨63⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨31⟩))
                    (Airbender.Expression.var ⟨64⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨39⟩))
                  (Airbender.Expression.var ⟨65⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨47⟩))
                (Airbender.Expression.var ⟨66⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨47⟩))
              (Airbender.Expression.var ⟨67⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨23⟩))
            (Airbender.Expression.var ⟨68⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨15⟩))
          (Airbender.Expression.var ⟨69⟩))))

noncomputable def native.witness72 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨104, by decide⟩)]

theorem native.idealCodeBinding72 :
    CleanIdealChecks.encode native.placement native.expression72 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 72 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding72 :
    NumericPolynomialChecks.encodeCombination native.witness72 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 72 [] := by kernel_rfl

theorem native.idealInputsBinding72 :
    CleanExpression.inputs native.expression72 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 72 [] := by kernel_rfl

theorem native.checked72 :
    equal (CleanExpression.polynomial native.placement native.expression72)
        (combination native.relations native.witness72) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression72 native.witness72
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 72
    (by decide +kernel) native.idealCodeBinding72 native.idealRelationsBinding native.idealWitnessBinding72

theorem native.preserved72 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression72).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression72 native.placement native.relations native.witness72
    native.checked72 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression73 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.add
                        (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                        (Airbender.Expression.var ⟨81⟩))
                      (Airbender.Expression.var ⟨84⟩))
                    (Airbender.Expression.var ⟨80⟩))
                  (Airbender.Expression.var ⟨82⟩))
                (Airbender.Expression.var ⟨83⟩)))))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.var ⟨206⟩))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
            (Airbender.Expression.var ⟨207⟩)))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨47⟩))
                    (Airbender.Expression.var ⟨63⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨94⟩))
                  (Airbender.Expression.var ⟨64⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨55⟩))
                (Airbender.Expression.var ⟨65⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨55⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨94⟩))
            (Airbender.Expression.var ⟨68⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨39⟩))
          (Airbender.Expression.var ⟨69⟩))))

noncomputable def native.witness73 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨105, by decide⟩)]

theorem native.idealCodeBinding73 :
    CleanIdealChecks.encode native.placement native.expression73 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 73 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding73 :
    NumericPolynomialChecks.encodeCombination native.witness73 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 73 [] := by kernel_rfl

theorem native.idealInputsBinding73 :
    CleanExpression.inputs native.expression73 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 73 [] := by kernel_rfl

theorem native.checked73 :
    equal (CleanExpression.polynomial native.placement native.expression73)
        (combination native.relations native.witness73) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression73 native.witness73
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 73
    (by decide +kernel) native.idealCodeBinding73 native.idealRelationsBinding native.idealWitnessBinding73

theorem native.preserved73 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression73).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression73 native.placement native.relations native.witness73
    native.checked73 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression74 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                    (Airbender.Expression.add
                      (Airbender.Expression.add
                        (Airbender.Expression.add
                          (Airbender.Expression.add
                            (Airbender.Expression.add
                              (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                              (Airbender.Expression.var ⟨81⟩))
                            (Airbender.Expression.var ⟨84⟩))
                          (Airbender.Expression.var ⟨80⟩))
                        (Airbender.Expression.var ⟨82⟩))
                      (Airbender.Expression.var ⟨83⟩)))))
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.var ⟨214⟩))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                  (Airbender.Expression.var ⟨215⟩)))))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.var ⟨81⟩))
                (Airbender.Expression.var ⟨84⟩)))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨214⟩))
              (Airbender.Expression.var ⟨209⟩))))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨80⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨217⟩))
            (Airbender.Expression.var ⟨208⟩))))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨82⟩))
            (Airbender.Expression.var ⟨83⟩)))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.var ⟨215⟩))
          (Airbender.Expression.var ⟨206⟩))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨57⟩))
                      (Airbender.Expression.var ⟨63⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨33⟩))
                    (Airbender.Expression.var ⟨64⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨41⟩))
                  (Airbender.Expression.var ⟨65⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨49⟩))
                (Airbender.Expression.var ⟨66⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨49⟩))
              (Airbender.Expression.var ⟨67⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨25⟩))
            (Airbender.Expression.var ⟨68⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨17⟩))
          (Airbender.Expression.var ⟨69⟩))))

noncomputable def native.witness74 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨106, by decide⟩)]

theorem native.idealCodeBinding74 :
    CleanIdealChecks.encode native.placement native.expression74 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 74 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding74 :
    NumericPolynomialChecks.encodeCombination native.witness74 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 74 [] := by kernel_rfl

theorem native.idealInputsBinding74 :
    CleanExpression.inputs native.expression74 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 74 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
