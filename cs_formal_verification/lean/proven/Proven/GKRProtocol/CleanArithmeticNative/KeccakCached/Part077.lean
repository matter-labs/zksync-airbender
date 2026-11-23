module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part064
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part065
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part066
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part067
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part068
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part069
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part070
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part071
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part072
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part073
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part074
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part075
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part076
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

local instance generatedBatch77Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch77Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.arithmeticChunk11 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk11).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk11 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved176 base data holds)
        (PredicateChecks.cons (native.preserved177 base data holds)
          (PredicateChecks.cons (native.preserved178 base data holds)
            (PredicateChecks.cons (native.preserved179 base data holds)
              (PredicateChecks.cons (native.preserved180 base data holds)
                (PredicateChecks.cons (native.preserved181 base data holds)
                  (PredicateChecks.cons (native.preserved182 base data holds)
                    (PredicateChecks.cons (native.preserved183 base data holds)
                      (PredicateChecks.cons (native.preserved184 base data holds)
                        (PredicateChecks.cons (native.preserved185 base data holds)
                          (PredicateChecks.cons (native.preserved186 base data holds)
                            PredicateChecks.nil))))))))))))

noncomputable def native.expressions : List (Airbender.Expression Source.BaseField) :=
  native.expressionsChunk0 ++
    (native.expressionsChunk1 ++
      (native.expressionsChunk2 ++
        (native.expressionsChunk3 ++
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))))))))))

theorem native.scopeChecked :
    ((native.expressions).all fun expression : Airbender.Expression Source.BaseField =>
        (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  all_append_true
    (fun expression : Airbender.Expression Source.BaseField =>
      (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
    native.expressionsChunk0
    (native.expressionsChunk1 ++
      (native.expressionsChunk2 ++
        (native.expressionsChunk3 ++
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))))))))))
    native.scopeChunk0
    (all_append_true
      (fun expression : Airbender.Expression Source.BaseField =>
        (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
      native.expressionsChunk1
      (native.expressionsChunk2 ++
        (native.expressionsChunk3 ++
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))))))))))
      native.scopeChunk1
      (all_append_true
        (fun expression : Airbender.Expression Source.BaseField =>
          (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
        native.expressionsChunk2
        (native.expressionsChunk3 ++
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))))))))
        native.scopeChunk2
        (all_append_true
          (fun expression : Airbender.Expression Source.BaseField =>
            (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
          native.expressionsChunk3
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))))))))
          native.scopeChunk3
          (all_append_true
            (fun expression : Airbender.Expression Source.BaseField =>
              (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
            native.expressionsChunk4
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))))))
            native.scopeChunk4
            (all_append_true
              (fun expression : Airbender.Expression Source.BaseField =>
                (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
              native.expressionsChunk5
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))))))
              native.scopeChunk5
              (all_append_true
                (fun expression : Airbender.Expression Source.BaseField =>
                  (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
                native.expressionsChunk6
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))))
                native.scopeChunk6
                (all_append_true
                  (fun expression : Airbender.Expression Source.BaseField =>
                    (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
                  native.expressionsChunk7
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))))
                  native.scopeChunk7
                  (all_append_true
                    (fun expression : Airbender.Expression Source.BaseField =>
                      (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
                    native.expressionsChunk8
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))
                    native.scopeChunk8
                    (all_append_true
                      (fun expression : Airbender.Expression Source.BaseField =>
                        (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
                      native.expressionsChunk9
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))
                      native.scopeChunk9
                      (all_append_true
                        (fun expression : Airbender.Expression Source.BaseField =>
                          (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
                        native.expressionsChunk10
                        (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))
                        native.scopeChunk10
                        (all_append_true
                          (fun expression : Airbender.Expression Source.BaseField =>
                            (CleanExpression.inputs expression).all (fun index => decide (index < 266)))
                          native.expressionsChunk11 ([] : List (Airbender.Expression Source.BaseField))
                          native.scopeChunk11
                          (show
                            ((([] : List (Airbender.Expression Source.BaseField))).all
                                fun expression : Airbender.Expression Source.BaseField =>
                                (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
                              true
                            from rfl))))))))))))

theorem native.arithmetic_preserved (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic :
      ∀ gate ∈ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact).gates,
        gate.expressionResidual (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address) =
          0) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressions).map FlatOperation.assert) :=
  by
  have holds := native.relations_hold base arithmetic
  exact
    CleanExpression.append_assertions_hold native.expressionsChunk0
      (native.expressionsChunk1 ++
        (native.expressionsChunk2 ++
          (native.expressionsChunk3 ++
            (native.expressionsChunk4 ++
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++
                            ([] : List (Airbender.Expression Source.BaseField)))))))))))))
      (native.environment base data) (native.arithmeticChunk0 base data holds)
      (CleanExpression.append_assertions_hold native.expressionsChunk1
        (native.expressionsChunk2 ++
          (native.expressionsChunk3 ++
            (native.expressionsChunk4 ++
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))))))))))
        (native.environment base data) (native.arithmeticChunk1 base data holds)
        (CleanExpression.append_assertions_hold native.expressionsChunk2
          (native.expressionsChunk3 ++
            (native.expressionsChunk4 ++
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))))))))
          (native.environment base data) (native.arithmeticChunk2 base data holds)
          (CleanExpression.append_assertions_hold native.expressionsChunk3
            (native.expressionsChunk4 ++
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))))))))
            (native.environment base data) (native.arithmeticChunk3 base data holds)
            (CleanExpression.append_assertions_hold native.expressionsChunk4
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))))))
              (native.environment base data) (native.arithmeticChunk4 base data holds)
              (CleanExpression.append_assertions_hold native.expressionsChunk5
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))))))
                (native.environment base data) (native.arithmeticChunk5 base data holds)
                (CleanExpression.append_assertions_hold native.expressionsChunk6
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))))
                  (native.environment base data) (native.arithmeticChunk6 base data holds)
                  (CleanExpression.append_assertions_hold native.expressionsChunk7
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))))
                    (native.environment base data) (native.arithmeticChunk7 base data holds)
                    (CleanExpression.append_assertions_hold native.expressionsChunk8
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))))
                      (native.environment base data) (native.arithmeticChunk8 base data holds)
                      (CleanExpression.append_assertions_hold native.expressionsChunk9
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField))))
                        (native.environment base data) (native.arithmeticChunk9 base data holds)
                        (CleanExpression.append_assertions_hold native.expressionsChunk10
                          (native.expressionsChunk11 ++ ([] : List (Airbender.Expression Source.BaseField)))
                          (native.environment base data) (native.arithmeticChunk10 base data holds)
                          (CleanExpression.append_assertions_hold native.expressionsChunk11
                            ([] : List (Airbender.Expression Source.BaseField)) (native.environment base data)
                            (native.arithmeticChunk11 base data holds)
                            (show
                              FlatOperation.ConstraintsHoldFlat (native.environment base data)
                                (([] : List (Airbender.Expression Source.BaseField)).map FlatOperation.assert)
                              from by trivial))))))))))))
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
