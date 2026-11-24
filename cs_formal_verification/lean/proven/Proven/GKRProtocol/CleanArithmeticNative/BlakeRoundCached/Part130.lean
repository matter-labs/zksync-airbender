module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part116
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part117
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part118
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part119
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part120
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part121
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part122
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part123
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part124
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part125
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part126
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part127
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part128
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part129
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

local instance generatedBatch130Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch130Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope211 :
    (CleanExpression.inputs native.expression211).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression211 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 211 (by decide +kernel) native.idealInputsBinding211

theorem native.scope212 :
    (CleanExpression.inputs native.expression212).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression212 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 212 (by decide +kernel) native.idealInputsBinding212

theorem native.scope213 :
    (CleanExpression.inputs native.expression213).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression213 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 213 (by decide +kernel) native.idealInputsBinding213

theorem native.scope214 :
    (CleanExpression.inputs native.expression214).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression214 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 214 (by decide +kernel) native.idealInputsBinding214

theorem native.scope215 :
    (CleanExpression.inputs native.expression215).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression215 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 215 (by decide +kernel) native.idealInputsBinding215

theorem native.scope216 :
    (CleanExpression.inputs native.expression216).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression216 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 216 (by decide +kernel) native.idealInputsBinding216

theorem native.scope217 :
    (CleanExpression.inputs native.expression217).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression217 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 217 (by decide +kernel) native.idealInputsBinding217

theorem native.scope218 :
    (CleanExpression.inputs native.expression218).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression218 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 218 (by decide +kernel) native.idealInputsBinding218

theorem native.scope219 :
    (CleanExpression.inputs native.expression219).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression219 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 219 (by decide +kernel) native.idealInputsBinding219

theorem native.scopeChunk13 :
    (native.expressionsChunk13).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
    native.expressionsChunk13)
    (BoolChecks.cons native.scope208
      (BoolChecks.cons native.scope209
        (BoolChecks.cons native.scope210
          (BoolChecks.cons native.scope211
            (BoolChecks.cons native.scope212
              (BoolChecks.cons native.scope213
                (BoolChecks.cons native.scope214
                  (BoolChecks.cons native.scope215
                    (BoolChecks.cons native.scope216
                      (BoolChecks.cons native.scope217
                        (BoolChecks.cons native.scope218 (BoolChecks.cons native.scope219 BoolChecks.nil))))))))))))

theorem native.arithmeticChunk13 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk13).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk13 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved208 base data holds)
        (PredicateChecks.cons (native.preserved209 base data holds)
          (PredicateChecks.cons (native.preserved210 base data holds)
            (PredicateChecks.cons (native.preserved211 base data holds)
              (PredicateChecks.cons (native.preserved212 base data holds)
                (PredicateChecks.cons (native.preserved213 base data holds)
                  (PredicateChecks.cons (native.preserved214 base data holds)
                    (PredicateChecks.cons (native.preserved215 base data holds)
                      (PredicateChecks.cons (native.preserved216 base data holds)
                        (PredicateChecks.cons (native.preserved217 base data holds)
                          (PredicateChecks.cons (native.preserved218 base data holds)
                            (PredicateChecks.cons (native.preserved219 base data holds)
                              PredicateChecks.nil)))))))))))))

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
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++
                              ([] : List (Airbender.Expression Source.BaseField)))))))))))))))

theorem native.scopeChecked :
    ((native.expressions).all fun expression : Airbender.Expression Source.BaseField =>
        (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  all_append_true
    (fun expression : Airbender.Expression Source.BaseField =>
      (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
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
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++
                              ([] : List (Airbender.Expression Source.BaseField)))))))))))))))
    native.scopeChunk0
    (all_append_true
      (fun expression : Airbender.Expression Source.BaseField =>
        (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
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
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++
                              ([] : List (Airbender.Expression Source.BaseField))))))))))))))
      native.scopeChunk1
      (all_append_true
        (fun expression : Airbender.Expression Source.BaseField =>
          (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
        native.expressionsChunk2
        (native.expressionsChunk3 ++
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++
                              ([] : List (Airbender.Expression Source.BaseField)))))))))))))
        native.scopeChunk2
        (all_append_true
          (fun expression : Airbender.Expression Source.BaseField =>
            (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
          native.expressionsChunk3
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++
                              ([] : List (Airbender.Expression Source.BaseField))))))))))))
          native.scopeChunk3
          (all_append_true
            (fun expression : Airbender.Expression Source.BaseField =>
              (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
            native.expressionsChunk4
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++
                              ([] : List (Airbender.Expression Source.BaseField)))))))))))
            native.scopeChunk4
            (all_append_true
              (fun expression : Airbender.Expression Source.BaseField =>
                (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
              native.expressionsChunk5
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField))))))))))
              native.scopeChunk5
              (all_append_true
                (fun expression : Airbender.Expression Source.BaseField =>
                  (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
                native.expressionsChunk6
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField)))))))))
                native.scopeChunk6
                (all_append_true
                  (fun expression : Airbender.Expression Source.BaseField =>
                    (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
                  native.expressionsChunk7
                  (native.expressionsChunk8 ++
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField))))))))
                  native.scopeChunk7
                  (all_append_true
                    (fun expression : Airbender.Expression Source.BaseField =>
                      (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
                    native.expressionsChunk8
                    (native.expressionsChunk9 ++
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField)))))))
                    native.scopeChunk8
                    (all_append_true
                      (fun expression : Airbender.Expression Source.BaseField =>
                        (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
                      native.expressionsChunk9
                      (native.expressionsChunk10 ++
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField))))))
                      native.scopeChunk9
                      (all_append_true
                        (fun expression : Airbender.Expression Source.BaseField =>
                          (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
                        native.expressionsChunk10
                        (native.expressionsChunk11 ++
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField)))))
                        native.scopeChunk10
                        (all_append_true
                          (fun expression : Airbender.Expression Source.BaseField =>
                            (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
                          native.expressionsChunk11
                          (native.expressionsChunk12 ++
                            (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField))))
                          native.scopeChunk11
                          (all_append_true
                            (fun expression : Airbender.Expression Source.BaseField =>
                              (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
                            native.expressionsChunk12
                            (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField)))
                            native.scopeChunk12
                            (all_append_true
                              (fun expression : Airbender.Expression Source.BaseField =>
                                (CleanExpression.inputs expression).all (fun index => decide (index < 763)))
                              native.expressionsChunk13 ([] : List (Airbender.Expression Source.BaseField))
                              native.scopeChunk13
                              (show
                                ((([] : List (Airbender.Expression Source.BaseField))).all
                                    fun expression : Airbender.Expression Source.BaseField =>
                                    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
                                  true
                                from rfl))))))))))))))

theorem native.arithmetic_preserved (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic :
      ∀ gate ∈ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact).gates,
        gate.expressionResidual
            (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address) =
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
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++
                                ([] : List (Airbender.Expression Source.BaseField)))))))))))))))
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
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++
                                ([] : List (Airbender.Expression Source.BaseField))))))))))))))
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
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++
                                ([] : List (Airbender.Expression Source.BaseField)))))))))))))
          (native.environment base data) (native.arithmeticChunk2 base data holds)
          (CleanExpression.append_assertions_hold native.expressionsChunk3
            (native.expressionsChunk4 ++
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++
                                ([] : List (Airbender.Expression Source.BaseField))))))))))))
            (native.environment base data) (native.arithmeticChunk3 base data holds)
            (CleanExpression.append_assertions_hold native.expressionsChunk4
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++
                                ([] : List (Airbender.Expression Source.BaseField)))))))))))
              (native.environment base data) (native.arithmeticChunk4 base data holds)
              (CleanExpression.append_assertions_hold native.expressionsChunk5
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++
                                ([] : List (Airbender.Expression Source.BaseField))))))))))
                (native.environment base data) (native.arithmeticChunk5 base data holds)
                (CleanExpression.append_assertions_hold native.expressionsChunk6
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++
                                ([] : List (Airbender.Expression Source.BaseField)))))))))
                  (native.environment base data) (native.arithmeticChunk6 base data holds)
                  (CleanExpression.append_assertions_hold native.expressionsChunk7
                    (native.expressionsChunk8 ++
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField))))))))
                    (native.environment base data) (native.arithmeticChunk7 base data holds)
                    (CleanExpression.append_assertions_hold native.expressionsChunk8
                      (native.expressionsChunk9 ++
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField)))))))
                      (native.environment base data) (native.arithmeticChunk8 base data holds)
                      (CleanExpression.append_assertions_hold native.expressionsChunk9
                        (native.expressionsChunk10 ++
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField))))))
                        (native.environment base data) (native.arithmeticChunk9 base data holds)
                        (CleanExpression.append_assertions_hold native.expressionsChunk10
                          (native.expressionsChunk11 ++
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField)))))
                          (native.environment base data) (native.arithmeticChunk10 base data holds)
                          (CleanExpression.append_assertions_hold native.expressionsChunk11
                            (native.expressionsChunk12 ++
                              (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField))))
                            (native.environment base data) (native.arithmeticChunk11 base data holds)
                            (CleanExpression.append_assertions_hold native.expressionsChunk12
                              (native.expressionsChunk13 ++ ([] : List (Airbender.Expression Source.BaseField)))
                              (native.environment base data) (native.arithmeticChunk12 base data holds)
                              (CleanExpression.append_assertions_hold native.expressionsChunk13
                                ([] : List (Airbender.Expression Source.BaseField)) (native.environment base data)
                                (native.arithmeticChunk13 base data holds)
                                (show
                                  FlatOperation.ConstraintsHoldFlat (native.environment base data)
                                    (([] : List (Airbender.Expression Source.BaseField)).map FlatOperation.assert)
                                  from by trivial))))))))))))))
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
