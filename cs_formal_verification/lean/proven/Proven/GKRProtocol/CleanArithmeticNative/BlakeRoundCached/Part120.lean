module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part035
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part036
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part037
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part038
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part039
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part040
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part041
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part042
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part043
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part119
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

local instance generatedBatch120Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch120Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope10 :
    (CleanExpression.inputs native.expression10).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression10 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 10 (by decide +kernel) native.idealInputsBinding10

theorem native.scope11 :
    (CleanExpression.inputs native.expression11).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression11 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 11 (by decide +kernel) native.idealInputsBinding11

theorem native.scope12 :
    (CleanExpression.inputs native.expression12).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression12 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 12 (by decide +kernel) native.idealInputsBinding12

theorem native.scope13 :
    (CleanExpression.inputs native.expression13).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression13 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 13 (by decide +kernel) native.idealInputsBinding13

theorem native.scope14 :
    (CleanExpression.inputs native.expression14).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression14 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 14 (by decide +kernel) native.idealInputsBinding14

theorem native.scope15 :
    (CleanExpression.inputs native.expression15).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression15 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 15 (by decide +kernel) native.idealInputsBinding15

theorem native.scopeChunk0 :
    (native.expressionsChunk0).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
    native.expressionsChunk0)
    (BoolChecks.cons native.scope0
      (BoolChecks.cons native.scope1
        (BoolChecks.cons native.scope2
          (BoolChecks.cons native.scope3
            (BoolChecks.cons native.scope4
              (BoolChecks.cons native.scope5
                (BoolChecks.cons native.scope6
                  (BoolChecks.cons native.scope7
                    (BoolChecks.cons native.scope8
                      (BoolChecks.cons native.scope9
                        (BoolChecks.cons native.scope10
                          (BoolChecks.cons native.scope11
                            (BoolChecks.cons native.scope12
                              (BoolChecks.cons native.scope13
                                (BoolChecks.cons native.scope14
                                  (BoolChecks.cons native.scope15 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk0 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk0).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk0 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved0 base data holds)
        (PredicateChecks.cons (native.preserved1 base data holds)
          (PredicateChecks.cons (native.preserved2 base data holds)
            (PredicateChecks.cons (native.preserved3 base data holds)
              (PredicateChecks.cons (native.preserved4 base data holds)
                (PredicateChecks.cons (native.preserved5 base data holds)
                  (PredicateChecks.cons (native.preserved6 base data holds)
                    (PredicateChecks.cons (native.preserved7 base data holds)
                      (PredicateChecks.cons (native.preserved8 base data holds)
                        (PredicateChecks.cons (native.preserved9 base data holds)
                          (PredicateChecks.cons (native.preserved10 base data holds)
                            (PredicateChecks.cons (native.preserved11 base data holds)
                              (PredicateChecks.cons (native.preserved12 base data holds)
                                (PredicateChecks.cons (native.preserved13 base data holds)
                                  (PredicateChecks.cons (native.preserved14 base data holds)
                                    (PredicateChecks.cons (native.preserved15 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk1 : List (Airbender.Expression Source.BaseField) :=
  [native.expression16, native.expression17, native.expression18, native.expression19, native.expression20,
    native.expression21, native.expression22, native.expression23, native.expression24, native.expression25,
    native.expression26, native.expression27, native.expression28, native.expression29, native.expression30,
    native.expression31]

theorem native.scope16 :
    (CleanExpression.inputs native.expression16).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression16 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 16 (by decide +kernel) native.idealInputsBinding16

theorem native.scope17 :
    (CleanExpression.inputs native.expression17).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression17 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 17 (by decide +kernel) native.idealInputsBinding17

theorem native.scope18 :
    (CleanExpression.inputs native.expression18).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression18 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 18 (by decide +kernel) native.idealInputsBinding18

theorem native.scope19 :
    (CleanExpression.inputs native.expression19).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression19 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 19 (by decide +kernel) native.idealInputsBinding19

theorem native.scope20 :
    (CleanExpression.inputs native.expression20).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression20 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 20 (by decide +kernel) native.idealInputsBinding20

theorem native.scope21 :
    (CleanExpression.inputs native.expression21).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression21 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 21 (by decide +kernel) native.idealInputsBinding21

theorem native.scope22 :
    (CleanExpression.inputs native.expression22).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression22 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 22 (by decide +kernel) native.idealInputsBinding22

theorem native.scope23 :
    (CleanExpression.inputs native.expression23).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression23 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 23 (by decide +kernel) native.idealInputsBinding23

theorem native.scope24 :
    (CleanExpression.inputs native.expression24).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression24 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 24 (by decide +kernel) native.idealInputsBinding24

theorem native.scope25 :
    (CleanExpression.inputs native.expression25).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression25 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 25 (by decide +kernel) native.idealInputsBinding25

theorem native.scope26 :
    (CleanExpression.inputs native.expression26).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression26 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 26 (by decide +kernel) native.idealInputsBinding26

theorem native.scope27 :
    (CleanExpression.inputs native.expression27).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression27 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 27 (by decide +kernel) native.idealInputsBinding27

theorem native.scope28 :
    (CleanExpression.inputs native.expression28).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression28 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 28 (by decide +kernel) native.idealInputsBinding28

theorem native.scope29 :
    (CleanExpression.inputs native.expression29).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression29 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 29 (by decide +kernel) native.idealInputsBinding29

theorem native.scope30 :
    (CleanExpression.inputs native.expression30).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression30 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 30 (by decide +kernel) native.idealInputsBinding30
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
