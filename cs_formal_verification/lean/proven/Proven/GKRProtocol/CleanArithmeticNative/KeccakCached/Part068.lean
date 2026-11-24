module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part014
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part015
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part016
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part017
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part018
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part019
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part020
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part021
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part022
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part067
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

local instance generatedBatch68Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch68Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope5 :
    (CleanExpression.inputs native.expression5).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression5 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 5 (by decide +kernel) native.idealInputsBinding5

theorem native.scope6 :
    (CleanExpression.inputs native.expression6).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression6 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 6 (by decide +kernel) native.idealInputsBinding6

theorem native.scope7 :
    (CleanExpression.inputs native.expression7).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression7 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 7 (by decide +kernel) native.idealInputsBinding7

theorem native.scope8 :
    (CleanExpression.inputs native.expression8).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression8 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 8 (by decide +kernel) native.idealInputsBinding8

theorem native.scope9 :
    (CleanExpression.inputs native.expression9).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression9 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 9 (by decide +kernel) native.idealInputsBinding9

theorem native.scope10 :
    (CleanExpression.inputs native.expression10).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression10 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 10 (by decide +kernel) native.idealInputsBinding10

theorem native.scope11 :
    (CleanExpression.inputs native.expression11).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression11 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 11 (by decide +kernel) native.idealInputsBinding11

theorem native.scope12 :
    (CleanExpression.inputs native.expression12).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression12 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 12 (by decide +kernel) native.idealInputsBinding12

theorem native.scope13 :
    (CleanExpression.inputs native.expression13).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression13 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 13 (by decide +kernel) native.idealInputsBinding13

theorem native.scope14 :
    (CleanExpression.inputs native.expression14).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression14 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 14 (by decide +kernel) native.idealInputsBinding14

theorem native.scope15 :
    (CleanExpression.inputs native.expression15).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression15 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 15 (by decide +kernel) native.idealInputsBinding15

theorem native.scopeChunk0 :
    (native.expressionsChunk0).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression16).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression16 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 16 (by decide +kernel) native.idealInputsBinding16

theorem native.scope17 :
    (CleanExpression.inputs native.expression17).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression17 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 17 (by decide +kernel) native.idealInputsBinding17

theorem native.scope18 :
    (CleanExpression.inputs native.expression18).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression18 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 18 (by decide +kernel) native.idealInputsBinding18

theorem native.scope19 :
    (CleanExpression.inputs native.expression19).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression19 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 19 (by decide +kernel) native.idealInputsBinding19

theorem native.scope20 :
    (CleanExpression.inputs native.expression20).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression20 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 20 (by decide +kernel) native.idealInputsBinding20

theorem native.scope21 :
    (CleanExpression.inputs native.expression21).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression21 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 21 (by decide +kernel) native.idealInputsBinding21

theorem native.scope22 :
    (CleanExpression.inputs native.expression22).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression22 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 22 (by decide +kernel) native.idealInputsBinding22

theorem native.scope23 :
    (CleanExpression.inputs native.expression23).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression23 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 23 (by decide +kernel) native.idealInputsBinding23

theorem native.scope24 :
    (CleanExpression.inputs native.expression24).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression24 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 24 (by decide +kernel) native.idealInputsBinding24

theorem native.scope25 :
    (CleanExpression.inputs native.expression25).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression25 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 25 (by decide +kernel) native.idealInputsBinding25
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
