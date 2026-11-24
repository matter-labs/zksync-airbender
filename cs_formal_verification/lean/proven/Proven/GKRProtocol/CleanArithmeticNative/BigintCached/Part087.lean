module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part014
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part015
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part016
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part017
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part018
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part019
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part020
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part021
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part022
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part023
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part024
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part025
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part026
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part027
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part028
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part029
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part030
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part031
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part032
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part035
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part037
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part039
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part041
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part043
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part045
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part047
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part049
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part051
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part053
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part055
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part057
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part058
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part059
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part060
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part086
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BigintCached
public import Proven.GKRProtocol.FullArithmeticNative.BigintCached
public import Proven.GKRProtocol.CleanPlacementNative.BigintCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch87Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch87Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope14 :
    (CleanExpression.inputs native.expression14).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression14 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 14 (by decide +kernel) native.idealInputsBinding14

theorem native.scope15 :
    (CleanExpression.inputs native.expression15).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression15 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 15 (by decide +kernel) native.idealInputsBinding15

theorem native.scopeChunk0 :
    (native.expressionsChunk0).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 276))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression16).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression16 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 16 (by decide +kernel) native.idealInputsBinding16

theorem native.scope17 :
    (CleanExpression.inputs native.expression17).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression17 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 17 (by decide +kernel) native.idealInputsBinding17

theorem native.scope18 :
    (CleanExpression.inputs native.expression18).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression18 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 18 (by decide +kernel) native.idealInputsBinding18

theorem native.scope19 :
    (CleanExpression.inputs native.expression19).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression19 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 19 (by decide +kernel) native.idealInputsBinding19

theorem native.scope20 :
    (CleanExpression.inputs native.expression20).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression20 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 20 (by decide +kernel) native.idealInputsBinding20

theorem native.scope21 :
    (CleanExpression.inputs native.expression21).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression21 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 21 (by decide +kernel) native.idealInputsBinding21

theorem native.scope22 :
    (CleanExpression.inputs native.expression22).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression22 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 22 (by decide +kernel) native.idealInputsBinding22

theorem native.scope23 :
    (CleanExpression.inputs native.expression23).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression23 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 23 (by decide +kernel) native.idealInputsBinding23

theorem native.scope24 :
    (CleanExpression.inputs native.expression24).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression24 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 24 (by decide +kernel) native.idealInputsBinding24

theorem native.scope25 :
    (CleanExpression.inputs native.expression25).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression25 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 25 (by decide +kernel) native.idealInputsBinding25

theorem native.scope26 :
    (CleanExpression.inputs native.expression26).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression26 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 26 (by decide +kernel) native.idealInputsBinding26

theorem native.scope27 :
    (CleanExpression.inputs native.expression27).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression27 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 27 (by decide +kernel) native.idealInputsBinding27

theorem native.scope28 :
    (CleanExpression.inputs native.expression28).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression28 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 28 (by decide +kernel) native.idealInputsBinding28

theorem native.scope29 :
    (CleanExpression.inputs native.expression29).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression29 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 29 (by decide +kernel) native.idealInputsBinding29

theorem native.scope30 :
    (CleanExpression.inputs native.expression30).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression30 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 30 (by decide +kernel) native.idealInputsBinding30

theorem native.scope31 :
    (CleanExpression.inputs native.expression31).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression31 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 31 (by decide +kernel) native.idealInputsBinding31

theorem native.scopeChunk1 :
    (native.expressionsChunk1).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 276))) (items :=
    native.expressionsChunk1)
    (BoolChecks.cons native.scope16
      (BoolChecks.cons native.scope17
        (BoolChecks.cons native.scope18
          (BoolChecks.cons native.scope19
            (BoolChecks.cons native.scope20
              (BoolChecks.cons native.scope21
                (BoolChecks.cons native.scope22
                  (BoolChecks.cons native.scope23
                    (BoolChecks.cons native.scope24
                      (BoolChecks.cons native.scope25
                        (BoolChecks.cons native.scope26
                          (BoolChecks.cons native.scope27
                            (BoolChecks.cons native.scope28
                              (BoolChecks.cons native.scope29
                                (BoolChecks.cons native.scope30
                                  (BoolChecks.cons native.scope31 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk1 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk1).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk1 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved16 base data holds)
        (PredicateChecks.cons (native.preserved17 base data holds)
          (PredicateChecks.cons (native.preserved18 base data holds)
            (PredicateChecks.cons (native.preserved19 base data holds)
              (PredicateChecks.cons (native.preserved20 base data holds)
                (PredicateChecks.cons (native.preserved21 base data holds)
                  (PredicateChecks.cons (native.preserved22 base data holds)
                    (PredicateChecks.cons (native.preserved23 base data holds)
                      (PredicateChecks.cons (native.preserved24 base data holds)
                        (PredicateChecks.cons (native.preserved25 base data holds)
                          (PredicateChecks.cons (native.preserved26 base data holds)
                            (PredicateChecks.cons (native.preserved27 base data holds)
                              (PredicateChecks.cons (native.preserved28 base data holds)
                                (PredicateChecks.cons (native.preserved29 base data holds)
                                  (PredicateChecks.cons (native.preserved30 base data holds)
                                    (PredicateChecks.cons (native.preserved31 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk2 : List (Airbender.Expression Source.BaseField) :=
  [native.expression32, native.expression33, native.expression34, native.expression35, native.expression36,
    native.expression37, native.expression38, native.expression39, native.expression40, native.expression41,
    native.expression42, native.expression43, native.expression44, native.expression45, native.expression46,
    native.expression47]
end Airbender.Compiler.CleanArithmeticNative.BigintCached
