module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part061
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part062
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part063
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part064
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part065
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part066
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part067
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part068
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part069
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part070
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part071
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part072
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part073
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part074
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part075
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part076
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part077
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part078
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part079
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part080
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part081
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part082
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part083
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part084
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part085
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part086
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part087
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part123
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

local instance generatedBatch124Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch124Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope91 :
    (CleanExpression.inputs native.expression91).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression91 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 91 (by decide +kernel) native.idealInputsBinding91

theorem native.scope92 :
    (CleanExpression.inputs native.expression92).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression92 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 92 (by decide +kernel) native.idealInputsBinding92

theorem native.scope93 :
    (CleanExpression.inputs native.expression93).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression93 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 93 (by decide +kernel) native.idealInputsBinding93

theorem native.scope94 :
    (CleanExpression.inputs native.expression94).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression94 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 94 (by decide +kernel) native.idealInputsBinding94

theorem native.scope95 :
    (CleanExpression.inputs native.expression95).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression95 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 95 (by decide +kernel) native.idealInputsBinding95

theorem native.scopeChunk5 :
    (native.expressionsChunk5).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
    native.expressionsChunk5)
    (BoolChecks.cons native.scope80
      (BoolChecks.cons native.scope81
        (BoolChecks.cons native.scope82
          (BoolChecks.cons native.scope83
            (BoolChecks.cons native.scope84
              (BoolChecks.cons native.scope85
                (BoolChecks.cons native.scope86
                  (BoolChecks.cons native.scope87
                    (BoolChecks.cons native.scope88
                      (BoolChecks.cons native.scope89
                        (BoolChecks.cons native.scope90
                          (BoolChecks.cons native.scope91
                            (BoolChecks.cons native.scope92
                              (BoolChecks.cons native.scope93
                                (BoolChecks.cons native.scope94
                                  (BoolChecks.cons native.scope95 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk5 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk5).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk5 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved80 base data holds)
        (PredicateChecks.cons (native.preserved81 base data holds)
          (PredicateChecks.cons (native.preserved82 base data holds)
            (PredicateChecks.cons (native.preserved83 base data holds)
              (PredicateChecks.cons (native.preserved84 base data holds)
                (PredicateChecks.cons (native.preserved85 base data holds)
                  (PredicateChecks.cons (native.preserved86 base data holds)
                    (PredicateChecks.cons (native.preserved87 base data holds)
                      (PredicateChecks.cons (native.preserved88 base data holds)
                        (PredicateChecks.cons (native.preserved89 base data holds)
                          (PredicateChecks.cons (native.preserved90 base data holds)
                            (PredicateChecks.cons (native.preserved91 base data holds)
                              (PredicateChecks.cons (native.preserved92 base data holds)
                                (PredicateChecks.cons (native.preserved93 base data holds)
                                  (PredicateChecks.cons (native.preserved94 base data holds)
                                    (PredicateChecks.cons (native.preserved95 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk6 : List (Airbender.Expression Source.BaseField) :=
  [native.expression96, native.expression97, native.expression98, native.expression99, native.expression100,
    native.expression101, native.expression102, native.expression103, native.expression104, native.expression105,
    native.expression106, native.expression107, native.expression108, native.expression109, native.expression110,
    native.expression111]

theorem native.scope96 :
    (CleanExpression.inputs native.expression96).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression96 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 96 (by decide +kernel) native.idealInputsBinding96

theorem native.scope97 :
    (CleanExpression.inputs native.expression97).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression97 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 97 (by decide +kernel) native.idealInputsBinding97

theorem native.scope98 :
    (CleanExpression.inputs native.expression98).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression98 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 98 (by decide +kernel) native.idealInputsBinding98

theorem native.scope99 :
    (CleanExpression.inputs native.expression99).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression99 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 99 (by decide +kernel) native.idealInputsBinding99

theorem native.scope100 :
    (CleanExpression.inputs native.expression100).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression100 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 100 (by decide +kernel) native.idealInputsBinding100

theorem native.scope101 :
    (CleanExpression.inputs native.expression101).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression101 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 101 (by decide +kernel) native.idealInputsBinding101

theorem native.scope102 :
    (CleanExpression.inputs native.expression102).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression102 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 102 (by decide +kernel) native.idealInputsBinding102

theorem native.scope103 :
    (CleanExpression.inputs native.expression103).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression103 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 103 (by decide +kernel) native.idealInputsBinding103

theorem native.scope104 :
    (CleanExpression.inputs native.expression104).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression104 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 104 (by decide +kernel) native.idealInputsBinding104

theorem native.scope105 :
    (CleanExpression.inputs native.expression105).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression105 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 105 (by decide +kernel) native.idealInputsBinding105

theorem native.scope106 :
    (CleanExpression.inputs native.expression106).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression106 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 106 (by decide +kernel) native.idealInputsBinding106

theorem native.scope107 :
    (CleanExpression.inputs native.expression107).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression107 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 107 (by decide +kernel) native.idealInputsBinding107

theorem native.scope108 :
    (CleanExpression.inputs native.expression108).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression108 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 108 (by decide +kernel) native.idealInputsBinding108

theorem native.scope109 :
    (CleanExpression.inputs native.expression109).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression109 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 109 (by decide +kernel) native.idealInputsBinding109

theorem native.scope110 :
    (CleanExpression.inputs native.expression110).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression110 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 110 (by decide +kernel) native.idealInputsBinding110

theorem native.scope111 :
    (CleanExpression.inputs native.expression111).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression111 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 111 (by decide +kernel) native.idealInputsBinding111
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
