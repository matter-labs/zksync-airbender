module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
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
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part088
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part089
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part090
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part091
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part092
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part093
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part094
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part095
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part096
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part097
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part124
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

local instance generatedBatch125Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch125Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scopeChunk6 :
    (native.expressionsChunk6).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
    native.expressionsChunk6)
    (BoolChecks.cons native.scope96
      (BoolChecks.cons native.scope97
        (BoolChecks.cons native.scope98
          (BoolChecks.cons native.scope99
            (BoolChecks.cons native.scope100
              (BoolChecks.cons native.scope101
                (BoolChecks.cons native.scope102
                  (BoolChecks.cons native.scope103
                    (BoolChecks.cons native.scope104
                      (BoolChecks.cons native.scope105
                        (BoolChecks.cons native.scope106
                          (BoolChecks.cons native.scope107
                            (BoolChecks.cons native.scope108
                              (BoolChecks.cons native.scope109
                                (BoolChecks.cons native.scope110
                                  (BoolChecks.cons native.scope111 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk6 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk6).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk6 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved96 base data holds)
        (PredicateChecks.cons (native.preserved97 base data holds)
          (PredicateChecks.cons (native.preserved98 base data holds)
            (PredicateChecks.cons (native.preserved99 base data holds)
              (PredicateChecks.cons (native.preserved100 base data holds)
                (PredicateChecks.cons (native.preserved101 base data holds)
                  (PredicateChecks.cons (native.preserved102 base data holds)
                    (PredicateChecks.cons (native.preserved103 base data holds)
                      (PredicateChecks.cons (native.preserved104 base data holds)
                        (PredicateChecks.cons (native.preserved105 base data holds)
                          (PredicateChecks.cons (native.preserved106 base data holds)
                            (PredicateChecks.cons (native.preserved107 base data holds)
                              (PredicateChecks.cons (native.preserved108 base data holds)
                                (PredicateChecks.cons (native.preserved109 base data holds)
                                  (PredicateChecks.cons (native.preserved110 base data holds)
                                    (PredicateChecks.cons (native.preserved111 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk7 : List (Airbender.Expression Source.BaseField) :=
  [native.expression112, native.expression113, native.expression114, native.expression115, native.expression116,
    native.expression117, native.expression118, native.expression119, native.expression120, native.expression121,
    native.expression122, native.expression123, native.expression124, native.expression125, native.expression126,
    native.expression127]

theorem native.scope112 :
    (CleanExpression.inputs native.expression112).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression112 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 112 (by decide +kernel) native.idealInputsBinding112

theorem native.scope113 :
    (CleanExpression.inputs native.expression113).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression113 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 113 (by decide +kernel) native.idealInputsBinding113

theorem native.scope114 :
    (CleanExpression.inputs native.expression114).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression114 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 114 (by decide +kernel) native.idealInputsBinding114

theorem native.scope115 :
    (CleanExpression.inputs native.expression115).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression115 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 115 (by decide +kernel) native.idealInputsBinding115

theorem native.scope116 :
    (CleanExpression.inputs native.expression116).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression116 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 116 (by decide +kernel) native.idealInputsBinding116

theorem native.scope117 :
    (CleanExpression.inputs native.expression117).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression117 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 117 (by decide +kernel) native.idealInputsBinding117

theorem native.scope118 :
    (CleanExpression.inputs native.expression118).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression118 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 118 (by decide +kernel) native.idealInputsBinding118

theorem native.scope119 :
    (CleanExpression.inputs native.expression119).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression119 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 119 (by decide +kernel) native.idealInputsBinding119

theorem native.scope120 :
    (CleanExpression.inputs native.expression120).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression120 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 120 (by decide +kernel) native.idealInputsBinding120

theorem native.scope121 :
    (CleanExpression.inputs native.expression121).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression121 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 121 (by decide +kernel) native.idealInputsBinding121

theorem native.scope122 :
    (CleanExpression.inputs native.expression122).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression122 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 122 (by decide +kernel) native.idealInputsBinding122

theorem native.scope123 :
    (CleanExpression.inputs native.expression123).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression123 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 123 (by decide +kernel) native.idealInputsBinding123

theorem native.scope124 :
    (CleanExpression.inputs native.expression124).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression124 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 124 (by decide +kernel) native.idealInputsBinding124

theorem native.scope125 :
    (CleanExpression.inputs native.expression125).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression125 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 125 (by decide +kernel) native.idealInputsBinding125

theorem native.scope126 :
    (CleanExpression.inputs native.expression126).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression126 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 126 (by decide +kernel) native.idealInputsBinding126

theorem native.scope127 :
    (CleanExpression.inputs native.expression127).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression127 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 127 (by decide +kernel) native.idealInputsBinding127

theorem native.scopeChunk7 :
    (native.expressionsChunk7).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
    native.expressionsChunk7)
    (BoolChecks.cons native.scope112
      (BoolChecks.cons native.scope113
        (BoolChecks.cons native.scope114
          (BoolChecks.cons native.scope115
            (BoolChecks.cons native.scope116
              (BoolChecks.cons native.scope117
                (BoolChecks.cons native.scope118
                  (BoolChecks.cons native.scope119
                    (BoolChecks.cons native.scope120
                      (BoolChecks.cons native.scope121
                        (BoolChecks.cons native.scope122
                          (BoolChecks.cons native.scope123
                            (BoolChecks.cons native.scope124
                              (BoolChecks.cons native.scope125
                                (BoolChecks.cons native.scope126
                                  (BoolChecks.cons native.scope127 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk7 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk7).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk7 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved112 base data holds)
        (PredicateChecks.cons (native.preserved113 base data holds)
          (PredicateChecks.cons (native.preserved114 base data holds)
            (PredicateChecks.cons (native.preserved115 base data holds)
              (PredicateChecks.cons (native.preserved116 base data holds)
                (PredicateChecks.cons (native.preserved117 base data holds)
                  (PredicateChecks.cons (native.preserved118 base data holds)
                    (PredicateChecks.cons (native.preserved119 base data holds)
                      (PredicateChecks.cons (native.preserved120 base data holds)
                        (PredicateChecks.cons (native.preserved121 base data holds)
                          (PredicateChecks.cons (native.preserved122 base data holds)
                            (PredicateChecks.cons (native.preserved123 base data holds)
                              (PredicateChecks.cons (native.preserved124 base data holds)
                                (PredicateChecks.cons (native.preserved125 base data holds)
                                  (PredicateChecks.cons (native.preserved126 base data holds)
                                    (PredicateChecks.cons (native.preserved127 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk8 : List (Airbender.Expression Source.BaseField) :=
  [native.expression128, native.expression129, native.expression130, native.expression131, native.expression132,
    native.expression133, native.expression134, native.expression135, native.expression136, native.expression137,
    native.expression138, native.expression139, native.expression140, native.expression141, native.expression142,
    native.expression143]

theorem native.scope128 :
    (CleanExpression.inputs native.expression128).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression128 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 128 (by decide +kernel) native.idealInputsBinding128

theorem native.scope129 :
    (CleanExpression.inputs native.expression129).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression129 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 129 (by decide +kernel) native.idealInputsBinding129
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
