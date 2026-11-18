module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part079
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part080
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part081
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part082
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part083
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part084
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part085
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part086
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part091
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

local instance generatedBatch92Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch92Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope113 :
    (CleanExpression.inputs native.expression113).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression113 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 113 (by decide +kernel) native.idealInputsBinding113

theorem native.scope114 :
    (CleanExpression.inputs native.expression114).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression114 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 114 (by decide +kernel) native.idealInputsBinding114

theorem native.scope115 :
    (CleanExpression.inputs native.expression115).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression115 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 115 (by decide +kernel) native.idealInputsBinding115

theorem native.scope116 :
    (CleanExpression.inputs native.expression116).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression116 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 116 (by decide +kernel) native.idealInputsBinding116

theorem native.scope117 :
    (CleanExpression.inputs native.expression117).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression117 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 117 (by decide +kernel) native.idealInputsBinding117

theorem native.scope118 :
    (CleanExpression.inputs native.expression118).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression118 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 118 (by decide +kernel) native.idealInputsBinding118

theorem native.scope119 :
    (CleanExpression.inputs native.expression119).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression119 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 119 (by decide +kernel) native.idealInputsBinding119

theorem native.scope120 :
    (CleanExpression.inputs native.expression120).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression120 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 120 (by decide +kernel) native.idealInputsBinding120

theorem native.scope121 :
    (CleanExpression.inputs native.expression121).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression121 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 121 (by decide +kernel) native.idealInputsBinding121

theorem native.scope122 :
    (CleanExpression.inputs native.expression122).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression122 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 122 (by decide +kernel) native.idealInputsBinding122

theorem native.scope123 :
    (CleanExpression.inputs native.expression123).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression123 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 123 (by decide +kernel) native.idealInputsBinding123

theorem native.scope124 :
    (CleanExpression.inputs native.expression124).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression124 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 124 (by decide +kernel) native.idealInputsBinding124

theorem native.scope125 :
    (CleanExpression.inputs native.expression125).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression125 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 125 (by decide +kernel) native.idealInputsBinding125

theorem native.scope126 :
    (CleanExpression.inputs native.expression126).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression126 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 126 (by decide +kernel) native.idealInputsBinding126

theorem native.scope127 :
    (CleanExpression.inputs native.expression127).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression127 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 127 (by decide +kernel) native.idealInputsBinding127

theorem native.scopeChunk7 :
    (native.expressionsChunk7).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 276))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
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
    native.expression133, native.expression134]

theorem native.scope128 :
    (CleanExpression.inputs native.expression128).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression128 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 128 (by decide +kernel) native.idealInputsBinding128

theorem native.scope129 :
    (CleanExpression.inputs native.expression129).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression129 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 129 (by decide +kernel) native.idealInputsBinding129

theorem native.scope130 :
    (CleanExpression.inputs native.expression130).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression130 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 130 (by decide +kernel) native.idealInputsBinding130

theorem native.scope131 :
    (CleanExpression.inputs native.expression131).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression131 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 131 (by decide +kernel) native.idealInputsBinding131

theorem native.scope132 :
    (CleanExpression.inputs native.expression132).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression132 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 132 (by decide +kernel) native.idealInputsBinding132

theorem native.scope133 :
    (CleanExpression.inputs native.expression133).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression133 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 133 (by decide +kernel) native.idealInputsBinding133
end Airbender.Compiler.CleanArithmeticNative.BigintCached
