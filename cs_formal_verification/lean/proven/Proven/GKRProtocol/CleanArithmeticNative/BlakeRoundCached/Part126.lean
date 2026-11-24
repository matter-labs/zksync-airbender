module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part092
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part093
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part094
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part095
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part096
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part097
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part098
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part099
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part100
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part101
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part125
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

local instance generatedBatch126Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch126Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope130 :
    (CleanExpression.inputs native.expression130).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression130 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 130 (by decide +kernel) native.idealInputsBinding130

theorem native.scope131 :
    (CleanExpression.inputs native.expression131).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression131 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 131 (by decide +kernel) native.idealInputsBinding131

theorem native.scope132 :
    (CleanExpression.inputs native.expression132).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression132 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 132 (by decide +kernel) native.idealInputsBinding132

theorem native.scope133 :
    (CleanExpression.inputs native.expression133).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression133 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 133 (by decide +kernel) native.idealInputsBinding133

theorem native.scope134 :
    (CleanExpression.inputs native.expression134).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression134 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 134 (by decide +kernel) native.idealInputsBinding134

theorem native.scope135 :
    (CleanExpression.inputs native.expression135).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression135 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 135 (by decide +kernel) native.idealInputsBinding135

theorem native.scope136 :
    (CleanExpression.inputs native.expression136).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression136 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 136 (by decide +kernel) native.idealInputsBinding136

theorem native.scope137 :
    (CleanExpression.inputs native.expression137).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression137 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 137 (by decide +kernel) native.idealInputsBinding137

theorem native.scope138 :
    (CleanExpression.inputs native.expression138).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression138 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 138 (by decide +kernel) native.idealInputsBinding138

theorem native.scope139 :
    (CleanExpression.inputs native.expression139).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression139 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 139 (by decide +kernel) native.idealInputsBinding139

theorem native.scope140 :
    (CleanExpression.inputs native.expression140).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression140 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 140 (by decide +kernel) native.idealInputsBinding140

theorem native.scope141 :
    (CleanExpression.inputs native.expression141).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression141 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 141 (by decide +kernel) native.idealInputsBinding141

theorem native.scope142 :
    (CleanExpression.inputs native.expression142).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression142 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 142 (by decide +kernel) native.idealInputsBinding142

theorem native.scope143 :
    (CleanExpression.inputs native.expression143).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression143 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 143 (by decide +kernel) native.idealInputsBinding143

theorem native.scopeChunk8 :
    (native.expressionsChunk8).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
    native.expressionsChunk8)
    (BoolChecks.cons native.scope128
      (BoolChecks.cons native.scope129
        (BoolChecks.cons native.scope130
          (BoolChecks.cons native.scope131
            (BoolChecks.cons native.scope132
              (BoolChecks.cons native.scope133
                (BoolChecks.cons native.scope134
                  (BoolChecks.cons native.scope135
                    (BoolChecks.cons native.scope136
                      (BoolChecks.cons native.scope137
                        (BoolChecks.cons native.scope138
                          (BoolChecks.cons native.scope139
                            (BoolChecks.cons native.scope140
                              (BoolChecks.cons native.scope141
                                (BoolChecks.cons native.scope142
                                  (BoolChecks.cons native.scope143 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk8 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk8).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk8 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved128 base data holds)
        (PredicateChecks.cons (native.preserved129 base data holds)
          (PredicateChecks.cons (native.preserved130 base data holds)
            (PredicateChecks.cons (native.preserved131 base data holds)
              (PredicateChecks.cons (native.preserved132 base data holds)
                (PredicateChecks.cons (native.preserved133 base data holds)
                  (PredicateChecks.cons (native.preserved134 base data holds)
                    (PredicateChecks.cons (native.preserved135 base data holds)
                      (PredicateChecks.cons (native.preserved136 base data holds)
                        (PredicateChecks.cons (native.preserved137 base data holds)
                          (PredicateChecks.cons (native.preserved138 base data holds)
                            (PredicateChecks.cons (native.preserved139 base data holds)
                              (PredicateChecks.cons (native.preserved140 base data holds)
                                (PredicateChecks.cons (native.preserved141 base data holds)
                                  (PredicateChecks.cons (native.preserved142 base data holds)
                                    (PredicateChecks.cons (native.preserved143 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk9 : List (Airbender.Expression Source.BaseField) :=
  [native.expression144, native.expression145, native.expression146, native.expression147, native.expression148,
    native.expression149, native.expression150, native.expression151, native.expression152, native.expression153,
    native.expression154, native.expression155, native.expression156, native.expression157, native.expression158,
    native.expression159]

theorem native.scope144 :
    (CleanExpression.inputs native.expression144).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression144 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 144 (by decide +kernel) native.idealInputsBinding144

theorem native.scope145 :
    (CleanExpression.inputs native.expression145).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression145 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 145 (by decide +kernel) native.idealInputsBinding145

theorem native.scope146 :
    (CleanExpression.inputs native.expression146).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression146 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 146 (by decide +kernel) native.idealInputsBinding146

theorem native.scope147 :
    (CleanExpression.inputs native.expression147).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression147 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 147 (by decide +kernel) native.idealInputsBinding147

theorem native.scope148 :
    (CleanExpression.inputs native.expression148).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression148 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 148 (by decide +kernel) native.idealInputsBinding148

theorem native.scope149 :
    (CleanExpression.inputs native.expression149).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression149 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 149 (by decide +kernel) native.idealInputsBinding149

theorem native.scope150 :
    (CleanExpression.inputs native.expression150).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression150 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 150 (by decide +kernel) native.idealInputsBinding150
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
