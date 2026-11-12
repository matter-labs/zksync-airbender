module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part046
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part047
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part048
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part049
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part050
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part051
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part052
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part053
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part054
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part055
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part056
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part057
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part058
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part059
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part073
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

local instance generatedBatch74Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch74Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scopeChunk7 :
    (native.expressionsChunk7).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression128).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression128 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 128 (by decide +kernel) native.idealInputsBinding128

theorem native.scope129 :
    (CleanExpression.inputs native.expression129).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression129 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 129 (by decide +kernel) native.idealInputsBinding129

theorem native.scope130 :
    (CleanExpression.inputs native.expression130).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression130 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 130 (by decide +kernel) native.idealInputsBinding130

theorem native.scope131 :
    (CleanExpression.inputs native.expression131).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression131 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 131 (by decide +kernel) native.idealInputsBinding131

theorem native.scope132 :
    (CleanExpression.inputs native.expression132).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression132 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 132 (by decide +kernel) native.idealInputsBinding132

theorem native.scope133 :
    (CleanExpression.inputs native.expression133).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression133 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 133 (by decide +kernel) native.idealInputsBinding133

theorem native.scope134 :
    (CleanExpression.inputs native.expression134).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression134 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 134 (by decide +kernel) native.idealInputsBinding134

theorem native.scope135 :
    (CleanExpression.inputs native.expression135).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression135 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 135 (by decide +kernel) native.idealInputsBinding135

theorem native.scope136 :
    (CleanExpression.inputs native.expression136).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression136 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 136 (by decide +kernel) native.idealInputsBinding136

theorem native.scope137 :
    (CleanExpression.inputs native.expression137).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression137 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 137 (by decide +kernel) native.idealInputsBinding137

theorem native.scope138 :
    (CleanExpression.inputs native.expression138).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression138 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 138 (by decide +kernel) native.idealInputsBinding138

theorem native.scope139 :
    (CleanExpression.inputs native.expression139).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression139 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 139 (by decide +kernel) native.idealInputsBinding139

theorem native.scope140 :
    (CleanExpression.inputs native.expression140).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression140 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 140 (by decide +kernel) native.idealInputsBinding140

theorem native.scope141 :
    (CleanExpression.inputs native.expression141).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression141 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 141 (by decide +kernel) native.idealInputsBinding141

theorem native.scope142 :
    (CleanExpression.inputs native.expression142).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression142 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 142 (by decide +kernel) native.idealInputsBinding142

theorem native.scope143 :
    (CleanExpression.inputs native.expression143).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression143 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 143 (by decide +kernel) native.idealInputsBinding143

theorem native.scopeChunk8 :
    (native.expressionsChunk8).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression144).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression144 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 144 (by decide +kernel) native.idealInputsBinding144

theorem native.scope145 :
    (CleanExpression.inputs native.expression145).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression145 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 145 (by decide +kernel) native.idealInputsBinding145
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
