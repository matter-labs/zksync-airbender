module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part106
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part107
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part108
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part109
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part110
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part111
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part112
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part113
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part114
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part115
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part116
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part117
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part118
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part119
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part128
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

local instance generatedBatch129Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch129Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.arithmeticChunk11 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
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
                            (PredicateChecks.cons (native.preserved187 base data holds)
                              (PredicateChecks.cons (native.preserved188 base data holds)
                                (PredicateChecks.cons (native.preserved189 base data holds)
                                  (PredicateChecks.cons (native.preserved190 base data holds)
                                    (PredicateChecks.cons (native.preserved191 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk12 : List (Airbender.Expression Source.BaseField) :=
  [native.expression192, native.expression193, native.expression194, native.expression195, native.expression196,
    native.expression197, native.expression198, native.expression199, native.expression200, native.expression201,
    native.expression202, native.expression203, native.expression204, native.expression205, native.expression206,
    native.expression207]

theorem native.scope192 :
    (CleanExpression.inputs native.expression192).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression192 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 192 (by decide +kernel) native.idealInputsBinding192

theorem native.scope193 :
    (CleanExpression.inputs native.expression193).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression193 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 193 (by decide +kernel) native.idealInputsBinding193

theorem native.scope194 :
    (CleanExpression.inputs native.expression194).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression194 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 194 (by decide +kernel) native.idealInputsBinding194

theorem native.scope195 :
    (CleanExpression.inputs native.expression195).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression195 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 195 (by decide +kernel) native.idealInputsBinding195

theorem native.scope196 :
    (CleanExpression.inputs native.expression196).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression196 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 196 (by decide +kernel) native.idealInputsBinding196

theorem native.scope197 :
    (CleanExpression.inputs native.expression197).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression197 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 197 (by decide +kernel) native.idealInputsBinding197

theorem native.scope198 :
    (CleanExpression.inputs native.expression198).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression198 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 198 (by decide +kernel) native.idealInputsBinding198

theorem native.scope199 :
    (CleanExpression.inputs native.expression199).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression199 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 199 (by decide +kernel) native.idealInputsBinding199

theorem native.scope200 :
    (CleanExpression.inputs native.expression200).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression200 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 200 (by decide +kernel) native.idealInputsBinding200

theorem native.scope201 :
    (CleanExpression.inputs native.expression201).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression201 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 201 (by decide +kernel) native.idealInputsBinding201

theorem native.scope202 :
    (CleanExpression.inputs native.expression202).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression202 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 202 (by decide +kernel) native.idealInputsBinding202

theorem native.scope203 :
    (CleanExpression.inputs native.expression203).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression203 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 203 (by decide +kernel) native.idealInputsBinding203

theorem native.scope204 :
    (CleanExpression.inputs native.expression204).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression204 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 204 (by decide +kernel) native.idealInputsBinding204

theorem native.scope205 :
    (CleanExpression.inputs native.expression205).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression205 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 205 (by decide +kernel) native.idealInputsBinding205

theorem native.scope206 :
    (CleanExpression.inputs native.expression206).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression206 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 206 (by decide +kernel) native.idealInputsBinding206

theorem native.scope207 :
    (CleanExpression.inputs native.expression207).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression207 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 207 (by decide +kernel) native.idealInputsBinding207

theorem native.scopeChunk12 :
    (native.expressionsChunk12).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
    native.expressionsChunk12)
    (BoolChecks.cons native.scope192
      (BoolChecks.cons native.scope193
        (BoolChecks.cons native.scope194
          (BoolChecks.cons native.scope195
            (BoolChecks.cons native.scope196
              (BoolChecks.cons native.scope197
                (BoolChecks.cons native.scope198
                  (BoolChecks.cons native.scope199
                    (BoolChecks.cons native.scope200
                      (BoolChecks.cons native.scope201
                        (BoolChecks.cons native.scope202
                          (BoolChecks.cons native.scope203
                            (BoolChecks.cons native.scope204
                              (BoolChecks.cons native.scope205
                                (BoolChecks.cons native.scope206
                                  (BoolChecks.cons native.scope207 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk12 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk12).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk12 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved192 base data holds)
        (PredicateChecks.cons (native.preserved193 base data holds)
          (PredicateChecks.cons (native.preserved194 base data holds)
            (PredicateChecks.cons (native.preserved195 base data holds)
              (PredicateChecks.cons (native.preserved196 base data holds)
                (PredicateChecks.cons (native.preserved197 base data holds)
                  (PredicateChecks.cons (native.preserved198 base data holds)
                    (PredicateChecks.cons (native.preserved199 base data holds)
                      (PredicateChecks.cons (native.preserved200 base data holds)
                        (PredicateChecks.cons (native.preserved201 base data holds)
                          (PredicateChecks.cons (native.preserved202 base data holds)
                            (PredicateChecks.cons (native.preserved203 base data holds)
                              (PredicateChecks.cons (native.preserved204 base data holds)
                                (PredicateChecks.cons (native.preserved205 base data holds)
                                  (PredicateChecks.cons (native.preserved206 base data holds)
                                    (PredicateChecks.cons (native.preserved207 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk13 : List (Airbender.Expression Source.BaseField) :=
  [native.expression208, native.expression209, native.expression210, native.expression211, native.expression212,
    native.expression213, native.expression214, native.expression215, native.expression216, native.expression217,
    native.expression218, native.expression219]

theorem native.scope208 :
    (CleanExpression.inputs native.expression208).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression208 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 208 (by decide +kernel) native.idealInputsBinding208

theorem native.scope209 :
    (CleanExpression.inputs native.expression209).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression209 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 209 (by decide +kernel) native.idealInputsBinding209

theorem native.scope210 :
    (CleanExpression.inputs native.expression210).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression210 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 210 (by decide +kernel) native.idealInputsBinding210
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
