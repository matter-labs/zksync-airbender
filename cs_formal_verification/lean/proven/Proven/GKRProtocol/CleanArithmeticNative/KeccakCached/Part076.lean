module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part060
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part061
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part062
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part063
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part064
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part065
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part066
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part067
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part075
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

local instance generatedBatch76Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch76Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope167 :
    (CleanExpression.inputs native.expression167).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression167 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 167 (by decide +kernel) native.idealInputsBinding167

theorem native.scope168 :
    (CleanExpression.inputs native.expression168).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression168 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 168 (by decide +kernel) native.idealInputsBinding168

theorem native.scope169 :
    (CleanExpression.inputs native.expression169).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression169 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 169 (by decide +kernel) native.idealInputsBinding169

theorem native.scope170 :
    (CleanExpression.inputs native.expression170).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression170 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 170 (by decide +kernel) native.idealInputsBinding170

theorem native.scope171 :
    (CleanExpression.inputs native.expression171).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression171 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 171 (by decide +kernel) native.idealInputsBinding171

theorem native.scope172 :
    (CleanExpression.inputs native.expression172).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression172 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 172 (by decide +kernel) native.idealInputsBinding172

theorem native.scope173 :
    (CleanExpression.inputs native.expression173).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression173 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 173 (by decide +kernel) native.idealInputsBinding173

theorem native.scope174 :
    (CleanExpression.inputs native.expression174).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression174 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 174 (by decide +kernel) native.idealInputsBinding174

theorem native.scope175 :
    (CleanExpression.inputs native.expression175).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression175 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 175 (by decide +kernel) native.idealInputsBinding175

theorem native.scopeChunk10 :
    (native.expressionsChunk10).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
    native.expressionsChunk10)
    (BoolChecks.cons native.scope160
      (BoolChecks.cons native.scope161
        (BoolChecks.cons native.scope162
          (BoolChecks.cons native.scope163
            (BoolChecks.cons native.scope164
              (BoolChecks.cons native.scope165
                (BoolChecks.cons native.scope166
                  (BoolChecks.cons native.scope167
                    (BoolChecks.cons native.scope168
                      (BoolChecks.cons native.scope169
                        (BoolChecks.cons native.scope170
                          (BoolChecks.cons native.scope171
                            (BoolChecks.cons native.scope172
                              (BoolChecks.cons native.scope173
                                (BoolChecks.cons native.scope174
                                  (BoolChecks.cons native.scope175 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk10 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk10).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk10 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved160 base data holds)
        (PredicateChecks.cons (native.preserved161 base data holds)
          (PredicateChecks.cons (native.preserved162 base data holds)
            (PredicateChecks.cons (native.preserved163 base data holds)
              (PredicateChecks.cons (native.preserved164 base data holds)
                (PredicateChecks.cons (native.preserved165 base data holds)
                  (PredicateChecks.cons (native.preserved166 base data holds)
                    (PredicateChecks.cons (native.preserved167 base data holds)
                      (PredicateChecks.cons (native.preserved168 base data holds)
                        (PredicateChecks.cons (native.preserved169 base data holds)
                          (PredicateChecks.cons (native.preserved170 base data holds)
                            (PredicateChecks.cons (native.preserved171 base data holds)
                              (PredicateChecks.cons (native.preserved172 base data holds)
                                (PredicateChecks.cons (native.preserved173 base data holds)
                                  (PredicateChecks.cons (native.preserved174 base data holds)
                                    (PredicateChecks.cons (native.preserved175 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk11 : List (Airbender.Expression Source.BaseField) :=
  [native.expression176, native.expression177, native.expression178, native.expression179, native.expression180,
    native.expression181, native.expression182, native.expression183, native.expression184, native.expression185,
    native.expression186]

theorem native.scope176 :
    (CleanExpression.inputs native.expression176).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression176 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 176 (by decide +kernel) native.idealInputsBinding176

theorem native.scope177 :
    (CleanExpression.inputs native.expression177).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression177 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 177 (by decide +kernel) native.idealInputsBinding177

theorem native.scope178 :
    (CleanExpression.inputs native.expression178).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression178 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 178 (by decide +kernel) native.idealInputsBinding178

theorem native.scope179 :
    (CleanExpression.inputs native.expression179).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression179 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 179 (by decide +kernel) native.idealInputsBinding179

theorem native.scope180 :
    (CleanExpression.inputs native.expression180).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression180 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 180 (by decide +kernel) native.idealInputsBinding180

theorem native.scope181 :
    (CleanExpression.inputs native.expression181).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression181 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 181 (by decide +kernel) native.idealInputsBinding181

theorem native.scope182 :
    (CleanExpression.inputs native.expression182).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression182 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 182 (by decide +kernel) native.idealInputsBinding182

theorem native.scope183 :
    (CleanExpression.inputs native.expression183).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression183 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 183 (by decide +kernel) native.idealInputsBinding183

theorem native.scope184 :
    (CleanExpression.inputs native.expression184).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression184 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 184 (by decide +kernel) native.idealInputsBinding184

theorem native.scope185 :
    (CleanExpression.inputs native.expression185).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression185 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 185 (by decide +kernel) native.idealInputsBinding185

theorem native.scope186 :
    (CleanExpression.inputs native.expression186).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression186 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 186 (by decide +kernel) native.idealInputsBinding186

theorem native.scopeChunk11 :
    (native.expressionsChunk11).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
    native.expressionsChunk11)
    (BoolChecks.cons native.scope176
      (BoolChecks.cons native.scope177
        (BoolChecks.cons native.scope178
          (BoolChecks.cons native.scope179
            (BoolChecks.cons native.scope180
              (BoolChecks.cons native.scope181
                (BoolChecks.cons native.scope182
                  (BoolChecks.cons native.scope183
                    (BoolChecks.cons native.scope184
                      (BoolChecks.cons native.scope185 (BoolChecks.cons native.scope186 BoolChecks.nil)))))))))))
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
