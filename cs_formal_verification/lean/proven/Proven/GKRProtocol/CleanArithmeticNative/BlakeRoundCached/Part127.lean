module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part097
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part098
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part099
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part100
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part101
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part102
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part103
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part104
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part105
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part106
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part126
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

local instance generatedBatch127Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch127Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope151 :
    (CleanExpression.inputs native.expression151).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression151 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 151 (by decide +kernel) native.idealInputsBinding151

theorem native.scope152 :
    (CleanExpression.inputs native.expression152).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression152 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 152 (by decide +kernel) native.idealInputsBinding152

theorem native.scope153 :
    (CleanExpression.inputs native.expression153).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression153 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 153 (by decide +kernel) native.idealInputsBinding153

theorem native.scope154 :
    (CleanExpression.inputs native.expression154).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression154 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 154 (by decide +kernel) native.idealInputsBinding154

theorem native.scope155 :
    (CleanExpression.inputs native.expression155).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression155 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 155 (by decide +kernel) native.idealInputsBinding155

theorem native.scope156 :
    (CleanExpression.inputs native.expression156).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression156 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 156 (by decide +kernel) native.idealInputsBinding156

theorem native.scope157 :
    (CleanExpression.inputs native.expression157).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression157 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 157 (by decide +kernel) native.idealInputsBinding157

theorem native.scope158 :
    (CleanExpression.inputs native.expression158).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression158 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 158 (by decide +kernel) native.idealInputsBinding158

theorem native.scope159 :
    (CleanExpression.inputs native.expression159).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression159 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 159 (by decide +kernel) native.idealInputsBinding159

theorem native.scopeChunk9 :
    (native.expressionsChunk9).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
    native.expressionsChunk9)
    (BoolChecks.cons native.scope144
      (BoolChecks.cons native.scope145
        (BoolChecks.cons native.scope146
          (BoolChecks.cons native.scope147
            (BoolChecks.cons native.scope148
              (BoolChecks.cons native.scope149
                (BoolChecks.cons native.scope150
                  (BoolChecks.cons native.scope151
                    (BoolChecks.cons native.scope152
                      (BoolChecks.cons native.scope153
                        (BoolChecks.cons native.scope154
                          (BoolChecks.cons native.scope155
                            (BoolChecks.cons native.scope156
                              (BoolChecks.cons native.scope157
                                (BoolChecks.cons native.scope158
                                  (BoolChecks.cons native.scope159 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk9 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk9).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk9 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved144 base data holds)
        (PredicateChecks.cons (native.preserved145 base data holds)
          (PredicateChecks.cons (native.preserved146 base data holds)
            (PredicateChecks.cons (native.preserved147 base data holds)
              (PredicateChecks.cons (native.preserved148 base data holds)
                (PredicateChecks.cons (native.preserved149 base data holds)
                  (PredicateChecks.cons (native.preserved150 base data holds)
                    (PredicateChecks.cons (native.preserved151 base data holds)
                      (PredicateChecks.cons (native.preserved152 base data holds)
                        (PredicateChecks.cons (native.preserved153 base data holds)
                          (PredicateChecks.cons (native.preserved154 base data holds)
                            (PredicateChecks.cons (native.preserved155 base data holds)
                              (PredicateChecks.cons (native.preserved156 base data holds)
                                (PredicateChecks.cons (native.preserved157 base data holds)
                                  (PredicateChecks.cons (native.preserved158 base data holds)
                                    (PredicateChecks.cons (native.preserved159 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk10 : List (Airbender.Expression Source.BaseField) :=
  [native.expression160, native.expression161, native.expression162, native.expression163, native.expression164,
    native.expression165, native.expression166, native.expression167, native.expression168, native.expression169,
    native.expression170, native.expression171, native.expression172, native.expression173, native.expression174,
    native.expression175]

theorem native.scope160 :
    (CleanExpression.inputs native.expression160).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression160 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 160 (by decide +kernel) native.idealInputsBinding160

theorem native.scope161 :
    (CleanExpression.inputs native.expression161).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression161 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 161 (by decide +kernel) native.idealInputsBinding161

theorem native.scope162 :
    (CleanExpression.inputs native.expression162).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression162 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 162 (by decide +kernel) native.idealInputsBinding162

theorem native.scope163 :
    (CleanExpression.inputs native.expression163).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression163 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 163 (by decide +kernel) native.idealInputsBinding163

theorem native.scope164 :
    (CleanExpression.inputs native.expression164).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression164 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 164 (by decide +kernel) native.idealInputsBinding164

theorem native.scope165 :
    (CleanExpression.inputs native.expression165).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression165 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 165 (by decide +kernel) native.idealInputsBinding165

theorem native.scope166 :
    (CleanExpression.inputs native.expression166).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression166 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 166 (by decide +kernel) native.idealInputsBinding166

theorem native.scope167 :
    (CleanExpression.inputs native.expression167).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression167 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 167 (by decide +kernel) native.idealInputsBinding167

theorem native.scope168 :
    (CleanExpression.inputs native.expression168).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression168 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 168 (by decide +kernel) native.idealInputsBinding168

theorem native.scope169 :
    (CleanExpression.inputs native.expression169).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression169 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 169 (by decide +kernel) native.idealInputsBinding169

theorem native.scope170 :
    (CleanExpression.inputs native.expression170).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression170 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 170 (by decide +kernel) native.idealInputsBinding170

theorem native.scope171 :
    (CleanExpression.inputs native.expression171).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression171 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 171 (by decide +kernel) native.idealInputsBinding171
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
