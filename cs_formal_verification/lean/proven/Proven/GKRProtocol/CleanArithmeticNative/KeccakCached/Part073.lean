module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part041
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part042
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part043
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part044
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part045
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part046
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part047
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part048
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part049
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part050
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part072
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

local instance generatedBatch73Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch73Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope107 :
    (CleanExpression.inputs native.expression107).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression107 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 107 (by decide +kernel) native.idealInputsBinding107

theorem native.scope108 :
    (CleanExpression.inputs native.expression108).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression108 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 108 (by decide +kernel) native.idealInputsBinding108

theorem native.scope109 :
    (CleanExpression.inputs native.expression109).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression109 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 109 (by decide +kernel) native.idealInputsBinding109

theorem native.scope110 :
    (CleanExpression.inputs native.expression110).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression110 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 110 (by decide +kernel) native.idealInputsBinding110

theorem native.scope111 :
    (CleanExpression.inputs native.expression111).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression111 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 111 (by decide +kernel) native.idealInputsBinding111

theorem native.scopeChunk6 :
    (native.expressionsChunk6).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression112).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression112 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 112 (by decide +kernel) native.idealInputsBinding112

theorem native.scope113 :
    (CleanExpression.inputs native.expression113).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression113 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 113 (by decide +kernel) native.idealInputsBinding113

theorem native.scope114 :
    (CleanExpression.inputs native.expression114).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression114 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 114 (by decide +kernel) native.idealInputsBinding114

theorem native.scope115 :
    (CleanExpression.inputs native.expression115).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression115 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 115 (by decide +kernel) native.idealInputsBinding115

theorem native.scope116 :
    (CleanExpression.inputs native.expression116).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression116 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 116 (by decide +kernel) native.idealInputsBinding116

theorem native.scope117 :
    (CleanExpression.inputs native.expression117).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression117 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 117 (by decide +kernel) native.idealInputsBinding117

theorem native.scope118 :
    (CleanExpression.inputs native.expression118).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression118 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 118 (by decide +kernel) native.idealInputsBinding118

theorem native.scope119 :
    (CleanExpression.inputs native.expression119).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression119 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 119 (by decide +kernel) native.idealInputsBinding119

theorem native.scope120 :
    (CleanExpression.inputs native.expression120).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression120 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 120 (by decide +kernel) native.idealInputsBinding120

theorem native.scope121 :
    (CleanExpression.inputs native.expression121).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression121 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 121 (by decide +kernel) native.idealInputsBinding121

theorem native.scope122 :
    (CleanExpression.inputs native.expression122).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression122 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 122 (by decide +kernel) native.idealInputsBinding122

theorem native.scope123 :
    (CleanExpression.inputs native.expression123).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression123 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 123 (by decide +kernel) native.idealInputsBinding123

theorem native.scope124 :
    (CleanExpression.inputs native.expression124).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression124 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 124 (by decide +kernel) native.idealInputsBinding124

theorem native.scope125 :
    (CleanExpression.inputs native.expression125).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression125 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 125 (by decide +kernel) native.idealInputsBinding125

theorem native.scope126 :
    (CleanExpression.inputs native.expression126).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression126 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 126 (by decide +kernel) native.idealInputsBinding126

theorem native.scope127 :
    (CleanExpression.inputs native.expression127).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression127 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 127 (by decide +kernel) native.idealInputsBinding127
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
