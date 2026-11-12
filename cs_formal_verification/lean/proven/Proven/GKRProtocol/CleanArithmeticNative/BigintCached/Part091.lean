module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part070
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part071
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part072
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part073
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part074
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part075
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part076
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part077
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part078
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part079
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part080
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part081
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part082
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part083
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part084
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part090
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

local instance generatedBatch91Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch91Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope95 :
    (CleanExpression.inputs native.expression95).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression95 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 95 (by decide +kernel) native.idealInputsBinding95

theorem native.scopeChunk5 :
    (native.expressionsChunk5).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 276))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression96).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression96 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 96 (by decide +kernel) native.idealInputsBinding96

theorem native.scope97 :
    (CleanExpression.inputs native.expression97).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression97 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 97 (by decide +kernel) native.idealInputsBinding97

theorem native.scope98 :
    (CleanExpression.inputs native.expression98).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression98 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 98 (by decide +kernel) native.idealInputsBinding98

theorem native.scope99 :
    (CleanExpression.inputs native.expression99).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression99 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 99 (by decide +kernel) native.idealInputsBinding99

theorem native.scope100 :
    (CleanExpression.inputs native.expression100).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression100 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 100 (by decide +kernel) native.idealInputsBinding100

theorem native.scope101 :
    (CleanExpression.inputs native.expression101).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression101 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 101 (by decide +kernel) native.idealInputsBinding101

theorem native.scope102 :
    (CleanExpression.inputs native.expression102).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression102 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 102 (by decide +kernel) native.idealInputsBinding102

theorem native.scope103 :
    (CleanExpression.inputs native.expression103).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression103 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 103 (by decide +kernel) native.idealInputsBinding103

theorem native.scope104 :
    (CleanExpression.inputs native.expression104).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression104 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 104 (by decide +kernel) native.idealInputsBinding104

theorem native.scope105 :
    (CleanExpression.inputs native.expression105).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression105 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 105 (by decide +kernel) native.idealInputsBinding105

theorem native.scope106 :
    (CleanExpression.inputs native.expression106).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression106 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 106 (by decide +kernel) native.idealInputsBinding106

theorem native.scope107 :
    (CleanExpression.inputs native.expression107).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression107 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 107 (by decide +kernel) native.idealInputsBinding107

theorem native.scope108 :
    (CleanExpression.inputs native.expression108).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression108 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 108 (by decide +kernel) native.idealInputsBinding108

theorem native.scope109 :
    (CleanExpression.inputs native.expression109).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression109 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 109 (by decide +kernel) native.idealInputsBinding109

theorem native.scope110 :
    (CleanExpression.inputs native.expression110).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression110 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 110 (by decide +kernel) native.idealInputsBinding110

theorem native.scope111 :
    (CleanExpression.inputs native.expression111).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression111 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 111 (by decide +kernel) native.idealInputsBinding111

theorem native.scopeChunk6 :
    (native.expressionsChunk6).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 276))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression112).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression112 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 112 (by decide +kernel) native.idealInputsBinding112
end Airbender.Compiler.CleanArithmeticNative.BigintCached
