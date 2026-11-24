module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part065
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part066
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part067
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part068
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part069
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part070
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part071
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part072
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part073
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part074
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part089
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

local instance generatedBatch90Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch90Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope74 :
    (CleanExpression.inputs native.expression74).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression74 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 74 (by decide +kernel) native.idealInputsBinding74

theorem native.scope75 :
    (CleanExpression.inputs native.expression75).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression75 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 75 (by decide +kernel) native.idealInputsBinding75

theorem native.scope76 :
    (CleanExpression.inputs native.expression76).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression76 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 76 (by decide +kernel) native.idealInputsBinding76

theorem native.scope77 :
    (CleanExpression.inputs native.expression77).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression77 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 77 (by decide +kernel) native.idealInputsBinding77

theorem native.scope78 :
    (CleanExpression.inputs native.expression78).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression78 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 78 (by decide +kernel) native.idealInputsBinding78

theorem native.scope79 :
    (CleanExpression.inputs native.expression79).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression79 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 79 (by decide +kernel) native.idealInputsBinding79

theorem native.scopeChunk4 :
    (native.expressionsChunk4).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 276))) (items :=
    native.expressionsChunk4)
    (BoolChecks.cons native.scope64
      (BoolChecks.cons native.scope65
        (BoolChecks.cons native.scope66
          (BoolChecks.cons native.scope67
            (BoolChecks.cons native.scope68
              (BoolChecks.cons native.scope69
                (BoolChecks.cons native.scope70
                  (BoolChecks.cons native.scope71
                    (BoolChecks.cons native.scope72
                      (BoolChecks.cons native.scope73
                        (BoolChecks.cons native.scope74
                          (BoolChecks.cons native.scope75
                            (BoolChecks.cons native.scope76
                              (BoolChecks.cons native.scope77
                                (BoolChecks.cons native.scope78
                                  (BoolChecks.cons native.scope79 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk4 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk4).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk4 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved64 base data holds)
        (PredicateChecks.cons (native.preserved65 base data holds)
          (PredicateChecks.cons (native.preserved66 base data holds)
            (PredicateChecks.cons (native.preserved67 base data holds)
              (PredicateChecks.cons (native.preserved68 base data holds)
                (PredicateChecks.cons (native.preserved69 base data holds)
                  (PredicateChecks.cons (native.preserved70 base data holds)
                    (PredicateChecks.cons (native.preserved71 base data holds)
                      (PredicateChecks.cons (native.preserved72 base data holds)
                        (PredicateChecks.cons (native.preserved73 base data holds)
                          (PredicateChecks.cons (native.preserved74 base data holds)
                            (PredicateChecks.cons (native.preserved75 base data holds)
                              (PredicateChecks.cons (native.preserved76 base data holds)
                                (PredicateChecks.cons (native.preserved77 base data holds)
                                  (PredicateChecks.cons (native.preserved78 base data holds)
                                    (PredicateChecks.cons (native.preserved79 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk5 : List (Airbender.Expression Source.BaseField) :=
  [native.expression80, native.expression81, native.expression82, native.expression83, native.expression84,
    native.expression85, native.expression86, native.expression87, native.expression88, native.expression89,
    native.expression90, native.expression91, native.expression92, native.expression93, native.expression94,
    native.expression95]

theorem native.scope80 :
    (CleanExpression.inputs native.expression80).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression80 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 80 (by decide +kernel) native.idealInputsBinding80

theorem native.scope81 :
    (CleanExpression.inputs native.expression81).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression81 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 81 (by decide +kernel) native.idealInputsBinding81

theorem native.scope82 :
    (CleanExpression.inputs native.expression82).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression82 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 82 (by decide +kernel) native.idealInputsBinding82

theorem native.scope83 :
    (CleanExpression.inputs native.expression83).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression83 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 83 (by decide +kernel) native.idealInputsBinding83

theorem native.scope84 :
    (CleanExpression.inputs native.expression84).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression84 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 84 (by decide +kernel) native.idealInputsBinding84

theorem native.scope85 :
    (CleanExpression.inputs native.expression85).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression85 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 85 (by decide +kernel) native.idealInputsBinding85

theorem native.scope86 :
    (CleanExpression.inputs native.expression86).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression86 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 86 (by decide +kernel) native.idealInputsBinding86

theorem native.scope87 :
    (CleanExpression.inputs native.expression87).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression87 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 87 (by decide +kernel) native.idealInputsBinding87

theorem native.scope88 :
    (CleanExpression.inputs native.expression88).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression88 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 88 (by decide +kernel) native.idealInputsBinding88

theorem native.scope89 :
    (CleanExpression.inputs native.expression89).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression89 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 89 (by decide +kernel) native.idealInputsBinding89

theorem native.scope90 :
    (CleanExpression.inputs native.expression90).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression90 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 90 (by decide +kernel) native.idealInputsBinding90

theorem native.scope91 :
    (CleanExpression.inputs native.expression91).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression91 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 91 (by decide +kernel) native.idealInputsBinding91

theorem native.scope92 :
    (CleanExpression.inputs native.expression92).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression92 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 92 (by decide +kernel) native.idealInputsBinding92

theorem native.scope93 :
    (CleanExpression.inputs native.expression93).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression93 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 93 (by decide +kernel) native.idealInputsBinding93

theorem native.scope94 :
    (CleanExpression.inputs native.expression94).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression94 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 94 (by decide +kernel) native.idealInputsBinding94
end Airbender.Compiler.CleanArithmeticNative.BigintCached
