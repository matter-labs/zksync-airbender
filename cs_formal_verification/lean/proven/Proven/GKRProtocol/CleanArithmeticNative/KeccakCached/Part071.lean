module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part032
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part035
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part036
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part037
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part038
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part039
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part040
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part070
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

local instance generatedBatch71Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch71Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope65 :
    (CleanExpression.inputs native.expression65).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression65 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 65 (by decide +kernel) native.idealInputsBinding65

theorem native.scope66 :
    (CleanExpression.inputs native.expression66).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression66 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 66 (by decide +kernel) native.idealInputsBinding66

theorem native.scope67 :
    (CleanExpression.inputs native.expression67).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression67 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 67 (by decide +kernel) native.idealInputsBinding67

theorem native.scope68 :
    (CleanExpression.inputs native.expression68).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression68 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 68 (by decide +kernel) native.idealInputsBinding68

theorem native.scope69 :
    (CleanExpression.inputs native.expression69).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression69 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 69 (by decide +kernel) native.idealInputsBinding69

theorem native.scope70 :
    (CleanExpression.inputs native.expression70).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression70 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 70 (by decide +kernel) native.idealInputsBinding70

theorem native.scope71 :
    (CleanExpression.inputs native.expression71).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression71 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 71 (by decide +kernel) native.idealInputsBinding71

theorem native.scope72 :
    (CleanExpression.inputs native.expression72).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression72 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 72 (by decide +kernel) native.idealInputsBinding72

theorem native.scope73 :
    (CleanExpression.inputs native.expression73).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression73 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 73 (by decide +kernel) native.idealInputsBinding73

theorem native.scope74 :
    (CleanExpression.inputs native.expression74).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression74 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 74 (by decide +kernel) native.idealInputsBinding74

theorem native.scope75 :
    (CleanExpression.inputs native.expression75).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression75 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 75 (by decide +kernel) native.idealInputsBinding75

theorem native.scope76 :
    (CleanExpression.inputs native.expression76).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression76 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 76 (by decide +kernel) native.idealInputsBinding76

theorem native.scope77 :
    (CleanExpression.inputs native.expression77).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression77 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 77 (by decide +kernel) native.idealInputsBinding77

theorem native.scope78 :
    (CleanExpression.inputs native.expression78).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression78 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 78 (by decide +kernel) native.idealInputsBinding78

theorem native.scope79 :
    (CleanExpression.inputs native.expression79).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression79 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 79 (by decide +kernel) native.idealInputsBinding79

theorem native.scopeChunk4 :
    (native.expressionsChunk4).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression80).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression80 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 80 (by decide +kernel) native.idealInputsBinding80

theorem native.scope81 :
    (CleanExpression.inputs native.expression81).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression81 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 81 (by decide +kernel) native.idealInputsBinding81

theorem native.scope82 :
    (CleanExpression.inputs native.expression82).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression82 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 82 (by decide +kernel) native.idealInputsBinding82

theorem native.scope83 :
    (CleanExpression.inputs native.expression83).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression83 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 83 (by decide +kernel) native.idealInputsBinding83

theorem native.scope84 :
    (CleanExpression.inputs native.expression84).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression84 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 84 (by decide +kernel) native.idealInputsBinding84

theorem native.scope85 :
    (CleanExpression.inputs native.expression85).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression85 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 85 (by decide +kernel) native.idealInputsBinding85
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
