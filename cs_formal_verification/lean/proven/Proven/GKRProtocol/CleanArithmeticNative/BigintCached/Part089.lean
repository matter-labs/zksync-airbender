module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part061
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part062
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part063
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part064
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part065
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part066
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part067
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part068
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part069
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part070
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part088
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

local instance generatedBatch89Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch89Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope53 :
    (CleanExpression.inputs native.expression53).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression53 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 53 (by decide +kernel) native.idealInputsBinding53

theorem native.scope54 :
    (CleanExpression.inputs native.expression54).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression54 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 54 (by decide +kernel) native.idealInputsBinding54

theorem native.scope55 :
    (CleanExpression.inputs native.expression55).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression55 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 55 (by decide +kernel) native.idealInputsBinding55

theorem native.scope56 :
    (CleanExpression.inputs native.expression56).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression56 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 56 (by decide +kernel) native.idealInputsBinding56

theorem native.scope57 :
    (CleanExpression.inputs native.expression57).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression57 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 57 (by decide +kernel) native.idealInputsBinding57

theorem native.scope58 :
    (CleanExpression.inputs native.expression58).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression58 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 58 (by decide +kernel) native.idealInputsBinding58

theorem native.scope59 :
    (CleanExpression.inputs native.expression59).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression59 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 59 (by decide +kernel) native.idealInputsBinding59

theorem native.scope60 :
    (CleanExpression.inputs native.expression60).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression60 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 60 (by decide +kernel) native.idealInputsBinding60

theorem native.scope61 :
    (CleanExpression.inputs native.expression61).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression61 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 61 (by decide +kernel) native.idealInputsBinding61

theorem native.scope62 :
    (CleanExpression.inputs native.expression62).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression62 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 62 (by decide +kernel) native.idealInputsBinding62

theorem native.scope63 :
    (CleanExpression.inputs native.expression63).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression63 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 63 (by decide +kernel) native.idealInputsBinding63

theorem native.scopeChunk3 :
    (native.expressionsChunk3).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 276))) (items :=
    native.expressionsChunk3)
    (BoolChecks.cons native.scope48
      (BoolChecks.cons native.scope49
        (BoolChecks.cons native.scope50
          (BoolChecks.cons native.scope51
            (BoolChecks.cons native.scope52
              (BoolChecks.cons native.scope53
                (BoolChecks.cons native.scope54
                  (BoolChecks.cons native.scope55
                    (BoolChecks.cons native.scope56
                      (BoolChecks.cons native.scope57
                        (BoolChecks.cons native.scope58
                          (BoolChecks.cons native.scope59
                            (BoolChecks.cons native.scope60
                              (BoolChecks.cons native.scope61
                                (BoolChecks.cons native.scope62
                                  (BoolChecks.cons native.scope63 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk3 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk3).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk3 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved48 base data holds)
        (PredicateChecks.cons (native.preserved49 base data holds)
          (PredicateChecks.cons (native.preserved50 base data holds)
            (PredicateChecks.cons (native.preserved51 base data holds)
              (PredicateChecks.cons (native.preserved52 base data holds)
                (PredicateChecks.cons (native.preserved53 base data holds)
                  (PredicateChecks.cons (native.preserved54 base data holds)
                    (PredicateChecks.cons (native.preserved55 base data holds)
                      (PredicateChecks.cons (native.preserved56 base data holds)
                        (PredicateChecks.cons (native.preserved57 base data holds)
                          (PredicateChecks.cons (native.preserved58 base data holds)
                            (PredicateChecks.cons (native.preserved59 base data holds)
                              (PredicateChecks.cons (native.preserved60 base data holds)
                                (PredicateChecks.cons (native.preserved61 base data holds)
                                  (PredicateChecks.cons (native.preserved62 base data holds)
                                    (PredicateChecks.cons (native.preserved63 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk4 : List (Airbender.Expression Source.BaseField) :=
  [native.expression64, native.expression65, native.expression66, native.expression67, native.expression68,
    native.expression69, native.expression70, native.expression71, native.expression72, native.expression73,
    native.expression74, native.expression75, native.expression76, native.expression77, native.expression78,
    native.expression79]

theorem native.scope64 :
    (CleanExpression.inputs native.expression64).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression64 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 64 (by decide +kernel) native.idealInputsBinding64

theorem native.scope65 :
    (CleanExpression.inputs native.expression65).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression65 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 65 (by decide +kernel) native.idealInputsBinding65

theorem native.scope66 :
    (CleanExpression.inputs native.expression66).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression66 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 66 (by decide +kernel) native.idealInputsBinding66

theorem native.scope67 :
    (CleanExpression.inputs native.expression67).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression67 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 67 (by decide +kernel) native.idealInputsBinding67

theorem native.scope68 :
    (CleanExpression.inputs native.expression68).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression68 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 68 (by decide +kernel) native.idealInputsBinding68

theorem native.scope69 :
    (CleanExpression.inputs native.expression69).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression69 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 69 (by decide +kernel) native.idealInputsBinding69

theorem native.scope70 :
    (CleanExpression.inputs native.expression70).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression70 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 70 (by decide +kernel) native.idealInputsBinding70

theorem native.scope71 :
    (CleanExpression.inputs native.expression71).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression71 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 71 (by decide +kernel) native.idealInputsBinding71

theorem native.scope72 :
    (CleanExpression.inputs native.expression72).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression72 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 72 (by decide +kernel) native.idealInputsBinding72

theorem native.scope73 :
    (CleanExpression.inputs native.expression73).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression73 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 73 (by decide +kernel) native.idealInputsBinding73
end Airbender.Compiler.CleanArithmeticNative.BigintCached
