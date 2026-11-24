module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part048
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part049
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part050
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part051
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part052
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part053
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part054
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part055
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part056
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part057
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part058
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part059
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part060
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part121
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

local instance generatedBatch122Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch122Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope49 :
    (CleanExpression.inputs native.expression49).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression49 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 49 (by decide +kernel) native.idealInputsBinding49

theorem native.scope50 :
    (CleanExpression.inputs native.expression50).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression50 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 50 (by decide +kernel) native.idealInputsBinding50

theorem native.scope51 :
    (CleanExpression.inputs native.expression51).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression51 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 51 (by decide +kernel) native.idealInputsBinding51

theorem native.scope52 :
    (CleanExpression.inputs native.expression52).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression52 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 52 (by decide +kernel) native.idealInputsBinding52

theorem native.scope53 :
    (CleanExpression.inputs native.expression53).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression53 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 53 (by decide +kernel) native.idealInputsBinding53

theorem native.scope54 :
    (CleanExpression.inputs native.expression54).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression54 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 54 (by decide +kernel) native.idealInputsBinding54

theorem native.scope55 :
    (CleanExpression.inputs native.expression55).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression55 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 55 (by decide +kernel) native.idealInputsBinding55

theorem native.scope56 :
    (CleanExpression.inputs native.expression56).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression56 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 56 (by decide +kernel) native.idealInputsBinding56

theorem native.scope57 :
    (CleanExpression.inputs native.expression57).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression57 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 57 (by decide +kernel) native.idealInputsBinding57

theorem native.scope58 :
    (CleanExpression.inputs native.expression58).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression58 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 58 (by decide +kernel) native.idealInputsBinding58

theorem native.scope59 :
    (CleanExpression.inputs native.expression59).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression59 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 59 (by decide +kernel) native.idealInputsBinding59

theorem native.scope60 :
    (CleanExpression.inputs native.expression60).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression60 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 60 (by decide +kernel) native.idealInputsBinding60

theorem native.scope61 :
    (CleanExpression.inputs native.expression61).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression61 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 61 (by decide +kernel) native.idealInputsBinding61

theorem native.scope62 :
    (CleanExpression.inputs native.expression62).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression62 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 62 (by decide +kernel) native.idealInputsBinding62

theorem native.scope63 :
    (CleanExpression.inputs native.expression63).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression63 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 63 (by decide +kernel) native.idealInputsBinding63

theorem native.scopeChunk3 :
    (native.expressionsChunk3).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression64).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression64 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 64 (by decide +kernel) native.idealInputsBinding64

theorem native.scope65 :
    (CleanExpression.inputs native.expression65).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression65 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 65 (by decide +kernel) native.idealInputsBinding65

theorem native.scope66 :
    (CleanExpression.inputs native.expression66).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression66 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 66 (by decide +kernel) native.idealInputsBinding66

theorem native.scope67 :
    (CleanExpression.inputs native.expression67).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression67 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 67 (by decide +kernel) native.idealInputsBinding67

theorem native.scope68 :
    (CleanExpression.inputs native.expression68).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression68 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 68 (by decide +kernel) native.idealInputsBinding68

theorem native.scope69 :
    (CleanExpression.inputs native.expression69).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression69 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 69 (by decide +kernel) native.idealInputsBinding69
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
