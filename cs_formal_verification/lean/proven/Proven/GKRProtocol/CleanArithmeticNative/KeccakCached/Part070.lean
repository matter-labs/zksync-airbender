module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part022
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part023
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part024
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part025
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part026
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part027
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part028
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part029
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part030
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part031
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part032
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part035
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part036
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part069
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

local instance generatedBatch70Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch70Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope47 :
    (CleanExpression.inputs native.expression47).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression47 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 47 (by decide +kernel) native.idealInputsBinding47

theorem native.scopeChunk2 :
    (native.expressionsChunk2).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
    native.expressionsChunk2)
    (BoolChecks.cons native.scope32
      (BoolChecks.cons native.scope33
        (BoolChecks.cons native.scope34
          (BoolChecks.cons native.scope35
            (BoolChecks.cons native.scope36
              (BoolChecks.cons native.scope37
                (BoolChecks.cons native.scope38
                  (BoolChecks.cons native.scope39
                    (BoolChecks.cons native.scope40
                      (BoolChecks.cons native.scope41
                        (BoolChecks.cons native.scope42
                          (BoolChecks.cons native.scope43
                            (BoolChecks.cons native.scope44
                              (BoolChecks.cons native.scope45
                                (BoolChecks.cons native.scope46
                                  (BoolChecks.cons native.scope47 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk2 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk2).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk2 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved32 base data holds)
        (PredicateChecks.cons (native.preserved33 base data holds)
          (PredicateChecks.cons (native.preserved34 base data holds)
            (PredicateChecks.cons (native.preserved35 base data holds)
              (PredicateChecks.cons (native.preserved36 base data holds)
                (PredicateChecks.cons (native.preserved37 base data holds)
                  (PredicateChecks.cons (native.preserved38 base data holds)
                    (PredicateChecks.cons (native.preserved39 base data holds)
                      (PredicateChecks.cons (native.preserved40 base data holds)
                        (PredicateChecks.cons (native.preserved41 base data holds)
                          (PredicateChecks.cons (native.preserved42 base data holds)
                            (PredicateChecks.cons (native.preserved43 base data holds)
                              (PredicateChecks.cons (native.preserved44 base data holds)
                                (PredicateChecks.cons (native.preserved45 base data holds)
                                  (PredicateChecks.cons (native.preserved46 base data holds)
                                    (PredicateChecks.cons (native.preserved47 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk3 : List (Airbender.Expression Source.BaseField) :=
  [native.expression48, native.expression49, native.expression50, native.expression51, native.expression52,
    native.expression53, native.expression54, native.expression55, native.expression56, native.expression57,
    native.expression58, native.expression59, native.expression60, native.expression61, native.expression62,
    native.expression63]

theorem native.scope48 :
    (CleanExpression.inputs native.expression48).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression48 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 48 (by decide +kernel) native.idealInputsBinding48

theorem native.scope49 :
    (CleanExpression.inputs native.expression49).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression49 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 49 (by decide +kernel) native.idealInputsBinding49

theorem native.scope50 :
    (CleanExpression.inputs native.expression50).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression50 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 50 (by decide +kernel) native.idealInputsBinding50

theorem native.scope51 :
    (CleanExpression.inputs native.expression51).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression51 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 51 (by decide +kernel) native.idealInputsBinding51

theorem native.scope52 :
    (CleanExpression.inputs native.expression52).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression52 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 52 (by decide +kernel) native.idealInputsBinding52

theorem native.scope53 :
    (CleanExpression.inputs native.expression53).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression53 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 53 (by decide +kernel) native.idealInputsBinding53

theorem native.scope54 :
    (CleanExpression.inputs native.expression54).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression54 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 54 (by decide +kernel) native.idealInputsBinding54

theorem native.scope55 :
    (CleanExpression.inputs native.expression55).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression55 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 55 (by decide +kernel) native.idealInputsBinding55

theorem native.scope56 :
    (CleanExpression.inputs native.expression56).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression56 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 56 (by decide +kernel) native.idealInputsBinding56

theorem native.scope57 :
    (CleanExpression.inputs native.expression57).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression57 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 57 (by decide +kernel) native.idealInputsBinding57

theorem native.scope58 :
    (CleanExpression.inputs native.expression58).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression58 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 58 (by decide +kernel) native.idealInputsBinding58

theorem native.scope59 :
    (CleanExpression.inputs native.expression59).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression59 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 59 (by decide +kernel) native.idealInputsBinding59

theorem native.scope60 :
    (CleanExpression.inputs native.expression60).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression60 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 60 (by decide +kernel) native.idealInputsBinding60

theorem native.scope61 :
    (CleanExpression.inputs native.expression61).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression61 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 61 (by decide +kernel) native.idealInputsBinding61

theorem native.scope62 :
    (CleanExpression.inputs native.expression62).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression62 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 62 (by decide +kernel) native.idealInputsBinding62

theorem native.scope63 :
    (CleanExpression.inputs native.expression63).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression63 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 63 (by decide +kernel) native.idealInputsBinding63

theorem native.scopeChunk3 :
    (native.expressionsChunk3).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression64).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression64 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 64 (by decide +kernel) native.idealInputsBinding64
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
