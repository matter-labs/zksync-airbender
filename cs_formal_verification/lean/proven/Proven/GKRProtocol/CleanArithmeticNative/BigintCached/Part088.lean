module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part035
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part036
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part037
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part038
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part039
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part040
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part041
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part042
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part043
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part044
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part045
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part046
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part047
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part048
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part049
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part050
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part051
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part052
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part053
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part054
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part055
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part056
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part057
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part058
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part059
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part060
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part061
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part062
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part063
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part064
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part065
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part087
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

local instance generatedBatch88Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch88Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope32 :
    (CleanExpression.inputs native.expression32).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression32 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 32 (by decide +kernel) native.idealInputsBinding32

theorem native.scope33 :
    (CleanExpression.inputs native.expression33).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression33 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 33 (by decide +kernel) native.idealInputsBinding33

theorem native.scope34 :
    (CleanExpression.inputs native.expression34).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression34 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 34 (by decide +kernel) native.idealInputsBinding34

theorem native.scope35 :
    (CleanExpression.inputs native.expression35).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression35 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 35 (by decide +kernel) native.idealInputsBinding35

theorem native.scope36 :
    (CleanExpression.inputs native.expression36).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression36 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 36 (by decide +kernel) native.idealInputsBinding36

theorem native.scope37 :
    (CleanExpression.inputs native.expression37).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression37 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 37 (by decide +kernel) native.idealInputsBinding37

theorem native.scope38 :
    (CleanExpression.inputs native.expression38).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression38 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 38 (by decide +kernel) native.idealInputsBinding38

theorem native.scope39 :
    (CleanExpression.inputs native.expression39).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression39 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 39 (by decide +kernel) native.idealInputsBinding39

theorem native.scope40 :
    (CleanExpression.inputs native.expression40).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression40 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 40 (by decide +kernel) native.idealInputsBinding40

theorem native.scope41 :
    (CleanExpression.inputs native.expression41).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression41 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 41 (by decide +kernel) native.idealInputsBinding41

theorem native.scope42 :
    (CleanExpression.inputs native.expression42).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression42 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 42 (by decide +kernel) native.idealInputsBinding42

theorem native.scope43 :
    (CleanExpression.inputs native.expression43).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression43 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 43 (by decide +kernel) native.idealInputsBinding43

theorem native.scope44 :
    (CleanExpression.inputs native.expression44).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression44 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 44 (by decide +kernel) native.idealInputsBinding44

theorem native.scope45 :
    (CleanExpression.inputs native.expression45).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression45 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 45 (by decide +kernel) native.idealInputsBinding45

theorem native.scope46 :
    (CleanExpression.inputs native.expression46).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression46 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 46 (by decide +kernel) native.idealInputsBinding46

theorem native.scope47 :
    (CleanExpression.inputs native.expression47).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression47 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 47 (by decide +kernel) native.idealInputsBinding47

theorem native.scopeChunk2 :
    (native.expressionsChunk2).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 276))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression48).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression48 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 48 (by decide +kernel) native.idealInputsBinding48

theorem native.scope49 :
    (CleanExpression.inputs native.expression49).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression49 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 49 (by decide +kernel) native.idealInputsBinding49

theorem native.scope50 :
    (CleanExpression.inputs native.expression50).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression50 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 50 (by decide +kernel) native.idealInputsBinding50

theorem native.scope51 :
    (CleanExpression.inputs native.expression51).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression51 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 51 (by decide +kernel) native.idealInputsBinding51

theorem native.scope52 :
    (CleanExpression.inputs native.expression52).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression52 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 52 (by decide +kernel) native.idealInputsBinding52
end Airbender.Compiler.CleanArithmeticNative.BigintCached
