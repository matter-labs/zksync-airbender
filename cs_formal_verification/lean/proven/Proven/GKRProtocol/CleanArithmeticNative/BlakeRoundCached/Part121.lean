module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part039
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part040
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part041
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part042
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part043
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part044
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part045
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part046
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part047
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part048
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part049
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part050
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part051
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part052
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part120
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

local instance generatedBatch121Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch121Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope31 :
    (CleanExpression.inputs native.expression31).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression31 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 31 (by decide +kernel) native.idealInputsBinding31

theorem native.scopeChunk1 :
    (native.expressionsChunk1).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
    native.expressionsChunk1)
    (BoolChecks.cons native.scope16
      (BoolChecks.cons native.scope17
        (BoolChecks.cons native.scope18
          (BoolChecks.cons native.scope19
            (BoolChecks.cons native.scope20
              (BoolChecks.cons native.scope21
                (BoolChecks.cons native.scope22
                  (BoolChecks.cons native.scope23
                    (BoolChecks.cons native.scope24
                      (BoolChecks.cons native.scope25
                        (BoolChecks.cons native.scope26
                          (BoolChecks.cons native.scope27
                            (BoolChecks.cons native.scope28
                              (BoolChecks.cons native.scope29
                                (BoolChecks.cons native.scope30
                                  (BoolChecks.cons native.scope31 BoolChecks.nil))))))))))))))))

theorem native.arithmeticChunk1 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk1).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk1 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved16 base data holds)
        (PredicateChecks.cons (native.preserved17 base data holds)
          (PredicateChecks.cons (native.preserved18 base data holds)
            (PredicateChecks.cons (native.preserved19 base data holds)
              (PredicateChecks.cons (native.preserved20 base data holds)
                (PredicateChecks.cons (native.preserved21 base data holds)
                  (PredicateChecks.cons (native.preserved22 base data holds)
                    (PredicateChecks.cons (native.preserved23 base data holds)
                      (PredicateChecks.cons (native.preserved24 base data holds)
                        (PredicateChecks.cons (native.preserved25 base data holds)
                          (PredicateChecks.cons (native.preserved26 base data holds)
                            (PredicateChecks.cons (native.preserved27 base data holds)
                              (PredicateChecks.cons (native.preserved28 base data holds)
                                (PredicateChecks.cons (native.preserved29 base data holds)
                                  (PredicateChecks.cons (native.preserved30 base data holds)
                                    (PredicateChecks.cons (native.preserved31 base data holds)
                                      PredicateChecks.nil)))))))))))))))))

noncomputable def native.expressionsChunk2 : List (Airbender.Expression Source.BaseField) :=
  [native.expression32, native.expression33, native.expression34, native.expression35, native.expression36,
    native.expression37, native.expression38, native.expression39, native.expression40, native.expression41,
    native.expression42, native.expression43, native.expression44, native.expression45, native.expression46,
    native.expression47]

theorem native.scope32 :
    (CleanExpression.inputs native.expression32).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression32 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 32 (by decide +kernel) native.idealInputsBinding32

theorem native.scope33 :
    (CleanExpression.inputs native.expression33).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression33 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 33 (by decide +kernel) native.idealInputsBinding33

theorem native.scope34 :
    (CleanExpression.inputs native.expression34).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression34 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 34 (by decide +kernel) native.idealInputsBinding34

theorem native.scope35 :
    (CleanExpression.inputs native.expression35).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression35 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 35 (by decide +kernel) native.idealInputsBinding35

theorem native.scope36 :
    (CleanExpression.inputs native.expression36).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression36 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 36 (by decide +kernel) native.idealInputsBinding36

theorem native.scope37 :
    (CleanExpression.inputs native.expression37).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression37 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 37 (by decide +kernel) native.idealInputsBinding37

theorem native.scope38 :
    (CleanExpression.inputs native.expression38).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression38 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 38 (by decide +kernel) native.idealInputsBinding38

theorem native.scope39 :
    (CleanExpression.inputs native.expression39).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression39 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 39 (by decide +kernel) native.idealInputsBinding39

theorem native.scope40 :
    (CleanExpression.inputs native.expression40).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression40 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 40 (by decide +kernel) native.idealInputsBinding40

theorem native.scope41 :
    (CleanExpression.inputs native.expression41).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression41 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 41 (by decide +kernel) native.idealInputsBinding41

theorem native.scope42 :
    (CleanExpression.inputs native.expression42).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression42 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 42 (by decide +kernel) native.idealInputsBinding42

theorem native.scope43 :
    (CleanExpression.inputs native.expression43).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression43 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 43 (by decide +kernel) native.idealInputsBinding43

theorem native.scope44 :
    (CleanExpression.inputs native.expression44).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression44 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 44 (by decide +kernel) native.idealInputsBinding44

theorem native.scope45 :
    (CleanExpression.inputs native.expression45).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression45 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 45 (by decide +kernel) native.idealInputsBinding45

theorem native.scope46 :
    (CleanExpression.inputs native.expression46).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression46 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 46 (by decide +kernel) native.idealInputsBinding46

theorem native.scope47 :
    (CleanExpression.inputs native.expression47).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression47 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 47 (by decide +kernel) native.idealInputsBinding47

theorem native.scopeChunk2 :
    (native.expressionsChunk2).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 763))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 763))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression48).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression48 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 48 (by decide +kernel) native.idealInputsBinding48
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
