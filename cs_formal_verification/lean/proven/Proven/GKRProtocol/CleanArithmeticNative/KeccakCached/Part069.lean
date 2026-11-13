module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part018
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part019
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part020
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part021
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part022
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part023
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part024
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part025
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part026
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part068
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

local instance generatedBatch69Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch69Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope26 :
    (CleanExpression.inputs native.expression26).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression26 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 26 (by decide +kernel) native.idealInputsBinding26

theorem native.scope27 :
    (CleanExpression.inputs native.expression27).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression27 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 27 (by decide +kernel) native.idealInputsBinding27

theorem native.scope28 :
    (CleanExpression.inputs native.expression28).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression28 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 28 (by decide +kernel) native.idealInputsBinding28

theorem native.scope29 :
    (CleanExpression.inputs native.expression29).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression29 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 29 (by decide +kernel) native.idealInputsBinding29

theorem native.scope30 :
    (CleanExpression.inputs native.expression30).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression30 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 30 (by decide +kernel) native.idealInputsBinding30

theorem native.scope31 :
    (CleanExpression.inputs native.expression31).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression31 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 31 (by decide +kernel) native.idealInputsBinding31

theorem native.scopeChunk1 :
    (native.expressionsChunk1).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 266))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 266))) (items :=
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
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
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
    (CleanExpression.inputs native.expression32).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression32 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 32 (by decide +kernel) native.idealInputsBinding32

theorem native.scope33 :
    (CleanExpression.inputs native.expression33).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression33 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 33 (by decide +kernel) native.idealInputsBinding33

theorem native.scope34 :
    (CleanExpression.inputs native.expression34).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression34 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 34 (by decide +kernel) native.idealInputsBinding34

theorem native.scope35 :
    (CleanExpression.inputs native.expression35).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression35 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 35 (by decide +kernel) native.idealInputsBinding35

theorem native.scope36 :
    (CleanExpression.inputs native.expression36).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression36 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 36 (by decide +kernel) native.idealInputsBinding36

theorem native.scope37 :
    (CleanExpression.inputs native.expression37).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression37 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 37 (by decide +kernel) native.idealInputsBinding37

theorem native.scope38 :
    (CleanExpression.inputs native.expression38).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression38 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 38 (by decide +kernel) native.idealInputsBinding38

theorem native.scope39 :
    (CleanExpression.inputs native.expression39).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression39 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 39 (by decide +kernel) native.idealInputsBinding39

theorem native.scope40 :
    (CleanExpression.inputs native.expression40).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression40 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 40 (by decide +kernel) native.idealInputsBinding40

theorem native.scope41 :
    (CleanExpression.inputs native.expression41).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression41 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 41 (by decide +kernel) native.idealInputsBinding41

theorem native.scope42 :
    (CleanExpression.inputs native.expression42).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression42 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 42 (by decide +kernel) native.idealInputsBinding42

theorem native.scope43 :
    (CleanExpression.inputs native.expression43).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression43 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 43 (by decide +kernel) native.idealInputsBinding43

theorem native.scope44 :
    (CleanExpression.inputs native.expression44).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression44 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 44 (by decide +kernel) native.idealInputsBinding44

theorem native.scope45 :
    (CleanExpression.inputs native.expression45).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression45 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 45 (by decide +kernel) native.idealInputsBinding45

theorem native.scope46 :
    (CleanExpression.inputs native.expression46).all (fun index => decide (index < 266)) = true :=
  CleanIdealChecks.scope_at native.expression46 Airbender.Compiler.CleanIdealNative.KeccakCached.capture
    Airbender.Compiler.CleanIdealNative.KeccakCached.checked 46 (by decide +kernel) native.idealInputsBinding46
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
