module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part084
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part085
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part086
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part087
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part088
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part089
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part090
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part091
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part092
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

local instance generatedBatch93Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch93Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.scope134 :
    (CleanExpression.inputs native.expression134).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression134 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 134 (by decide +kernel) native.idealInputsBinding134

theorem native.scopeChunk8 :
    (native.expressionsChunk8).all
        (fun expression => (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  BoolChecks.all_true (predicate := fun expression =>
    (CleanExpression.inputs expression).all (fun index => decide (index < 276))) (items :=
    native.expressionsChunk8)
    (BoolChecks.cons native.scope128
      (BoolChecks.cons native.scope129
        (BoolChecks.cons native.scope130
          (BoolChecks.cons native.scope131
            (BoolChecks.cons native.scope132
              (BoolChecks.cons native.scope133 (BoolChecks.cons native.scope134 BoolChecks.nil)))))))

theorem native.arithmeticChunk8 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressionsChunk8).map FlatOperation.assert) :=
  CleanExpression.assertions_hold native.expressionsChunk8 (native.environment base data)
    (PredicateChecks.all
      (PredicateChecks.cons (native.preserved128 base data holds)
        (PredicateChecks.cons (native.preserved129 base data holds)
          (PredicateChecks.cons (native.preserved130 base data holds)
            (PredicateChecks.cons (native.preserved131 base data holds)
              (PredicateChecks.cons (native.preserved132 base data holds)
                (PredicateChecks.cons (native.preserved133 base data holds)
                  (PredicateChecks.cons (native.preserved134 base data holds) PredicateChecks.nil))))))))

noncomputable def native.expressions : List (Airbender.Expression Source.BaseField) :=
  native.expressionsChunk0 ++
    (native.expressionsChunk1 ++
      (native.expressionsChunk2 ++
        (native.expressionsChunk3 ++
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField))))))))))

theorem native.scopeChecked :
    ((native.expressions).all fun expression : Airbender.Expression Source.BaseField =>
        (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
      true :=
  all_append_true
    (fun expression : Airbender.Expression Source.BaseField =>
      (CleanExpression.inputs expression).all (fun index => decide (index < 276)))
    native.expressionsChunk0
    (native.expressionsChunk1 ++
      (native.expressionsChunk2 ++
        (native.expressionsChunk3 ++
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField))))))))))
    native.scopeChunk0
    (all_append_true
      (fun expression : Airbender.Expression Source.BaseField =>
        (CleanExpression.inputs expression).all (fun index => decide (index < 276)))
      native.expressionsChunk1
      (native.expressionsChunk2 ++
        (native.expressionsChunk3 ++
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField)))))))))
      native.scopeChunk1
      (all_append_true
        (fun expression : Airbender.Expression Source.BaseField =>
          (CleanExpression.inputs expression).all (fun index => decide (index < 276)))
        native.expressionsChunk2
        (native.expressionsChunk3 ++
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField))))))))
        native.scopeChunk2
        (all_append_true
          (fun expression : Airbender.Expression Source.BaseField =>
            (CleanExpression.inputs expression).all (fun index => decide (index < 276)))
          native.expressionsChunk3
          (native.expressionsChunk4 ++
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField)))))))
          native.scopeChunk3
          (all_append_true
            (fun expression : Airbender.Expression Source.BaseField =>
              (CleanExpression.inputs expression).all (fun index => decide (index < 276)))
            native.expressionsChunk4
            (native.expressionsChunk5 ++
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField))))))
            native.scopeChunk4
            (all_append_true
              (fun expression : Airbender.Expression Source.BaseField =>
                (CleanExpression.inputs expression).all (fun index => decide (index < 276)))
              native.expressionsChunk5
              (native.expressionsChunk6 ++
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField)))))
              native.scopeChunk5
              (all_append_true
                (fun expression : Airbender.Expression Source.BaseField =>
                  (CleanExpression.inputs expression).all (fun index => decide (index < 276)))
                native.expressionsChunk6
                (native.expressionsChunk7 ++
                  (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField))))
                native.scopeChunk6
                (all_append_true
                  (fun expression : Airbender.Expression Source.BaseField =>
                    (CleanExpression.inputs expression).all (fun index => decide (index < 276)))
                  native.expressionsChunk7
                  (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField)))
                  native.scopeChunk7
                  (all_append_true
                    (fun expression : Airbender.Expression Source.BaseField =>
                      (CleanExpression.inputs expression).all (fun index => decide (index < 276)))
                    native.expressionsChunk8 ([] : List (Airbender.Expression Source.BaseField)) native.scopeChunk8
                    (show
                      ((([] : List (Airbender.Expression Source.BaseField))).all
                          fun expression : Airbender.Expression Source.BaseField =>
                          (CleanExpression.inputs expression).all (fun index => decide (index < 276))) =
                        true
                      from rfl)))))))))

theorem native.arithmetic_preserved (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic :
      ∀ gate ∈ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact).gates,
        gate.expressionResidual (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address) =
          0) :
    FlatOperation.ConstraintsHoldFlat (native.environment base data)
      ((native.expressions).map FlatOperation.assert) :=
  by
  have holds := native.relations_hold base arithmetic
  exact
    CleanExpression.append_assertions_hold native.expressionsChunk0
      (native.expressionsChunk1 ++
        (native.expressionsChunk2 ++
          (native.expressionsChunk3 ++
            (native.expressionsChunk4 ++
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField))))))))))
      (native.environment base data) (native.arithmeticChunk0 base data holds)
      (CleanExpression.append_assertions_hold native.expressionsChunk1
        (native.expressionsChunk2 ++
          (native.expressionsChunk3 ++
            (native.expressionsChunk4 ++
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField)))))))))
        (native.environment base data) (native.arithmeticChunk1 base data holds)
        (CleanExpression.append_assertions_hold native.expressionsChunk2
          (native.expressionsChunk3 ++
            (native.expressionsChunk4 ++
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField))))))))
          (native.environment base data) (native.arithmeticChunk2 base data holds)
          (CleanExpression.append_assertions_hold native.expressionsChunk3
            (native.expressionsChunk4 ++
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField)))))))
            (native.environment base data) (native.arithmeticChunk3 base data holds)
            (CleanExpression.append_assertions_hold native.expressionsChunk4
              (native.expressionsChunk5 ++
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField))))))
              (native.environment base data) (native.arithmeticChunk4 base data holds)
              (CleanExpression.append_assertions_hold native.expressionsChunk5
                (native.expressionsChunk6 ++
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField)))))
                (native.environment base data) (native.arithmeticChunk5 base data holds)
                (CleanExpression.append_assertions_hold native.expressionsChunk6
                  (native.expressionsChunk7 ++
                    (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField))))
                  (native.environment base data) (native.arithmeticChunk6 base data holds)
                  (CleanExpression.append_assertions_hold native.expressionsChunk7
                    (native.expressionsChunk8 ++ ([] : List (Airbender.Expression Source.BaseField)))
                    (native.environment base data) (native.arithmeticChunk7 base data holds)
                    (CleanExpression.append_assertions_hold native.expressionsChunk8
                      ([] : List (Airbender.Expression Source.BaseField)) (native.environment base data)
                      (native.arithmeticChunk8 base data holds)
                      (show
                        FlatOperation.ConstraintsHoldFlat (native.environment base data)
                          (([] : List (Airbender.Expression Source.BaseField)).map FlatOperation.assert)
                        from by trivial)))))))))
end Airbender.Compiler.CleanArithmeticNative.BigintCached
