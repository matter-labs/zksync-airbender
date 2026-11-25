module
public import Human.Import.Exec.Proth120Native
public import Human.Circuits.UnifiedReduced.Proth120Clock
public import Human.Helpers.Decoder.Program

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Compiler.Proth120Native

import_proth120_native gates placements nativeQueries from "../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"

abbrev F := ZMod proth120Modulus
def nativeScalar (raw : Nat) : F := CircuitField.decode proth120Modulus raw

/-- Every sparse quadratic gate in the cached layout holds at its physical wires.
    Logical witness columns agree with the layout's physical placements. -/
def NativeArithmetic (physical : GKRAddress → F) (logical : Nat → F) : Prop :=
  (∀ g ∈ gates, Gate.Holds nativeScalar physical g) ∧
  ∀ kv ∈ placements, logical kv.1 = physical kv.2

/-- Every structured equation of the Proth120 logical row. -/
def EquationsHold (logical : Nat → F) : Prop :=
  ∀ (setup : Table F (fields 10)) e, FlatOperation.assert e ∈ importedConstraints setup →
    e.eval (Verification.environment logical) = 0

/-- Native quadratic gates and placements imply all the unified row's structured equations. -/
def NativeArithmeticClaim : Prop :=
  ∀ physical logical, NativeArithmetic physical logical → EquationsHold logical

/-- A physical and logical assignment jointly satisfy the native arithmetic premises. -/
def NativeArithmeticSatisfiableClaim : Prop :=
  ∃ physical logical, NativeArithmetic physical logical

/-- Public interpretation of the single generic setup chain. A zero mask at column 8
    selects an ordinary pooled row. A tag of 46 selects a public program row. -/
structure PublicLookupRows (setup : Table F (fields 10)) (decode : Vector F 9 → Prop) where
  generic : List F → Prop
  pooled : ∀ v : Vector F 10, generic v.toList → v[8] = 0 → setup.Contains #[] v
  decoder : ∀ v, generic (v.toList ++ [46]) → decode v

/-- Exact membership of every enabled, uncompressed native operand in its public output
    group. This is the lookup-argument interface; hashing and challenge compression lie outside it. -/
def NativeLookupsMatched (publicRows : List F → Prop) (physical : GKRAddress → F) : Prop :=
  ∀ q ∈ nativeQueries, (q.enable.map physical).getD 1 ≠ 0 →
    let xs := q.fields.map (value nativeScalar physical)
    match q.group with
    | 0 => publicRows xs
    | 1 => ∃ x : Fin 65536, xs = [(x.val : F)]
    | 2 => ∃ x : Fin Trace.timestampBase, xs = [(x.val : F)]
    | _ => False

/-- Native arithmetic and exact physical lookup operands imply every equation, range,
    pooled and clock lookup. An active row also issues the claimed public decoder query. -/
def NativeRowClaim : Prop :=
  ∀ (setup : Table F (fields 10)) (decode : Vector F 9 → Prop) (rows : PublicLookupRows setup decode)
    physical logical, NativeArithmetic physical logical → NativeLookupsMatched rows.generic physical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (clockConstraints setup) ∧
      (logical importedConstraintsTraceColumns.execute = 1 →
        decode (Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns logical))

def NativeRowSatisfiableClaim : Prop :=
  ∃ (setup : Table F (fields 10)) (decode : Vector F 9 → Prop) (rows : PublicLookupRows setup decode)
    (physical : GKRAddress → F) (logical : Nat → F), NativeArithmetic physical logical ∧ NativeLookupsMatched rows.generic physical ∧
      logical importedConstraintsTraceColumns.execute = 1

end Airbender.UnifiedReduced.Proth120
