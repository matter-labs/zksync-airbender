import Airbender.Import.GKRProtocol.Source

namespace Airbender.Compiler.Source
set_option warningAsError true

/-- Authored source fields, with explicit table selectors, decoder-mask packing
and zero padding. None of these fields are obtained from lowered equations. -/
inductive EncodedField where
  | input : LookupInput → EncodedField
  | table : LookupTable → EncodedField
  | familyMask : List Nat → EncodedField
  | zero

def EncodedField.value (values : Nat → BaseField) : EncodedField → BaseField
  | .input expression => expression.value values
  | .table selection => selection.value values
  | .familyMask bits => (bits.zipIdx.map (fun (wire, index) => (2 ^ index : BaseField) * values wire)).sum
  | .zero => 0

/-- Original source columns and history/setup inputs have separate domains.
Compiler-generated timestamp cells cannot be reclassified as original columns. -/
structure MemoryValues where
  original : Nat → BaseField
  readTimestamp : Nat → Fin 2 → BaseField
  initializationAddress : Fin 2 → BaseField
  teardownTimestamp : Nat → Fin 2 → BaseField
  teardownValue : Nat → Fin 2 → BaseField

structure MemoryPlacement (n : Nat) where
  original : Nat → Fin n
  readTimestamp : Nat → Fin 2 → Fin n
  initializationAddress : Fin 2 → Fin n
  teardownTimestamp : Nat → Fin 2 → Fin n
  teardownValue : Nat → Fin 2 → Fin n

def MemoryPlacement.project (placement : MemoryPlacement n) (values : Fin n → BaseField) : MemoryValues :=
  ⟨values ∘ placement.original, fun query limb => values (placement.readTimestamp query limb),
    fun limb => values (placement.initializationAddress limb),
    fun query limb => values (placement.teardownTimestamp query limb),
    fun query limb => values (placement.teardownValue query limb)⟩

inductive MemoryField where
  | input : LookupInput → MemoryField
  | readTimestamp : Nat → Fin 2 → MemoryField
  | initializationAddress : Fin 2 → MemoryField
  | teardownTimestamp : Nat → Fin 2 → MemoryField
  | teardownValue : Nat → Fin 2 → MemoryField
  | constant : Nat → MemoryField
  | add : MemoryField → MemoryField → MemoryField
  | scale : Nat → MemoryField → MemoryField
  | neg : MemoryField → MemoryField

def MemoryField.value (values : MemoryValues) : MemoryField → BaseField
  | .input expression => expression.value values.original
  | .readTimestamp query limb => values.readTimestamp query limb
  | .initializationAddress limb => values.initializationAddress limb
  | .teardownTimestamp query limb => values.teardownTimestamp query limb
  | .teardownValue query limb => values.teardownValue query limb
  | .constant scalar => scalar
  | .add left right => left.value values + right.value values
  | .scale scalar inner => scalar * inner.value values
  | .neg inner => -inner.value values

/-- Boolean subtraction borrows are witnesses, separate from original columns
and from memory-history inputs. -/
structure HelperValues where
  memory : MemoryValues
  borrow : Nat → BaseField

structure HelperPlacement (n : Nat) where
  memory : MemoryPlacement n
  borrow : Nat → Fin n

def HelperPlacement.project (placement : HelperPlacement n) (values : Fin n → BaseField) : HelperValues :=
  ⟨placement.memory.project values, values ∘ placement.borrow⟩

inductive HelperField where
  | memory : MemoryField → HelperField
  | borrow : Nat → HelperField
  | add : HelperField → HelperField → HelperField
  | scale : Nat → HelperField → HelperField
  | neg : HelperField → HelperField

def HelperField.value (values : HelperValues) : HelperField → BaseField
  | .memory field => field.value values.memory
  | .borrow index => values.borrow index
  | .add left right => left.value values + right.value values
  | .scale coefficient field => coefficient * field.value values
  | .neg field => -field.value values

end Airbender.Compiler.Source

namespace Airbender.Compiler

structure SourceLookupQuery where
  fields : List Source.EncodedField
  mask : Option Source.EncodedField

def SourceLookupQuery.weight [CommRing R] (query : SourceLookupQuery)
    (hom : Source.BaseField →+* R) (source : Nat → Source.BaseField) : R :=
  match query.mask with
  | none => 1
  | some field => hom (field.value source)

/-- A source request, retaining its weight separately from its field payload. -/
structure MaterializedQuery where
  fields : List Source.BaseField
  weight : Source.BaseField

def SourceLookupQuery.materialized (query : SourceLookupQuery) (source : Nat → Source.BaseField) : MaterializedQuery :=
  ⟨query.fields.map (fun field => field.value source), query.weight (RingHom.id _) source⟩

/-- Omit disabled requests while retaining every nonzero-weight emitted tuple.
Multiplicity soundness is stated at the exact tuple boundary above. -/
def activeLookupFields (queries : List MaterializedQuery) : List (List Source.BaseField) :=
  (queries.filter fun query => query.weight != 0).map MaterializedQuery.fields

end Airbender.Compiler
