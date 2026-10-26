import Airbender.Proofs.GKRProtocol.SourceFields
import Airbender.Proofs.GKRProtocol.CacheBindings

namespace Airbender.Compiler.Source
set_option warningAsError true

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

def MemoryField.polynomial (placement : MemoryPlacement n) : MemoryField → Compiler.Polynomial n BaseField
  | .input expression => expression.polynomial placement.original
  | .readTimestamp query limb => Compiler.atom (placement.readTimestamp query limb)
  | .initializationAddress limb => Compiler.atom (placement.initializationAddress limb)
  | .teardownTimestamp query limb => Compiler.atom (placement.teardownTimestamp query limb)
  | .teardownValue query limb => Compiler.atom (placement.teardownValue query limb)
  | .constant scalar => Compiler.constant scalar
  | .add left right => Compiler.add (left.polynomial placement) (right.polynomial placement)
  | .scale scalar inner => Compiler.multiply (Compiler.constant scalar) (inner.polynomial placement)
  | .neg inner => Compiler.negate (inner.polynomial placement)

theorem MemoryField.polynomial_value (field : MemoryField) (placement : MemoryPlacement n)
    (values : Fin n → BaseField) :
    Compiler.evaluate values (field.polynomial placement) = field.value (placement.project values) := by
  induction field with
  | input expression => exact expression.polynomial_value placement.original values
  | readTimestamp query limb => exact Compiler.evaluate_atom _ _
  | initializationAddress limb => exact Compiler.evaluate_atom _ _
  | teardownTimestamp query limb => exact Compiler.evaluate_atom _ _
  | teardownValue query limb => exact Compiler.evaluate_atom _ _
  | constant scalar => exact Compiler.evaluate_constant _ _
  | add left right leftProof rightProof => simpa only [polynomial, value, Compiler.evaluate_add] using congrArg₂ (· + ·) leftProof rightProof
  | scale scalar input proof => simpa only [polynomial, value, Compiler.evaluate_multiply, Compiler.evaluate_constant] using congrArg ((scalar : BaseField) * ·) proof
  | neg input proof => simpa only [polynomial, value, Compiler.evaluate_negate] using congrArg Neg.neg proof

def MemoryField.originalIndices : MemoryField → List Nat
  | .input (.Variable index) => [index]
  | .input (.Expression terms _) => terms.toList.map (·.2)
  | .add left right => left.originalIndices ++ right.originalIndices
  | .scale _ inner | .neg inner => inner.originalIndices
  | .readTimestamp _ _ | .initializationAddress _ | .teardownTimestamp _ _ | .teardownValue _ _ | .constant _ => []

def MemoryField.referencesValid (originalVariables historySlots teardownSlots : Nat) (hasInitialization : Bool) : MemoryField → Bool
  | .input (.Variable index) => index < originalVariables
  | .input (.Expression terms _) => terms.all (fun term => term.2 < originalVariables)
  | .readTimestamp query _ => query < historySlots
  | .initializationAddress _ => hasInitialization
  | .teardownTimestamp query _ | .teardownValue query _ => query < teardownSlots
  | .constant _ => true
  | .add left right => referencesValid originalVariables historySlots teardownSlots hasInitialization left &&
      referencesValid originalVariables historySlots teardownSlots hasInitialization right
  | .scale _ inner | .neg inner => referencesValid originalVariables historySlots teardownSlots hasInitialization inner

structure MemoryWord where
  low : MemoryField
  high : MemoryField

def MemoryWord.zero : MemoryWord := ⟨.constant 0, .constant 0⟩

def MemoryWord.original (columns : Fixed 2 Nat) : MemoryWord :=
  ⟨.input (.Variable columns.values[0]!), .input (.Variable columns.values[1]!)⟩

def MemoryWord.history (query : Nat) : MemoryWord :=
  ⟨.readTimestamp query ⟨0, by decide⟩, .readTimestamp query ⟨1, by decide⟩⟩

def MemoryWord.offset (word : MemoryWord) (offset : Nat) : MemoryWord :=
  ⟨.add word.low (.constant offset), word.high⟩

def MemoryWord.representation : RamWordRepresentation → MemoryWord
  | .Zero => zero
  | .U16Limbs columns => original columns
  | .U8Limbs columns =>
      ⟨.add (.input (.Variable columns.values[0]!)) (.scale 256 (.input (.Variable columns.values[1]!))),
       .add (.input (.Variable columns.values[2]!)) (.scale 256 (.input (.Variable columns.values[3]!)))⟩

structure MemoryRow where
  addressSpace : MemoryField
  address : MemoryWord
  timestamp : MemoryWord
  data : MemoryWord

def MemoryRow.fields (row : MemoryRow) : List MemoryField :=
  [row.addressSpace, row.address.low, row.address.high, row.timestamp.low, row.timestamp.high, row.data.low, row.data.high]

def MemoryRow.fingerprint [CommRing R] (row : MemoryRow) (values : MemoryValues)
    (hom : BaseField →+* R) (challenges : Compiler.CacheChallenges R) : R :=
  challenges.memoryGamma + hom (row.addressSpace.value values) +
    challenges.memoryPowers ⟨0, by decide⟩ * hom (row.address.low.value values) +
    challenges.memoryPowers ⟨1, by decide⟩ * hom (row.address.high.value values) +
    challenges.memoryPowers ⟨2, by decide⟩ * hom (row.timestamp.low.value values) +
    challenges.memoryPowers ⟨3, by decide⟩ * hom (row.timestamp.high.value values) +
    challenges.memoryPowers ⟨4, by decide⟩ * hom (row.data.low.value values) +
    challenges.memoryPowers ⟨5, by decide⟩ * hom (row.data.high.value values)

def MemoryRow.originalIndices (row : MemoryRow) : List Nat := row.fields.flatMap MemoryField.originalIndices

end Airbender.Compiler.Source
