module
import all Mathlib.Data.List.Sort
public import Human.Compiler.NativeMemory
public import Proven.GKRProtocol.NativeProduct
public import Proven.GKRProtocol.BaseEncoding
public import Mathlib.Tactic.Ring

@[expose] public section
set_option warningAsError true

/-! Lean forms of the native cache and product recipes. They build the same payload trees as the
memory and product import commands, so the kernel compares them with the imported lists of each
capture. The semantic lemmas relate these payloads to the extension semantics of `NativeMemory`. -/

namespace Airbender.Compiler.NativeMemoryBridge
open NativeArithmetic NativeMemory

/-- One memory-bank input. -/
abbrev memoryInput (offset : Nat) : LookupPayload := .input (.BaseLayerMemory offset)

/-- An affine relation, in its native term order. -/
def linearProgram (row : LinearRelation) : LookupPayload :=
  row.linear_terms.toList.foldl (fun result term => .add result (.scale (.base term.1.raw.val) (.input term.2)))
    (.constant (.base row.constant.raw.val))

/-- The alpha-weighted sum of programs, in column order. -/
def foldPrograms (programs : List LookupPayload) : LookupPayload :=
  programs.zipIdx.foldl (fun result entry => .add result (.scale (.lookupPower entry.2) entry.1))
    (.constant (.natural 0))

def vectorProgram (row : VectorLookupRelation) : LookupPayload :=
  foldPrograms (row.columns.toList.map linearProgram)

def setupProgram (addresses : Array GKRAddress) : LookupPayload :=
  foldPrograms (addresses.toList.map .input)

def addressSpaceProgram : CompiledAddressSpaceRelationStrict → LookupPayload
  | .Constant value => .constant (.natural value.val)
  | .IsRam offset => memoryInput offset
  | .IsRegister offset => .add (.constant (.natural 1)) (.scale .negativeOne (memoryInput offset))

def addressProgram (result : LookupPayload) : CompiledAddressStrict → Option LookupPayload
  | .ConstantU16 value => some (.add result (.scale (.memoryPower 0) (.constant (.natural value.val))))
  | .Constant value => some (.add result (.scale (.memoryPower 0) (.constant (.natural value.val))))
  | .U16Space offset => some (.add result (.scale (.memoryPower 0) (memoryInput offset)))
  | .U32Space offsets => match offsets.values.toList with
    | [low, high] => some (.add (.add result (.scale (.memoryPower 0) (memoryInput low)))
        (.scale (.memoryPower 1) (memoryInput high)))
    | _ => none
  | .U32SpaceSpecialIndirect base dynamic offset high =>
    let withBase := AffineProgram.add (.add result (.scale (.memoryPower 0) (memoryInput base)))
      (.scale (.memoryPower 1) (memoryInput high))
    let withDynamic := match dynamic with
      | none => withBase
      | some (scale, input) => .add withBase (.scale (.memoryPower 0) (.scale (.natural scale.val) (memoryInput input)))
    some (.add withDynamic (.scale (.memoryPower 0) (.constant (.natural offset.val))))
  | .U32SpaceGeneric _ => none

def timestampProgram (offset : U32) (result : LookupPayload) : CompiledMemoryTimestamp → Option LookupPayload
  | .Zero => some result
  | .Normal limbs => match limbs.values.toList with
    | [low, high] => some (.add (.add result (.scale (.memoryPower 2)
        (.add (memoryInput low) (.constant (.natural offset.val))))) (.scale (.memoryPower 3) (memoryInput high)))
    | _ => none

def valueProgram (result : LookupPayload) : RamWordRepresentation → Option LookupPayload
  | .Zero => some result
  | .U16Limbs limbs => match limbs.values.toList with
    | [low, high] => some (.add (.add result (.scale (.memoryPower 4) (memoryInput low)))
        (.scale (.memoryPower 5) (memoryInput high)))
    | _ => none
  | .U8Limbs bytes => match bytes.values.toList with
    | [first, second, third, fourth] => some (.add
        (.add result (.scale (.memoryPower 4) (.add (memoryInput first) (.scale (.natural 256) (memoryInput second)))))
        (.scale (.memoryPower 5) (.add (memoryInput third) (.scale (.natural 256) (memoryInput fourth)))))
    | _ => none

def tupleProgram (row : SpecialMemoryContributionRelation) : Option LookupPayload := do
  let withAddress ← addressProgram (.add (.constant .memoryGamma) (addressSpaceProgram row.address_space)) row.address
  let withTimestamp ← timestampProgram row.timestamp_offset withAddress row.timestamp
  valueProgram withTimestamp row.value

def cacheProgram : GKRCacheRelation → Option LookupPayload
  | .SingleColumnLookup row _ => some (linearProgram row.input)
  | .MemoryTuple row => tupleProgram row
  | .VectorizedLookup row => some (vectorProgram row)
  | .VectorizedLookupSetup addresses => some (setupProgram addresses)

def gateDefinition : GKRRelation → Option AffineDefinition
  | .CopyInBaseField input output | .CopyInExtensionField input output => some ⟨output, .input input⟩
  | .MaterializeSingleLookupInput row output _ => some ⟨output, linearProgram row.input⟩
  | .MaterializedVectorLookupInput row output => some ⟨output, vectorProgram row⟩
  | _ => none

/-- All gates of all layers, in native order. -/
def layerGates (circuit : Circuit) : List GateArtifacts :=
  circuit.layers.toList.flatMap fun layer => (layer.gates ++ layer.gates_with_external_connections).toList

/-- All caches of all layers, in native order. -/
def layerCaches (circuit : Circuit) : List (GKRAddress × GKRCacheRelation) :=
  circuit.layers.toList.flatMap fun layer => layer.cached_relations.toList

/-- Every cache, then every copy and materialization gate, as affine definitions. -/
def definitionPrograms (circuit : Circuit) : List AffineDefinition :=
  (layerCaches circuit).filterMap (fun entry => (cacheProgram entry.2).map (AffineDefinition.mk entry.1)) ++
    (layerGates circuit).filterMap fun gate => gateDefinition gate.enforced_relation

def memoryCaches (circuit : Circuit) : List GKRAddress :=
  (layerCaches circuit).filterMap fun entry => match entry.2 with
    | .MemoryTuple _ => some entry.1
    | _ => none

def productGate (caches : List GKRAddress) : GKRRelation → Option NativeProductGate
  | .InitialGrandProductFromCaches input output => match input.values.toList with
    | [left, right] => some (.pair output (.input left) (.input right))
    | _ => none
  | .InitialGrandProductWithoutCaches input output => match input.values.toList with
    | [left, right] => do some (.pair output (← tupleProgram left) (← tupleProgram right))
    | _ => none
  | .MaterializeGrandProductTermExpression input output => (tupleProgram input).map (.single output)
  | .CopyInExtensionField input output =>
    if caches.contains input then some (.single output (.input input)) else some (.copy output input)
  | .TrivialProduct input output => match input.values.toList with
    | [left, right] => some (.mul output left right)
    | _ => none
  | .MaskIntoIdentityProduct input predicate output => some (.mask output input predicate)
  | _ => none

/-- Every RAM-product gate of the circuit, in native order. -/
def productGates (circuit : Circuit) : List NativeProductGate :=
  (layerGates circuit).filterMap fun gate => productGate (memoryCaches circuit) gate.enforced_relation

/-! Field roles that the semantic lemmas need. The kernel evaluates them for each capture. -/

/-- The base-field roles of a checked consumer typing. -/
def baseRoles (typing : ConsumerTyping) (address : GKRAddress) : Bool := typing.compatible (address, .base)

/-- Base-layer, setup and virtual setup wires are base-field wires. The supplied roles classify the
    inner and cached wires. -/
def isBase (roles : GKRAddress → Bool) (address : GKRAddress) : Bool :=
  match address with
  | .BaseLayerWitness _ | .BaseLayerMemory _ | .Setup _ | .VirtualSetup _ => true
  | .InnerLayer _ _ | .Cached _ _ => roles address
  | .ScratchSpace _ => false

def linearTyped (roles : GKRAddress → Bool) (row : LinearRelation) : Bool :=
  row.linear_terms.toList.all fun term => isBase roles term.2

def cacheTyped (roles : GKRAddress → Bool) (output : GKRAddress) : GKRCacheRelation → Bool
  | .SingleColumnLookup row _ => isBase roles output && linearTyped roles row.input
  | .MemoryTuple row => !isBase roles output && (tupleProgram row).isSome
  | .VectorizedLookup row => !isBase roles output && row.columns.toList.all (linearTyped roles)
  | .VectorizedLookupSetup addresses => !isBase roles output && addresses.toList.all (isBase roles)

def gateTyped (roles : GKRAddress → Bool) : GKRRelation → Bool
  | .CopyInBaseField input output => isBase roles output && isBase roles input
  | .CopyInExtensionField input output => !isBase roles output && !isBase roles input
  | .MaterializeSingleLookupInput row output _ => isBase roles output && linearTyped roles row.input
  | .MaterializedVectorLookupInput row output => !isBase roles output && row.columns.toList.all (linearTyped roles)
  | .InitialGrandProductFromCaches input output =>
    !isBase roles output && input.values.toList.all fun address => !isBase roles address
  | .InitialGrandProductWithoutCaches input output =>
    !isBase roles output && input.values.toList.all fun row => (tupleProgram row).isSome
  | .MaterializeGrandProductTermExpression input output => !isBase roles output && (tupleProgram input).isSome
  | .TrivialProduct input output => !isBase roles output && input.values.toList.all fun address => !isBase roles address
  | .MaskIntoIdentityProduct input predicate output =>
    !isBase roles output && !isBase roles input && isBase roles predicate
  | _ => true

/-- Field roles of the caches and gates in the RAM bridge. -/
def typingChecked (roles : GKRAddress → Bool) (circuit : Circuit) : Bool :=
  (layerCaches circuit).all (fun entry => cacheTyped roles entry.1 entry.2) &&
    (layerGates circuit).all fun gate => gateTyped roles gate.enforced_relation

/-! Semantics. -/

variable {R : Type} [CommRing R]

def cacheChallenges (challenges : NativeMemory.Challenges R) : CacheChallenges R :=
  ⟨challenges.lookupAlpha, challenges.memory.additive, challenges.memory.weights⟩

/-- Base wires read `physical`; extension wires read `values`. -/
def wires (challenges : NativeMemory.Challenges R) (roles : GKRAddress → Bool) (physical : GKRAddress → F)
    (values : GKRAddress → R) (address : GKRAddress) : R :=
  if isBase roles address then challenges.memory.embed (physical address) else values address

/-- The roles of a checked consumer typing classify every wire as the typing does. -/
theorem isBase_baseRoles (typing : ConsumerTyping) (address : GKRAddress) :
    isBase (baseRoles typing) address = typing.compatible (address, .base) := by
  cases address <;> rfl

/-- The wires of a checked consumer typing are its typed assignment. -/
theorem wires_typed (challenges : NativeMemory.Challenges R) (typing : ConsumerTyping)
    (physical : GKRAddress → F) (values : GKRAddress → R) :
    wires challenges (baseRoles typing) physical values =
      (⟨physical, values⟩ : TypedAssignment R).value typing challenges.memory.embed := by
  funext address
  cases address <;> rfl

theorem fixed_two {α : Type} (pair : Fixed 2 α) : ∃ left right, pair.values.toList = [left, right] := by
  have size : pair.values.toList.length = 2 := by simpa using pair.size_eq
  exact List.length_eq_two.mp size

theorem fixed_four {α : Type} (bytes : Fixed 4 α) :
    ∃ first second third fourth, bytes.values.toList = [first, second, third, fourth] := by
  have size : bytes.values.toList.length = 4 := by simpa using bytes.size_eq
  match bytes.values.toList, size with
  | [first, second, third, fourth], _ => exact ⟨first, second, third, fourth, rfl⟩

section Semantics
variable (challenges : NativeMemory.Challenges R) (roles : GKRAddress → Bool) (physical : GKRAddress → F)
  (values : GKRAddress → R)

theorem wires_base {address : GKRAddress} (base : isBase roles address = true) :
    wires challenges roles physical values address = challenges.embed (physical address) := by
  simp only [wires, base, ↓reduceIte]
  rfl

theorem wires_extension {address : GKRAddress} (extension : isBase roles address = false) :
    wires challenges roles physical values address = values address := by
  simp only [wires, extension, Bool.false_eq_true, ↓reduceIte]

theorem wires_memory (offset : Nat) :
    wires challenges roles physical values (.BaseLayerMemory offset) = challenges.column physical offset :=
  wires_base challenges roles physical values rfl

@[simp] theorem interpret_constant (scalar : CacheCoefficient) (hom : Source.BaseField →+* R)
    (cache : CacheChallenges R) (input : GKRAddress → R) :
    LookupPayload.interpret (AffineProgram.constant scalar) hom cache input = scalar.value hom cache := rfl

@[simp] theorem interpret_input (address : GKRAddress) (hom : Source.BaseField →+* R)
    (cache : CacheChallenges R) (input : GKRAddress → R) :
    LookupPayload.interpret (AffineProgram.input address) hom cache input = input address := rfl

@[simp] theorem interpret_add (left right : LookupPayload) (hom : Source.BaseField →+* R)
    (cache : CacheChallenges R) (input : GKRAddress → R) :
    LookupPayload.interpret (AffineProgram.add left right) hom cache input =
      left.interpret hom cache input + right.interpret hom cache input := rfl

@[simp] theorem interpret_scale (scalar : CacheCoefficient) (inner : LookupPayload) (hom : Source.BaseField →+* R)
    (cache : CacheChallenges R) (input : GKRAddress → R) :
    LookupPayload.interpret (AffineProgram.scale scalar inner) hom cache input =
      scalar.value hom cache * inner.interpret hom cache input := rfl


@[simp] theorem coefficient_natural (scalar : Nat) (hom : Source.BaseField →+* R) (cache : CacheChallenges R) :
    (CacheCoefficient.natural scalar).value hom cache = hom (scalar : F) := rfl

@[simp] theorem coefficient_base (raw : Nat) (hom : Source.BaseField →+* R) (cache : CacheChallenges R) :
    (CacheCoefficient.base raw).value hom cache = hom ((raw : F) * (montgomeryInverse : F)) := rfl

@[simp] theorem coefficient_memoryPower (index : Fin 6) (hom : Source.BaseField →+* R) (cache : CacheChallenges R) :
    (CacheCoefficient.memoryPower index).value hom cache = cache.memoryPowers index := rfl

@[simp] theorem coefficient_lookupPower (index : Nat) (hom : Source.BaseField →+* R) (cache : CacheChallenges R) :
    (CacheCoefficient.lookupPower index).value hom cache = cache.lookupAlpha ^ index := rfl

@[simp] theorem coefficient_memoryGamma (hom : Source.BaseField →+* R) (cache : CacheChallenges R) :
    CacheCoefficient.memoryGamma.value hom cache = cache.memoryGamma := rfl

@[simp] theorem coefficient_negativeOne (hom : Source.BaseField →+* R) (cache : CacheChallenges R) :
    CacheCoefficient.negativeOne.value hom cache = -1 := rfl

@[simp] theorem cacheChallenges_memoryPowers :
    (cacheChallenges challenges).memoryPowers = challenges.memory.weights := rfl

@[simp] theorem cacheChallenges_memoryGamma :
    (cacheChallenges challenges).memoryGamma = challenges.memory.additive := rfl

@[simp] theorem cacheChallenges_lookupAlpha :
    (cacheChallenges challenges).lookupAlpha = challenges.lookupAlpha := rfl

theorem linear_interpret (row : LinearRelation) (typed : linearTyped roles row = true) :
    LookupPayload.interpret (linearProgram row) challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) = challenges.embed (linear row physical) := by
  unfold linearProgram linear
  rw [← Array.foldl_toList]
  have terms := List.all_eq_true.mp typed
  have start : LookupPayload.interpret (AffineProgram.constant (CacheCoefficient.base row.constant.raw.val) : LookupPayload) challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) =
      challenges.embed (coefficient row.constant) := rfl
  revert terms start
  generalize row.linear_terms.toList = list
  generalize (AffineProgram.constant (CacheCoefficient.base row.constant.raw.val) : LookupPayload) = initial
  generalize coefficient row.constant = initialValue
  induction list generalizing initial initialValue with
  | nil => intro _ start; exact start
  | cons term rest proof =>
    obtain ⟨scalar, address⟩ := term
    intro terms start
    simp only [List.foldl_cons]
    apply proof
    · intro other member
      exact terms other (List.mem_cons_of_mem _ member)
    · have base : isBase roles address = true := terms (scalar, address) List.mem_cons_self
      simp only [interpret_add, interpret_scale, interpret_input, start, coefficient_base,
        wires_base challenges roles physical values base, Challenges.embed, coefficient, map_add, map_mul]

theorem foldPrograms_interpret (programs : List LookupPayload) (results : List F)
    (same : List.Forall₂ (fun program result => LookupPayload.interpret program challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) = challenges.embed result) programs results) :
    LookupPayload.interpret (foldPrograms programs) challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) = fold challenges results := by
  unfold foldPrograms fold
  have start : LookupPayload.interpret (AffineProgram.constant (CacheCoefficient.natural 0) : LookupPayload) challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) = 0 := by
    simp
  suffices general : ∀ (offset : Nat) (initial : LookupPayload),
      LookupPayload.interpret ((programs.zipIdx offset).foldl
        (fun result entry => .add result (.scale (.lookupPower entry.2) entry.1)) initial) challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) =
      LookupPayload.interpret initial challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) + ((results.zipIdx offset).map fun (column, index) =>
        challenges.lookupAlpha ^ index * challenges.embed column).sum by
    rw [general 0 _, start, zero_add]
  induction same with
  | nil => intro offset initial; simp
  | @cons program result programs results head tail proof =>
    intro offset initial
    simp only [List.zipIdx_cons, List.foldl_cons, List.map_cons, List.sum_cons]
    rw [proof (offset + 1) _]
    simp only [interpret_add, interpret_scale, coefficient_lookupPower, cacheChallenges_lookupAlpha, head]
    ring

theorem vector_interpret (row : VectorLookupRelation) (typed : row.columns.toList.all (linearTyped roles) = true) :
    LookupPayload.interpret (vectorProgram row) challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) = fold challenges (row.columns.toList.map fun column => linear column physical) := by
  unfold vectorProgram
  apply foldPrograms_interpret
  have columns := List.all_eq_true.mp typed
  revert columns
  generalize row.columns.toList = list
  induction list with
  | nil => intro _; exact List.Forall₂.nil
  | cons column rest proof =>
    intro columns
    exact List.Forall₂.cons (linear_interpret challenges roles physical values column (columns column List.mem_cons_self))
      (proof fun other member => columns other (List.mem_cons_of_mem _ member))

theorem setup_interpret (addresses : Array GKRAddress) (typed : addresses.toList.all (isBase roles) = true) :
    LookupPayload.interpret (setupProgram addresses) challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) = fold challenges (addresses.toList.map physical) := by
  unfold setupProgram
  apply foldPrograms_interpret
  have members := List.all_eq_true.mp typed
  revert members
  generalize addresses.toList = list
  induction list with
  | nil => intro _; exact List.Forall₂.nil
  | cons address rest proof =>
    intro members
    exact List.Forall₂.cons (by
        simp only [interpret_input]
        exact wires_base challenges roles physical values (members address List.mem_cons_self))
      (proof fun other member => members other (List.mem_cons_of_mem _ member))

theorem addressSpace_interpret (space : CompiledAddressSpaceRelationStrict) :
    LookupPayload.interpret (addressSpaceProgram space) challenges.memory.embed (cacheChallenges challenges)
      (wires challenges roles physical values) = addressSpace challenges physical space := by
  cases space with
  | Constant value => rfl
  | IsRam offset => exact wires_memory challenges roles physical values offset
  | IsRegister offset =>
    simp only [addressSpaceProgram, addressSpace, interpret_add, interpret_scale, interpret_constant,
      interpret_input, coefficient_natural, coefficient_negativeOne, wires_memory, Nat.cast_one, map_one]
    ring

theorem address_interpret (start : LookupPayload) (word : CompiledAddressStrict) :
    (addressProgram start word).map (fun program => LookupPayload.interpret program challenges.memory.embed
      (cacheChallenges challenges) (wires challenges roles physical values)) =
      (address challenges physical word).map (LookupPayload.interpret start challenges.memory.embed
        (cacheChallenges challenges) (wires challenges roles physical values) + ·) := by
  cases word with
  | ConstantU16 value =>
    simp only [addressProgram, address, Option.map_some, interpret_add, interpret_scale, interpret_constant,
      coefficient_memoryPower, coefficient_natural, cacheChallenges_memoryPowers, Challenges.embed]
  | Constant value =>
    simp only [addressProgram, address, Option.map_some, interpret_add, interpret_scale, interpret_constant,
      coefficient_memoryPower, coefficient_natural, cacheChallenges_memoryPowers, Challenges.embed]
  | U16Space offset =>
    simp only [addressProgram, address, Option.map_some, interpret_add, interpret_scale, interpret_input,
      coefficient_memoryPower, cacheChallenges_memoryPowers, wires_memory]
  | U32Space offsets =>
    obtain ⟨low, high, pair⟩ := fixed_two offsets
    simp only [addressProgram, address, pair, Option.map_some, interpret_add, interpret_scale, interpret_input,
      coefficient_memoryPower, cacheChallenges_memoryPowers, wires_memory, Option.some.injEq]
    ring
  | U32SpaceSpecialIndirect base dynamic offset high =>
    cases dynamic with
    | none =>
      simp only [addressProgram, address, Option.map_some, interpret_add, interpret_scale, interpret_input,
        interpret_constant, coefficient_memoryPower, coefficient_natural, cacheChallenges_memoryPowers,
        wires_memory, Challenges.embed, Option.some.injEq]
      ring
    | some entry =>
      obtain ⟨scale, input⟩ := entry
      simp only [addressProgram, address, Option.map_some, interpret_add, interpret_scale, interpret_input,
        interpret_constant, coefficient_memoryPower, coefficient_natural, cacheChallenges_memoryPowers,
        wires_memory, Challenges.embed, Option.some.injEq]
      ring
  | U32SpaceGeneric _ => rfl

theorem timestamp_interpret (offset : U32) (start : LookupPayload) (time : CompiledMemoryTimestamp) :
    (timestampProgram offset start time).map (fun program => LookupPayload.interpret program challenges.memory.embed
      (cacheChallenges challenges) (wires challenges roles physical values)) =
      (timestamp challenges physical offset time).map (LookupPayload.interpret start challenges.memory.embed
        (cacheChallenges challenges) (wires challenges roles physical values) + ·) := by
  cases time with
  | Zero => simp only [timestampProgram, timestamp, Option.map_some, add_zero]
  | Normal limbs =>
    obtain ⟨low, high, pair⟩ := fixed_two limbs
    simp only [timestampProgram, timestamp, pair, Option.map_some, interpret_add, interpret_scale,
      interpret_input, interpret_constant, coefficient_memoryPower, coefficient_natural,
      cacheChallenges_memoryPowers, wires_memory, Challenges.embed, Option.some.injEq]
    ring

theorem value_interpret (start : LookupPayload) (word : RamWordRepresentation) :
    (valueProgram start word).map (fun program => LookupPayload.interpret program challenges.memory.embed
      (cacheChallenges challenges) (wires challenges roles physical values)) =
      (value challenges physical word).map (LookupPayload.interpret start challenges.memory.embed
        (cacheChallenges challenges) (wires challenges roles physical values) + ·) := by
  cases word with
  | Zero => simp only [valueProgram, value, Option.map_some, add_zero]
  | U16Limbs limbs =>
    obtain ⟨low, high, pair⟩ := fixed_two limbs
    simp only [valueProgram, value, pair, Option.map_some, interpret_add, interpret_scale, interpret_input,
      coefficient_memoryPower, cacheChallenges_memoryPowers, wires_memory, Option.some.injEq]
    ring
  | U8Limbs bytes =>
    obtain ⟨first, second, third, fourth, quad⟩ := fixed_four bytes
    simp only [valueProgram, value, quad, Option.map_some, interpret_add, interpret_scale, interpret_input,
      coefficient_memoryPower, coefficient_natural, cacheChallenges_memoryPowers, wires_memory,
      Challenges.embed, Option.some.injEq, Nat.cast_ofNat]
    ring

theorem tuple_interpret (row : SpecialMemoryContributionRelation) :
    (tupleProgram row).map (fun program => LookupPayload.interpret program challenges.memory.embed
      (cacheChallenges challenges) (wires challenges roles physical values)) = tuple challenges physical row := by
  have start : LookupPayload.interpret (.add (.constant .memoryGamma) (addressSpaceProgram row.address_space))
      challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) =
      challenges.memory.additive + addressSpace challenges physical row.address_space := by
    rw [interpret_add, addressSpace_interpret challenges roles physical values]
    rfl
  have addressSame := address_interpret challenges roles physical values
    (.add (.constant .memoryGamma) (addressSpaceProgram row.address_space)) row.address
  unfold tupleProgram tuple
  cases humanAddress : address challenges physical row.address with
  | none =>
    rw [humanAddress, Option.map_none] at addressSame
    simp [Option.map_eq_none_iff.mp addressSame]
  | some addressTerm =>
    rw [humanAddress, Option.map_some] at addressSame
    obtain ⟨withAddress, foundAddress, valueAddress⟩ := Option.map_eq_some_iff.mp addressSame
    have timeSame := timestamp_interpret challenges roles physical values row.timestamp_offset withAddress
      row.timestamp
    cases humanTime : timestamp challenges physical row.timestamp_offset row.timestamp with
    | none =>
      rw [humanTime, Option.map_none] at timeSame
      simp [foundAddress, Option.map_eq_none_iff.mp timeSame]
    | some timeTerm =>
      rw [humanTime, Option.map_some] at timeSame
      obtain ⟨withTime, foundTime, valueTime⟩ := Option.map_eq_some_iff.mp timeSame
      have valueSame := value_interpret challenges roles physical values withTime row.value
      cases humanValue : value challenges physical row.value with
      | none =>
        rw [humanValue, Option.map_none] at valueSame
        simp [foundAddress, foundTime, Option.map_eq_none_iff.mp valueSame]
      | some valueTerm =>
        rw [humanValue, Option.map_some] at valueSame
        obtain ⟨withValue, foundValue, valueValue⟩ := Option.map_eq_some_iff.mp valueSame
        simp only [foundAddress, foundTime, foundValue, Option.bind_eq_bind, Option.bind_some, Option.map_some,
          Option.pure_def, Option.some.injEq]
        rw [valueValue, valueTime, valueAddress, start]

theorem cache_definition_holds (output : GKRAddress) (relation : GKRCacheRelation) (program : LookupPayload)
    (found : cacheProgram relation = some program) (typed : cacheTyped roles output relation = true)
    (base : NativeArithmetic.CacheHolds output relation physical)
    (extension : NativeMemory.CacheHolds challenges physical values output relation) :
    (AffineDefinition.mk output program).Holds challenges.memory.embed (cacheChallenges challenges)
      (wires challenges roles physical values) := by
  simp only [AffineDefinition.Holds]
  cases relation with
  | SingleColumnLookup row width =>
    simp only [cacheProgram, Option.some.injEq] at found
    subst found
    simp only [cacheTyped, Bool.and_eq_true] at typed
    rw [wires_base challenges roles physical values typed.1,
      linear_interpret challenges roles physical values row.input typed.2]
    exact congrArg challenges.embed base
  | MemoryTuple row =>
    simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true'] at typed
    rw [wires_extension challenges roles physical values typed.1]
    have same := tuple_interpret challenges roles physical values row
    change tupleProgram row = some program at found
    rw [found, Option.map_some] at same
    exact (Option.some.inj (same.trans extension)).symm
  | VectorizedLookup row =>
    simp only [cacheProgram, Option.some.injEq] at found
    subst found
    simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true'] at typed
    rw [wires_extension challenges roles physical values typed.1,
      vector_interpret challenges roles physical values row typed.2]
    exact extension
  | VectorizedLookupSetup addresses =>
    simp only [cacheProgram, Option.some.injEq] at found
    subst found
    simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true'] at typed
    rw [wires_extension challenges roles physical values typed.1,
      setup_interpret challenges roles physical values addresses typed.2]
    exact extension

theorem gate_definition_holds (relation : GKRRelation) (definition : AffineDefinition)
    (found : gateDefinition relation = some definition) (typed : gateTyped roles relation = true)
    (base : NativeArithmetic.GateHolds relation physical)
    (extension : NativeMemory.GateHolds challenges physical values relation) :
    definition.Holds challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) := by
  cases relation <;> simp only [gateDefinition, reduceCtorEq] at found <;>
    simp only [Option.some.injEq] at found <;> subst found <;> simp only [AffineDefinition.Holds, interpret_input]
  case CopyInBaseField input output =>
    simp only [gateTyped, Bool.and_eq_true] at typed
    rw [wires_base challenges roles physical values typed.1, wires_base challenges roles physical values typed.2]
    exact congrArg challenges.embed base
  case CopyInExtensionField input output =>
    simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at typed
    rw [wires_extension challenges roles physical values typed.1, wires_extension challenges roles physical values typed.2]
    exact extension
  case MaterializeSingleLookupInput row output width =>
    simp only [gateTyped, Bool.and_eq_true] at typed
    rw [wires_base challenges roles physical values typed.1,
      linear_interpret challenges roles physical values row.input typed.2]
    exact congrArg challenges.embed base
  case MaterializedVectorLookupInput row output =>
    simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at typed
    rw [wires_extension challenges roles physical values typed.1,
      vector_interpret challenges roles physical values row typed.2]
    exact extension

theorem product_gate_holds (caches : List GKRAddress) (relation : GKRRelation)
    (gate : NativeProductGate) (found : productGate caches relation = some gate) (typed : gateTyped roles relation = true)
    (extension : NativeMemory.GateHolds challenges physical values relation) :
    gate.Holds challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) := by
  cases relation <;> simp only [productGate, reduceCtorEq] at found
  case InitialGrandProductFromCaches input output =>
    obtain ⟨left, right, pair⟩ := fixed_two input
    simp only [pair, Option.some.injEq] at found
    subst found
    simp only [gateTyped, pair, Bool.and_eq_true, Bool.not_eq_true', List.all_cons, List.all_nil, Bool.and_true] at typed
    simp only [NativeMemory.GateHolds, pair] at extension
    simp only [NativeProductGate.Holds, interpret_input, wires_extension challenges roles physical values typed.1,
      wires_extension challenges roles physical values typed.2.1, wires_extension challenges roles physical values typed.2.2]
    exact extension
  case InitialGrandProductWithoutCaches input output =>
    obtain ⟨left, right, pair⟩ := fixed_two input
    simp only [pair] at found
    simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at typed
    simp only [NativeMemory.GateHolds, pair] at extension
    obtain ⟨leftValue, rightValue, leftFound, rightFound, product⟩ := extension
    cases leftProgram : tupleProgram left with
    | none => simp [leftProgram] at found
    | some leftPayload =>
      cases rightProgram : tupleProgram right with
      | none => simp [leftProgram, rightProgram] at found
      | some rightPayload =>
        simp only [leftProgram, rightProgram, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at found
        subst found
        have leftSame := tuple_interpret challenges roles physical values left
        have rightSame := tuple_interpret challenges roles physical values right
        rw [leftProgram, Option.map_some, leftFound, Option.some.injEq] at leftSame
        rw [rightProgram, Option.map_some, rightFound, Option.some.injEq] at rightSame
        simp only [NativeProductGate.Holds, wires_extension challenges roles physical values typed.1, leftSame,
          rightSame]
        exact product
  case MaterializeGrandProductTermExpression input output =>
    cases program : tupleProgram input with
    | none => simp [program] at found
    | some payload =>
      simp only [program, Option.map_some, Option.some.injEq] at found
      subst found
      simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at typed
      have same := tuple_interpret challenges roles physical values input
      rw [program, Option.map_some] at same
      simp only [NativeProductGate.Holds, wires_extension challenges roles physical values typed.1]
      exact (Option.some.inj (same.trans extension)).symm
  case CopyInExtensionField input output =>
    simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at typed
    split at found <;> simp only [Option.some.injEq] at found <;> subst found <;>
      simp only [NativeProductGate.Holds, interpret_input, wires_extension challenges roles physical values typed.1,
        wires_extension challenges roles physical values typed.2] <;> exact extension
  case TrivialProduct input output =>
    obtain ⟨left, right, pair⟩ := fixed_two input
    simp only [pair, Option.some.injEq] at found
    subst found
    simp only [gateTyped, pair, Bool.and_eq_true, Bool.not_eq_true', List.all_cons, List.all_nil, Bool.and_true] at typed
    simp only [NativeMemory.GateHolds, pair] at extension
    simp only [NativeProductGate.Holds, wires_extension challenges roles physical values typed.1,
      wires_extension challenges roles physical values typed.2.1, wires_extension challenges roles physical values typed.2.2]
    exact extension
  case MaskIntoIdentityProduct input predicate output =>
    simp only [Option.some.injEq] at found
    subst found
    simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at typed
    simp only [NativeProductGate.Holds, wires_extension challenges roles physical values typed.1.1,
      wires_extension challenges roles physical values typed.1.2, wires_base challenges roles physical values typed.2]
    rw [extension]
    simp only [PaddingBoundary.mask, maskProduct]
    ring

end Semantics

section Circuit
variable (challenges : NativeMemory.Challenges R) (roles : GKRAddress → Bool) (physical : GKRAddress → F)
  (values : GKRAddress → R) {circuit : Circuit}

theorem cache_member {entry : GKRAddress × GKRCacheRelation} (member : entry ∈ layerCaches circuit) :
    ∃ layer ∈ circuit.layers, entry ∈ layer.cached_relations := by
  obtain ⟨layer, layerMember, inside⟩ := List.mem_flatMap.mp member
  exact ⟨layer, Array.mem_def.mpr layerMember, Array.mem_def.mpr inside⟩

theorem gate_member {gate : GateArtifacts} (member : gate ∈ layerGates circuit) :
    ∃ layer ∈ circuit.layers, gate ∈ layer.gates ++ layer.gates_with_external_connections := by
  obtain ⟨layer, layerMember, inside⟩ := List.mem_flatMap.mp member
  exact ⟨layer, Array.mem_def.mpr layerMember, Array.mem_def.mpr inside⟩

theorem typed_caches (typed : typingChecked roles circuit = true) :
    ∀ entry ∈ layerCaches circuit, cacheTyped roles entry.1 entry.2 = true := by
  simp only [typingChecked, Bool.and_eq_true] at typed
  exact List.all_eq_true.mp typed.1

theorem typed_gates (typed : typingChecked roles circuit = true) :
    ∀ gate ∈ layerGates circuit, gateTyped roles gate.enforced_relation = true := by
  simp only [typingChecked, Bool.and_eq_true] at typed
  exact List.all_eq_true.mp typed.2

/-- Native base gates and the extension semantics give every imported affine definition. -/
theorem definitions_hold (typed : typingChecked roles circuit = true)
    (accepted : NativeArithmetic.Holds circuit physical)
    (extension : NativeMemory.Holds circuit challenges physical values) :
    ∀ definition ∈ definitionPrograms circuit, definition.Holds challenges.memory.embed
      (cacheChallenges challenges) (wires challenges roles physical values) := by
  intro definition member
  rcases List.mem_append.mp member with cache | gate
  · obtain ⟨entry, entryMember, found⟩ := List.mem_filterMap.mp cache
    obtain ⟨program, programFound, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨layer, layerMember, inside⟩ := cache_member entryMember
    exact cache_definition_holds challenges roles physical values entry.1 entry.2 program programFound
      (typed_caches roles typed entry entryMember) ((accepted layer layerMember).1 entry inside)
      ((extension layer layerMember).1 entry inside)
  · obtain ⟨artifact, artifactMember, found⟩ := List.mem_filterMap.mp gate
    obtain ⟨layer, layerMember, inside⟩ := gate_member artifactMember
    exact gate_definition_holds challenges roles physical values artifact.enforced_relation definition found
      (typed_gates roles typed artifact artifactMember) ((accepted layer layerMember).2 artifact inside)
      ((extension layer layerMember).2 artifact inside)

/-- The extension semantics give every imported RAM-product gate. -/
theorem products_hold (typed : typingChecked roles circuit = true)
    (extension : NativeMemory.Holds circuit challenges physical values) :
    ∀ gate ∈ productGates circuit, gate.Holds challenges.memory.embed
      (cacheChallenges challenges) (wires challenges roles physical values) := by
  intro gate member
  obtain ⟨artifact, artifactMember, found⟩ := List.mem_filterMap.mp member
  obtain ⟨layer, layerMember, inside⟩ := gate_member artifactMember
  exact product_gate_holds challenges roles physical values _ artifact.enforced_relation gate found
    (typed_gates roles typed artifact artifactMember) ((extension layer layerMember).2 artifact inside)

theorem cache_member_definition {layer : GKRLayerDescription} {entry : GKRAddress × GKRCacheRelation}
    {program : LookupPayload} (layerMember : layer ∈ circuit.layers) (inside : entry ∈ layer.cached_relations)
    (found : cacheProgram entry.2 = some program) :
    AffineDefinition.mk entry.1 program ∈ definitionPrograms circuit := by
  apply List.mem_append_left
  refine List.mem_filterMap.mpr ⟨entry, List.mem_flatMap.mpr ⟨layer, Array.mem_def.mp layerMember, Array.mem_def.mp inside⟩, ?_⟩
  rw [found]
  rfl

theorem gate_member_definition {layer : GKRLayerDescription} {gate : GateArtifacts} {definition : AffineDefinition}
    (layerMember : layer ∈ circuit.layers) (inside : gate ∈ layer.gates ++ layer.gates_with_external_connections)
    (found : gateDefinition gate.enforced_relation = some definition) :
    definition ∈ definitionPrograms circuit :=
  List.mem_append_right _ (List.mem_filterMap.mpr
    ⟨gate, List.mem_flatMap.mpr ⟨layer, Array.mem_def.mp layerMember, Array.mem_def.mp inside⟩, found⟩)

theorem gate_member_product {layer : GKRLayerDescription} {gate : GateArtifacts} {product : NativeProductGate}
    (layerMember : layer ∈ circuit.layers) (inside : gate ∈ layer.gates ++ layer.gates_with_external_connections)
    (found : productGate (memoryCaches circuit) gate.enforced_relation = some product) :
    product ∈ productGates circuit :=
  List.mem_filterMap.mpr ⟨gate, List.mem_flatMap.mpr ⟨layer, Array.mem_def.mp layerMember, Array.mem_def.mp inside⟩, found⟩

/-- Imported definitions and product gates give the extension semantics of every cache and gate. -/
theorem holds_of_programs (typed : typingChecked roles circuit = true)
    (definitions : ∀ definition ∈ definitionPrograms circuit, definition.Holds challenges.memory.embed
      (cacheChallenges challenges) (wires challenges roles physical values))
    (products : ∀ gate ∈ productGates circuit, gate.Holds challenges.memory.embed
      (cacheChallenges challenges) (wires challenges roles physical values)) :
    NativeMemory.Holds circuit challenges physical (wires challenges roles physical values) := by
  intro layer layerMember
  constructor
  · intro entry inside
    have entryTyped := typed_caches roles typed entry
      (List.mem_flatMap.mpr ⟨layer, Array.mem_def.mp layerMember, Array.mem_def.mp inside⟩)
    have holds (program : LookupPayload) (found : cacheProgram entry.2 = some program) :=
      definitions _ (cache_member_definition layerMember inside found)
    rcases entry with ⟨output, relation⟩
    cases relation with
    | SingleColumnLookup row width => trivial
    | MemoryTuple row =>
      simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true', Option.isSome_iff_exists] at entryTyped
      obtain ⟨program, found⟩ := entryTyped.2
      have same := tuple_interpret challenges roles physical values row
      rw [found, Option.map_some] at same
      simp only [NativeMemory.CacheHolds, ← same]
      exact congrArg some (holds program found).symm
    | VectorizedLookup row =>
      simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true'] at entryTyped
      simp only [NativeMemory.CacheHolds]
      rw [holds (vectorProgram row) rfl]
      exact vector_interpret challenges roles physical values row entryTyped.2
    | VectorizedLookupSetup addresses =>
      simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true'] at entryTyped
      simp only [NativeMemory.CacheHolds]
      rw [holds (setupProgram addresses) rfl]
      exact setup_interpret challenges roles physical values addresses entryTyped.2
  · intro gate inside
    have gateTyped' := typed_gates roles typed gate
      (List.mem_flatMap.mpr ⟨layer, Array.mem_def.mp layerMember, Array.mem_def.mp inside⟩)
    have holds (definition : AffineDefinition) (found : gateDefinition gate.enforced_relation = some definition) :=
      definitions _ (gate_member_definition layerMember inside found)
    have product (candidate : NativeProductGate)
        (found : productGate (memoryCaches circuit) gate.enforced_relation = some candidate) :=
      products _ (gate_member_product layerMember inside found)
    revert gateTyped' holds product
    cases gate.enforced_relation <;> intro gateTyped' holds product <;>
      simp only [NativeMemory.GateHolds]
    case CopyInExtensionField input output =>
      have equation := holds _ rfl
      simpa only [AffineDefinition.Holds, interpret_input] using equation
    case MaterializedVectorLookupInput row output =>
      simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at gateTyped'
      have equation := holds _ rfl
      simp only [AffineDefinition.Holds] at equation
      rw [equation]
      exact vector_interpret challenges roles physical values row gateTyped'.2
    case InitialGrandProductFromCaches input output =>
      obtain ⟨left, right, pair⟩ := fixed_two input
      have equation := product (.pair output (.input left) (.input right)) (by simp only [productGate, pair])
      simp only [pair]
      simpa only [NativeProductGate.Holds, interpret_input] using equation
    case InitialGrandProductWithoutCaches input output =>
      obtain ⟨left, right, pair⟩ := fixed_two input
      simp only [gateTyped, pair, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true,
        Option.isSome_iff_exists] at gateTyped'
      obtain ⟨leftProgram, leftFound⟩ := gateTyped'.2.1
      obtain ⟨rightProgram, rightFound⟩ := gateTyped'.2.2
      have equation := product (.pair output leftProgram rightProgram)
        (by simp only [productGate, pair, leftFound, rightFound, Option.bind_eq_bind, Option.bind_some])
      have leftSame := tuple_interpret challenges roles physical values left
      have rightSame := tuple_interpret challenges roles physical values right
      rw [leftFound, Option.map_some] at leftSame
      rw [rightFound, Option.map_some] at rightSame
      simp only [pair]
      exact ⟨_, _, leftSame.symm, rightSame.symm, equation⟩
    case MaterializeGrandProductTermExpression input output =>
      simp only [gateTyped, Bool.and_eq_true, Option.isSome_iff_exists] at gateTyped'
      obtain ⟨program, found⟩ := gateTyped'.2
      have equation := product (.single output program) (by simp only [productGate, found, Option.map_some])
      have same := tuple_interpret challenges roles physical values input
      rw [found, Option.map_some] at same
      rw [← same]
      exact congrArg some equation.symm
    case TrivialProduct input output =>
      obtain ⟨left, right, pair⟩ := fixed_two input
      have equation := product (.mul output left right) (by simp only [productGate, pair])
      simp only [pair]
      simpa only [NativeProductGate.Holds] using equation
    case MaskIntoIdentityProduct input predicate output =>
      simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at gateTyped'
      have equation := product (.mask output input predicate) (by simp only [productGate])
      simp only [NativeProductGate.Holds] at equation
      rw [equation, wires_base challenges roles physical values gateTyped'.2]
      simp only [PaddingBoundary.mask, maskProduct, Challenges.embed]
      ring

end Circuit

end Airbender.Compiler.NativeMemoryBridge
