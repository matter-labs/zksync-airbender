module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NativeMemoryPorts

@[expose] public section
set_option warningAsError true

/-! The RAM products of a worker capture. The product gates of the capture multiply cached memory tuples.
The kernel checks that the renamed tuples of each product tree are a permutation of the model tuples of
the worker ports and its request. -/

namespace Airbender.Compiler.NativeMemoryBridge
open NativeArithmetic NativeMemory Trace

deriving instance DecidableEq for Fixed
deriving instance DecidableEq for CompiledAddressSpaceRelationStrict
deriving instance DecidableEq for CompiledAddressStrict
deriving instance DecidableEq for CompiledMemoryTimestamp
deriving instance DecidableEq for RamWordRepresentation
deriving instance DecidableEq for SpecialMemoryContributionRelation

/-- The outputs of the base-field caches and gates. -/
def baseOutputs (circuit : Circuit) : List GKRAddress :=
  (layerCaches circuit).filterMap (fun entry => match entry.2 with
    | .SingleColumnLookup _ _ => some entry.1
    | _ => none) ++
  (layerGates circuit).filterMap fun gate => match gate.enforced_relation with
    | .LinearBaseFieldRelation _ output | .MaxQuadratic _ _ output | .CopyInBaseField _ output
    | .MaterializeSingleLookupInput _ output _ => some output
    | _ => none

/-- An inner or cached wire is a base-field wire when a base-field cache or gate writes it. -/
def structuralRoles (circuit : Circuit) (address : GKRAddress) : Bool := (baseOutputs circuit).contains address

/-- The memory tuple of a cache output. -/
def cacheTuple (circuit : Circuit) (address : GKRAddress) : Option SpecialMemoryContributionRelation :=
  ((layerCaches circuit).find? fun entry => entry.1 == address).bind fun entry => match entry.2 with
    | .MemoryTuple row => some row
    | _ => none

/-- The renamed memory tuple that a product registry leaf reads. -/
def leafTuple (circuit : Circuit) (registry : List LookupPayload) (index : Nat) :
    Option SpecialMemoryContributionRelation :=
  match registry[index]? with
  | some (.input address) => (cacheTuple circuit address).bind (renameTuple (memoryVariable circuit))
  | _ => none

/-- The input of the base copy gate that writes an address. -/
def copySource (circuit : Circuit) (address : GKRAddress) : Option GKRAddress :=
  (layerGates circuit).findSome? fun gate => match gate.enforced_relation with
    | .CopyInBaseField input output => if output == address then some input else none
    | _ => none

/-- Follow base copy gates back from an address, at most `fuel` times. -/
def copyRoot (circuit : Circuit) : Nat → GKRAddress → GKRAddress
  | 0, address => address
  | fuel + 1, address => match copySource circuit address with
    | some input => copyRoot circuit fuel input
    | none => address

/-- The model read tuples of the worker ports, then the request tuple. -/
def modelReadTuples (ports : List MemoryPort) (csr : Nat) (invocation : Vector Nat 2) :
    Option (List SpecialMemoryContributionRelation) := do
  return (← ports.mapM portReadRelation) ++ [← requestRelation csr (some invocation)]

/-- The model write tuples of the worker ports, then the returned request tuple. -/
def modelWriteTuples (ports : List MemoryPort) (csr : Nat) (invocation : Vector Nat 2) :
    Option (List SpecialMemoryContributionRelation) := do
  return (← ports.mapM (portWriteRelation invocation)) ++ [← requestRelation csr none]

/-- The renamed tuples of the product tree leaves are a permutation of the model tuples. -/
def tuplesMatch (circuit : Circuit) (registry : List LookupPayload) (leaves : List Nat)
    (model : Option (List SpecialMemoryContributionRelation)) : Bool :=
  match leaves.mapM (leafTuple circuit registry), model with
  | some actual, some expected => actual.isPerm expected
  | _, _ => false

variable {R : Type} [CommRing R]

theorem copySource_value {circuit : Circuit} {physical : GKRAddress → F}
    (accepted : NativeArithmetic.Holds circuit physical) {address input : GKRAddress}
    (found : copySource circuit address = some input) : physical address = physical input := by
  obtain ⟨gate, member, result⟩ := List.exists_of_findSome?_eq_some found
  revert result
  cases relation : gate.enforced_relation <;> simp
  case CopyInBaseField source output =>
    intro same rfl
    obtain ⟨layer, layerMember, inside⟩ := gate_member member
    have holds := (accepted layer layerMember).2 gate inside
    rw [relation] at holds
    rw [← same]
    exact holds

theorem copyRoot_value {circuit : Circuit} {physical : GKRAddress → F}
    (accepted : NativeArithmetic.Holds circuit physical) (fuel : Nat) (address : GKRAddress) :
    physical address = physical (copyRoot circuit fuel address) := by
  induction fuel generalizing address with
  | zero => rfl
  | succ fuel proof =>
    simp only [copyRoot]
    cases found : copySource circuit address with
    | none => rfl
    | some input => exact (copySource_value accepted found).trans (proof input)

section Products
variable (challenges : NativeMemory.Challenges R) (roles : GKRAddress → Bool) (physical : GKRAddress → F)
  (values : GKRAddress → R) (assignment : Nat → F) {circuit : Circuit}

theorem cacheTuple_some {address : GKRAddress} {native : SpecialMemoryContributionRelation}
    (found : cacheTuple circuit address = some native) :
    ∃ entry ∈ layerCaches circuit, entry.1 = address ∧ entry.2 = .MemoryTuple native := by
  unfold cacheTuple at found
  cases entryFound : (layerCaches circuit).find? (fun entry => entry.1 == address) with
  | none => simp [entryFound] at found
  | some entry =>
    rw [entryFound, Option.bind_some] at found
    refine ⟨entry, List.mem_of_find?_eq_some entryFound, by simpa using List.find?_some entryFound, ?_⟩
    revert found
    cases entry.2 <;> simp

/-- A registry leaf reads the native tuple of its cache, which equals the renamed tuple on the assignment. -/
theorem leaf_value (typed : typingChecked roles circuit = true)
    (extension : NativeMemory.Holds circuit challenges physical values)
    (agreement : PlacementAgreement circuit physical assignment) {registry : List LookupPayload} {index : Nat}
    {row : SpecialMemoryContributionRelation} (found : leafTuple circuit registry index = some row) :
    tuple challenges (memoryWires assignment) row =
      some (productRegistryValue registry challenges.memory.embed (cacheChallenges challenges)
        (wires challenges roles physical values) index) := by
  unfold leafTuple at found
  cases payload : registry[index]? with
  | none => simp [payload] at found
  | some leaf =>
    rw [payload] at found
    cases leaf with
    | input address =>
      simp only at found
      cases cached : cacheTuple circuit address with
      | none => simp [cached] at found
      | some native =>
        rw [cached, Option.bind_some] at found
        obtain ⟨entry, member, output, relation⟩ := cacheTuple_some cached
        obtain ⟨layer, layerMember, inside⟩ := cache_member member
        have holds := (extension layer layerMember).1 entry inside
        have entryTyped := typed_caches roles typed entry member
        rw [relation] at holds entryTyped
        simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true'] at entryTyped
        simp only [NativeMemory.CacheHolds] at holds
        rw [← tuple_rename challenges (fun offset placed placedFound =>
          memoryVariable_value agreement placedFound) found, holds]
        simp only [productRegistryValue, payload, interpret_input, ← output,
          wires_extension challenges roles physical values entryTyped.1]
    | constant _ | add _ _ | scale _ _ => simp at found

/-- Leaves whose renamed tuples are all present give the product of their tuple values. -/
theorem leaves_product (typed : typingChecked roles circuit = true)
    (extension : NativeMemory.Holds circuit challenges physical values)
    (agreement : PlacementAgreement circuit physical assignment) (registry : List LookupPayload) :
    ∀ (leaves : List Nat) (rows : List SpecialMemoryContributionRelation),
      leaves.mapM (leafTuple circuit registry) = some rows →
      (leaves.map (productRegistryValue registry challenges.memory.embed (cacheChallenges challenges)
        (wires challenges roles physical values))).prod =
        (rows.map fun row => (tuple challenges (memoryWires assignment) row).getD 0).prod
  | [], rows, found => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found
    subst found
    rfl
  | index :: rest, rows, found => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at found
    cases first : leafTuple circuit registry index with
    | none => simp [first] at found
    | some row =>
      cases others : rest.mapM (leafTuple circuit registry) with
      | none => simp [first, others] at found
      | some tail =>
        simp only [first, others, Option.bind_some, Option.some.injEq] at found
        subst found
        simp only [List.map_cons, List.prod_cons,
          leaf_value challenges roles physical values assignment typed extension agreement first, Option.getD_some,
          leaves_product typed extension agreement registry rest tail others]

end Products

section Model
variable (challenges : NativeMemory.Challenges R) (assignment : Nat → F)

/-- The model write token of a worker port at the invocation clock. -/
def workerWriteToken (invocation : Vector Nat 2) (port : MemoryPort) : Trace.MemoryToken babyBearModulus :=
  ⟨port.address.code assignment, ((rawPair assignment invocation).1 + port.clock.offset,
    (rawPair assignment invocation).2), port.writeCode assignment⟩

theorem ports_read_product : ∀ (ports : List MemoryPort) (rows : List SpecialMemoryContributionRelation),
    ports.mapM portReadRelation = some rows →
    (rows.map fun row => (tuple challenges (memoryWires assignment) row).getD 0).prod =
      ((ports.map (readToken assignment)).map challenges.memory.encode).prod
  | [], rows, found => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found
    subst found
    rfl
  | port :: rest, rows, found => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at found
    cases first : portReadRelation port with
    | none => simp [first] at found
    | some row =>
      cases others : rest.mapM portReadRelation with
      | none => simp [first, others] at found
      | some tail =>
        simp only [first, others, Option.bind_some, Option.some.injEq] at found
        subst found
        simp only [List.map_cons, List.prod_cons, portRead_tuple challenges assignment port first, Option.getD_some,
          ports_read_product rest tail others]

theorem ports_write_product (invocation : Vector Nat 2) :
    ∀ (ports : List MemoryPort) (rows : List SpecialMemoryContributionRelation),
    ports.mapM (portWriteRelation invocation) = some rows →
    (rows.map fun row => (tuple challenges (memoryWires assignment) row).getD 0).prod =
      ((ports.map (workerWriteToken assignment invocation)).map challenges.memory.encode).prod
  | [], rows, found => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found
    subst found
    rfl
  | port :: rest, rows, found => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at found
    cases first : portWriteRelation invocation port with
    | none => simp [first] at found
    | some row =>
      cases others : rest.mapM (portWriteRelation invocation) with
      | none => simp [first, others] at found
      | some tail =>
        simp only [first, others, Option.bind_some, Option.some.injEq] at found
        subst found
        simp only [List.map_cons, List.prod_cons, portWrite_tuple challenges assignment invocation port first,
          Option.getD_some, ports_write_product invocation rest tail others]
        rfl

/-- The model read tuples give the encoded port read tokens and the issued request token. -/
theorem model_read_product (ports : List MemoryPort) (csr : Nat) (invocation : Vector Nat 2)
    {rows : List SpecialMemoryContributionRelation} (found : modelReadTuples ports csr invocation = some rows) :
    (rows.map fun row => (tuple challenges (memoryWires assignment) row).getD 0).prod =
      ((ports.map (readToken assignment) ++
        [(⟨csr, rawPair assignment invocation⟩ : Delegation.Requests.Request babyBearModulus).issued]).map
        challenges.memory.encode).prod := by
  simp only [modelReadTuples, Option.bind_eq_bind, Option.pure_def] at found
  cases portRows : ports.mapM portReadRelation with
  | none => simp [portRows] at found
  | some head =>
    cases requestRow : requestRelation csr (some invocation) with
    | none => simp [portRows, requestRow] at found
    | some last =>
      simp only [portRows, requestRow, Option.bind_some, Option.some.injEq] at found
      subst found
      have requestValue := request_tuple challenges assignment ⟨csr, rawPair assignment invocation⟩ (some invocation)
        requestRow
      simp only [List.map_append, List.prod_append, ports_read_product challenges assignment ports head portRows,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, requestValue, Option.getD_some]
      rfl

/-- The model write tuples give the encoded port write tokens and the returned request token. -/
theorem model_write_product (ports : List MemoryPort) (csr : Nat) (invocation : Vector Nat 2)
    {rows : List SpecialMemoryContributionRelation} (found : modelWriteTuples ports csr invocation = some rows) :
    (rows.map fun row => (tuple challenges (memoryWires assignment) row).getD 0).prod =
      ((ports.map (workerWriteToken assignment invocation) ++
        [(⟨csr, rawPair assignment invocation⟩ : Delegation.Requests.Request babyBearModulus).empty]).map
        challenges.memory.encode).prod := by
  simp only [modelWriteTuples, Option.bind_eq_bind, Option.pure_def] at found
  cases portRows : ports.mapM (portWriteRelation invocation) with
  | none => simp [portRows] at found
  | some head =>
    cases requestRow : requestRelation csr none with
    | none => simp [portRows, requestRow] at found
    | some last =>
      simp only [portRows, requestRow, Option.bind_some, Option.some.injEq] at found
      subst found
      have requestValue := request_tuple challenges assignment ⟨csr, rawPair assignment invocation⟩ none requestRow
      simp only [List.map_append, List.prod_append,
        ports_write_product challenges assignment invocation ports head portRows,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, requestValue, Option.getD_some]
      rfl

end Model

section Assembly
variable (challenges : NativeMemory.Challenges R) (roles : GKRAddress → Bool) (physical : GKRAddress → F)
  (values : GKRAddress → R) (assignment : Nat → F) {circuit : Circuit}

theorem matched_product (typed : typingChecked roles circuit = true)
    (extension : NativeMemory.Holds circuit challenges physical values)
    (agreement : PlacementAgreement circuit physical assignment) (registry : List LookupPayload) (leaves : List Nat)
    {model : Option (List SpecialMemoryContributionRelation)} (checked : tuplesMatch circuit registry leaves model = true) :
    ∃ rows, model = some rows ∧
      (leaves.map (productRegistryValue registry challenges.memory.embed (cacheChallenges challenges)
        (wires challenges roles physical values))).prod =
        (rows.map fun row => (tuple challenges (memoryWires assignment) row).getD 0).prod := by
  unfold tuplesMatch at checked
  cases actualFound : leaves.mapM (leafTuple circuit registry) with
  | none => simp [actualFound] at checked
  | some actual =>
    cases model with
    | none => simp [actualFound] at checked
    | some expected =>
      simp only [actualFound] at checked
      refine ⟨expected, rfl, ?_⟩
      rw [leaves_product challenges roles physical values assignment typed extension agreement registry leaves actual
        actualFound]
      exact ((List.isPerm_iff.mp checked).map _).prod_eq

/-- The RAM outputs of a worker capture are the execute-masked products of the encoded model tokens. -/
theorem worker_ram_products (typed : typingChecked roles circuit = true)
    (accepted : NativeArithmetic.Holds circuit physical)
    (extension : NativeMemory.Holds circuit challenges physical values)
    (agreement : PlacementAgreement circuit physical assignment)
    {registry : List LookupPayload} {readLeaves writeLeaves : List Nat} {ports : List MemoryPort}
    {csr : Nat} {invocation : Vector Nat 2} {readOutput writeOutput mask : GKRAddress}
    {fuel memoryExecute executeColumn : Nat}
    (outputs : ramOutputs circuit = [readOutput, writeOutput])
    (outputRoles : isBase roles readOutput = false ∧ isBase roles writeOutput = false)
    (maskRole : isBase roles mask = true)
    (maskRoot : copyRoot circuit fuel mask = .BaseLayerMemory memoryExecute)
    (execute : memoryVariable circuit memoryExecute = some executeColumn)
    (reads : tuplesMatch circuit registry readLeaves (modelReadTuples ports csr invocation) = true)
    (writes : tuplesMatch circuit registry writeLeaves (modelWriteTuples ports csr invocation) = true)
    (read : wires challenges roles physical values readOutput = maskProduct (wires challenges roles physical values mask)
      (readLeaves.map (productRegistryValue registry challenges.memory.embed (cacheChallenges challenges)
        (wires challenges roles physical values))).prod)
    (write : wires challenges roles physical values writeOutput = maskProduct (wires challenges roles physical values mask)
      (writeLeaves.map (productRegistryValue registry challenges.memory.embed (cacheChallenges challenges)
        (wires challenges roles physical values))).prod) :
    RamProducts circuit challenges values (assignment executeColumn)
      (ports.map (readToken assignment) ++
        [(⟨csr, rawPair assignment invocation⟩ : Delegation.Requests.Request babyBearModulus).issued])
      (ports.map (workerWriteToken assignment invocation) ++
        [(⟨csr, rawPair assignment invocation⟩ : Delegation.Requests.Request babyBearModulus).empty]) := by
  have maskValue : wires challenges roles physical values mask = challenges.memory.embed (assignment executeColumn) := by
    rw [wires_base challenges roles physical values maskRole, copyRoot_value accepted fuel mask, maskRoot,
      memoryVariable_value agreement execute]
    rfl
  obtain ⟨readRows, readModel, readProduct⟩ :=
    matched_product challenges roles physical values assignment typed extension agreement registry readLeaves reads
  obtain ⟨writeRows, writeModel, writeProduct⟩ :=
    matched_product challenges roles physical values assignment typed extension agreement registry writeLeaves writes
  apply ram_products_of_outputs outputs
  · rw [← wires_extension challenges roles physical values outputRoles.1, read, maskValue, readProduct,
      model_read_product challenges assignment ports csr invocation readModel]
  · rw [← wires_extension challenges roles physical values outputRoles.2, write, maskValue, writeProduct,
      model_write_product challenges assignment ports csr invocation writeModel]

end Assembly

end Airbender.Compiler.NativeMemoryBridge
