module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryTokens
public import Human.Helpers.Delegation.Requests

@[expose] public section
set_option warningAsError true

/-! The memory tuples of a worker capture against the model port descriptors. Each tuple reads memory
columns. The placement of the capture names the logical variable of each column. A model port gives the
same tuple over logical variables, and its value is the encoding of the model token. -/

namespace Airbender.Compiler.NativeMemoryBridge
open NativeArithmetic NativeMemory Trace

/-- The logical variable that the capture places at a memory column. -/
def memoryVariable (circuit : Circuit) (offset : Nat) : Option Nat :=
  (circuit.placement_data.entries.toList.find? fun entry => entry.2 == .BaseLayerMemory offset).map (·.1)

/-- Two columns as a fixed pair. -/
def fixedPair (first second : Nat) : Fixed 2 Nat := ⟨#[first, second], rfl⟩

/-- Rename the two columns of a fixed pair. -/
def renamePair (rename : Nat → Option Nat) (pair : Fixed 2 Nat) : Option (Fixed 2 Nat) :=
  match pair.values.toList with
  | [first, second] => do return fixedPair (← rename first) (← rename second)
  | _ => none

def renameSpace (rename : Nat → Option Nat) :
    CompiledAddressSpaceRelationStrict → Option CompiledAddressSpaceRelationStrict
  | .Constant value => some (.Constant value)
  | .IsRam offset => (rename offset).map .IsRam
  | .IsRegister offset => (rename offset).map .IsRegister

def renameAddress (rename : Nat → Option Nat) : CompiledAddressStrict → Option CompiledAddressStrict
  | .ConstantU16 value => some (.ConstantU16 value)
  | .Constant value => some (.Constant value)
  | .U16Space offset => (rename offset).map .U16Space
  | .U32Space offsets => (renamePair rename offsets).map .U32Space
  | .U32SpaceSpecialIndirect base none offset high => do
    return .U32SpaceSpecialIndirect (← rename base) none offset (← rename high)
  | .U32SpaceSpecialIndirect base (some (scale, column)) offset high => do
    return .U32SpaceSpecialIndirect (← rename base) (some (scale, ← rename column)) offset (← rename high)
  | .U32SpaceGeneric _ => none

def renameTimestamp (rename : Nat → Option Nat) : CompiledMemoryTimestamp → Option CompiledMemoryTimestamp
  | .Zero => some .Zero
  | .Normal limbs => (renamePair rename limbs).map .Normal

def renameValue (rename : Nat → Option Nat) : RamWordRepresentation → Option RamWordRepresentation
  | .Zero => some .Zero
  | .U16Limbs limbs => (renamePair rename limbs).map .U16Limbs
  | .U8Limbs bytes => match bytes.values.toList with
    | [first, second, third, fourth] => do
      return .U8Limbs ⟨#[← rename first, ← rename second, ← rename third, ← rename fourth], rfl⟩
    | _ => none

/-- Rename every memory column of a memory tuple. -/
def renameTuple (rename : Nat → Option Nat) (row : SpecialMemoryContributionRelation) :
    Option SpecialMemoryContributionRelation := do
  return ⟨← renameSpace rename row.address_space, ← renameAddress rename row.address,
    ← renameTimestamp rename row.timestamp, ← renameValue rename row.value, row.timestamp_offset⟩

/-- Logical values at the memory columns that a renamed tuple reads. -/
def memoryWires (assignment : Nat → F) : GKRAddress → F
  | .BaseLayerMemory column => assignment column
  | _ => 0

/-- The model word representation of a port word. -/
def wordRepresentation : WordColumns → RamWordRepresentation
  | .zero => .Zero
  | .u16 columns => .U16Limbs (fixedPair columns[0] columns[1])
  | .u8 columns => .U8Limbs ⟨#[columns[0], columns[1], columns[2], columns[3]], rfl⟩

/-- The model address space and address of a port. -/
def addressRelation : MemoryAddress → Option (CompiledAddressSpaceRelationStrict × CompiledAddressStrict)
  | .constantRegister index =>
    if bound : index < 65536 then some (.Constant ⟨0, by decide⟩, .ConstantU16 ⟨index, bound⟩) else none
  | .register column => some (.Constant ⟨0, by decide⟩, .U16Space column)
  | .mixed selector registerOnTrue columns =>
    some (if registerOnTrue then .IsRegister selector else .IsRam selector, .U32Space (fixedPair columns[0] columns[1]))
  | .indirect port => do
    let dynamic ← match port.offsetColumn with
      | none => some none
      | some column => if bound : port.scale < 65536 then some (some (⟨port.scale, bound⟩, column)) else none
    if bound : port.constant < 4294967296 then
      some (.Constant ⟨1, by decide⟩,
        .U32SpaceSpecialIndirect port.baseColumns[0] dynamic ⟨port.constant, bound⟩ port.baseColumns[1])
    else none

/-- The tuple of a port read: the previous timestamp and the read value. -/
def portReadRelation (port : MemoryPort) : Option SpecialMemoryContributionRelation := do
  let (space, address) ← addressRelation port.address
  return ⟨space, address, .Normal (fixedPair port.clock.previous[0] port.clock.previous[1]),
    wordRepresentation port.readValue, ⟨0, by decide⟩⟩

/-- The tuple of a port write: the base timestamp with the port offset and the written value. -/
def portWriteRelation (time : Vector Nat 2) (port : MemoryPort) : Option SpecialMemoryContributionRelation := do
  let (space, address) ← addressRelation port.address
  if bound : port.clock.offset < 4294967296 then
    return ⟨space, address, .Normal (fixedPair time[0] time[1]),
      wordRepresentation (port.writeValue.getD port.readValue), ⟨port.clock.offset, bound⟩⟩
  else none

/-- The tuple of a request token at the request time, or of the returned zero-time token. -/
def requestRelation (csr : Nat) (time : Option (Vector Nat 2)) : Option SpecialMemoryContributionRelation :=
  if bound : csr < 65536 then
    some ⟨.Constant ⟨0, by decide⟩, .ConstantU16 ⟨csr, bound⟩,
      (time.map fun time => CompiledMemoryTimestamp.Normal (fixedPair time[0] time[1])).getD .Zero,
      .Zero, ⟨0, by decide⟩⟩
  else none

end Airbender.Compiler.NativeMemoryBridge

namespace Airbender.Compiler.NativeMemoryBridge
open NativeArithmetic NativeMemory Trace

variable {R : Type} [CommRing R]

theorem memoryVariable_value {circuit : Circuit} {physical : GKRAddress → F} {assignment : Nat → F}
    (agreement : PlacementAgreement circuit physical assignment) {offset placed : Nat}
    (found : memoryVariable circuit offset = some placed) :
    physical (.BaseLayerMemory offset) = assignment placed := by
  unfold memoryVariable at found
  obtain ⟨entry, entryFound, rfl⟩ := Option.map_eq_some_iff.mp found
  have member := List.mem_of_find?_eq_some entryFound
  have address : entry.2 = .BaseLayerMemory offset := by simpa using List.find?_some entryFound
  rw [← address]
  exact (agreement entry (Array.mem_def.mpr member)).symm

theorem renamePair_some {rename : Nat → Option Nat} {pair renamed : Fixed 2 Nat}
    (found : renamePair rename pair = some renamed) :
    ∃ first second first' second', pair.values.toList = [first, second] ∧
      renamed = fixedPair first' second' ∧ rename first = some first' ∧ rename second = some second' := by
  obtain ⟨first, second, values⟩ := fixed_two pair
  simp only [renamePair, values] at found
  cases firstFound : rename first <;> cases secondFound : rename second <;>
    simp [firstFound, secondFound] at found
  exact ⟨first, second, _, _, values, found.symm, firstFound, secondFound⟩

section Rename
variable (challenges : NativeMemory.Challenges R) {physical : GKRAddress → F} {assignment : Nat → F}
  {rename : Nat → Option Nat}
  (same : ∀ offset placed, rename offset = some placed → physical (.BaseLayerMemory offset) = assignment placed)
include same

theorem column_rename {offset placed : Nat} (found : rename offset = some placed) :
    challenges.column physical offset = challenges.column (memoryWires assignment) placed := by
  rw [Challenges.column, Challenges.column, same offset placed found]
  rfl

theorem space_rename {space renamed : CompiledAddressSpaceRelationStrict}
    (found : renameSpace rename space = some renamed) :
    addressSpace challenges physical space = addressSpace challenges (memoryWires assignment) renamed := by
  cases space with
  | Constant value =>
    simp only [renameSpace, Option.some.injEq] at found
    subst found
    rfl
  | IsRam offset =>
    obtain ⟨placed, variableFound, rfl⟩ := Option.map_eq_some_iff.mp found
    exact column_rename challenges same variableFound
  | IsRegister offset =>
    obtain ⟨placed, variableFound, rfl⟩ := Option.map_eq_some_iff.mp found
    simp only [addressSpace, column_rename challenges same variableFound]

theorem address_rename {word renamed : CompiledAddressStrict} (found : renameAddress rename word = some renamed) :
    address challenges physical word = address challenges (memoryWires assignment) renamed := by
  cases word with
  | ConstantU16 value =>
    simp only [renameAddress, Option.some.injEq] at found
    subst found
    rfl
  | Constant value =>
    simp only [renameAddress, Option.some.injEq] at found
    subst found
    rfl
  | U16Space offset =>
    obtain ⟨placed, variableFound, rfl⟩ := Option.map_eq_some_iff.mp found
    simp only [address, column_rename challenges same variableFound]
  | U32Space offsets =>
    obtain ⟨pair, pairFound, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨first, second, first', second', values, rfl, firstFound, secondFound⟩ := renamePair_some pairFound
    simp only [address, values, fixedPair, List.toList_toArray, column_rename challenges same firstFound,
      column_rename challenges same secondFound]
  | U32SpaceSpecialIndirect base dynamic offset high =>
    cases dynamic with
    | none =>
      simp only [renameAddress] at found
      cases baseFound : rename base <;> cases highFound : rename high <;>
        simp [baseFound, highFound] at found
      subst found
      simp only [address, column_rename challenges same baseFound, column_rename challenges same highFound]
    | some entry =>
      obtain ⟨scale, column⟩ := entry
      simp only [renameAddress] at found
      cases baseFound : rename base <;> cases columnFound : rename column <;> cases highFound : rename high <;>
        simp [baseFound, columnFound, highFound] at found
      subst found
      simp only [address, column_rename challenges same baseFound, column_rename challenges same columnFound,
        column_rename challenges same highFound]
  | U32SpaceGeneric _ => simp [renameAddress] at found

theorem timestamp_rename (offset : U32) {time renamed : CompiledMemoryTimestamp}
    (found : renameTimestamp rename time = some renamed) :
    timestamp challenges physical offset time = timestamp challenges (memoryWires assignment) offset renamed := by
  cases time with
  | Zero =>
    simp only [renameTimestamp, Option.some.injEq] at found
    subst found
    rfl
  | Normal limbs =>
    obtain ⟨pair, pairFound, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨first, second, first', second', values, rfl, firstFound, secondFound⟩ := renamePair_some pairFound
    simp only [timestamp, values, fixedPair, List.toList_toArray, column_rename challenges same firstFound,
      column_rename challenges same secondFound]

theorem value_rename {word renamed : RamWordRepresentation} (found : renameValue rename word = some renamed) :
    value challenges physical word = value challenges (memoryWires assignment) renamed := by
  cases word with
  | Zero =>
    simp only [renameValue, Option.some.injEq] at found
    subst found
    rfl
  | U16Limbs limbs =>
    obtain ⟨pair, pairFound, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨first, second, first', second', values, rfl, firstFound, secondFound⟩ := renamePair_some pairFound
    simp only [value, values, fixedPair, List.toList_toArray, column_rename challenges same firstFound,
      column_rename challenges same secondFound]
  | U8Limbs bytes =>
    obtain ⟨first, second, third, fourth, quad⟩ := fixed_four bytes
    simp only [renameValue, quad] at found
    cases firstFound : rename first <;> cases secondFound : rename second <;>
      cases thirdFound : rename third <;> cases fourthFound : rename fourth <;>
      simp [firstFound, secondFound, thirdFound, fourthFound] at found
    subst found
    simp only [value, quad, column_rename challenges same firstFound,
      column_rename challenges same secondFound, column_rename challenges same thirdFound,
      column_rename challenges same fourthFound]

/-- A renamed tuple has the value of the native tuple on the logical assignment. -/
theorem tuple_rename {row renamed : SpecialMemoryContributionRelation} (found : renameTuple rename row = some renamed) :
    tuple challenges physical row = tuple challenges (memoryWires assignment) renamed := by
  simp only [renameTuple] at found
  cases spaceFound : renameSpace rename row.address_space <;>
    cases addressFound : renameAddress rename row.address <;>
    cases timeFound : renameTimestamp rename row.timestamp <;>
    cases valueFound : renameValue rename row.value <;>
    simp [spaceFound, addressFound, timeFound, valueFound] at found
  subst found
  simp only [tuple, space_rename challenges same spaceFound, address_rename challenges same addressFound,
    timestamp_rename challenges same row.timestamp_offset timeFound, value_rename challenges same valueFound]

end Rename

section Ports
variable (challenges : NativeMemory.Challenges R) (assignment : Nat → F)

/-- The address-space and address part of the token encoding. -/
def addressEncoding (code : Nat) : R :=
  challenges.memory.embed ((Nat.unpair code).1 : F) +
    challenges.memory.weights 0 * challenges.memory.embed ((Nat.unpair (Nat.unpair code).2).1 : F) +
    challenges.memory.weights 1 * challenges.memory.embed ((Nat.unpair (Nat.unpair code).2).2 : F)

/-- The value part of the token encoding. -/
def valueEncoding (code : Nat) : R :=
  challenges.memory.weights 4 * challenges.memory.embed ((Nat.unpair code).1 : F) +
    challenges.memory.weights 5 * challenges.memory.embed ((Nat.unpair code).2 : F)

theorem encode_parts (token : Trace.MemoryToken babyBearModulus) :
    challenges.memory.encode token = challenges.memory.additive + addressEncoding challenges token.address +
      challenges.memory.weights 2 * challenges.memory.embed token.time.1 +
      challenges.memory.weights 3 * challenges.memory.embed token.time.2 + valueEncoding challenges token.value := by
  simp only [InitsTeardowns.Native.Parameters.encode, addressEncoding, valueEncoding]
  ring

theorem value_word (word : WordColumns) :
    value challenges (memoryWires assignment) (wordRepresentation word) =
      some (valueEncoding challenges (word.code assignment)) := by
  cases word <;>
    simp [wordRepresentation, value, fixedPair, WordColumns.evaluate, WordColumns.code, valueEncoding,
      Challenges.column, Challenges.embed, memoryWires, Nat.unpair_pair]

theorem address_port (port : MemoryAddress) {space : CompiledAddressSpaceRelationStrict}
    {word : CompiledAddressStrict} (found : addressRelation port = some (space, word)) :
    ∃ term, address challenges (memoryWires assignment) word = some term ∧
      addressSpace challenges (memoryWires assignment) space + term =
        addressEncoding challenges (port.code assignment) := by
  cases port with
  | constantRegister index =>
    simp only [addressRelation] at found
    split at found <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at found
    obtain ⟨rfl, rfl⟩ := found
    refine ⟨_, rfl, ?_⟩
    simp [addressSpace, addressEncoding, MemoryAddress.code, Nat.unpair_pair, Challenges.embed]
  | register column =>
    simp only [addressRelation, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    refine ⟨_, rfl, ?_⟩
    simp [addressSpace, addressEncoding, MemoryAddress.code, Nat.unpair_pair, Challenges.embed, Challenges.column,
      memoryWires]
  | mixed selector registerOnTrue columns =>
    simp only [addressRelation, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    refine ⟨_, rfl, ?_⟩
    cases registerOnTrue <;>
      simp [addressSpace, addressEncoding, MemoryAddress.code, pairCode, Nat.unpair_pair, Challenges.embed,
        Challenges.column, memoryWires] <;> ring
  | indirect port =>
    simp only [addressRelation] at found
    cases offsetColumn : port.offsetColumn with
    | none =>
      simp only [offsetColumn] at found
      split at found <;> simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq] at found
      obtain ⟨rfl, rfl⟩ := found
      refine ⟨_, rfl, ?_⟩
      simp [addressSpace, addressEncoding, MemoryAddress.code, Verification.IndirectPort.rawAddress, offsetColumn,
        Nat.unpair_pair, Challenges.embed, Challenges.column, memoryWires]
      ring
    | some column =>
      simp only [offsetColumn] at found
      split at found <;> simp only [Option.bind_eq_bind, Option.bind_none, Option.bind_some, reduceCtorEq] at found
      split at found <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at found
      obtain ⟨rfl, rfl⟩ := found
      refine ⟨_, rfl, ?_⟩
      simp [addressSpace, addressEncoding, MemoryAddress.code, Verification.IndirectPort.rawAddress, offsetColumn,
        Nat.unpair_pair, Challenges.embed, Challenges.column, memoryWires]
      ring

/-- A port read tuple has the value of the encoded model read token. -/
theorem portRead_tuple (port : MemoryPort) {row : SpecialMemoryContributionRelation}
    (found : portReadRelation port = some row) :
    tuple challenges (memoryWires assignment) row = some (challenges.memory.encode (readToken assignment port)) := by
  simp only [portReadRelation] at found
  cases relation : addressRelation port.address with
  | none => simp [relation] at found
  | some pair =>
    obtain ⟨space, word⟩ := pair
    simp only [relation, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at found
    subst found
    obtain ⟨term, addressFound, addressSame⟩ := address_port challenges assignment port.address relation
    simp only [tuple, addressFound, timestamp, fixedPair, List.toList_toArray, value_word, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq, encode_parts, readToken, MemoryPort.readCode, rawPair]
    rw [← addressSame]
    simp only [Challenges.column, Challenges.embed, memoryWires, Nat.cast_zero, map_zero, add_zero]
    ring

/-- A port write tuple has the value of the encoded model write token. -/
theorem portWrite_tuple (time : Vector Nat 2) (port : MemoryPort) {row : SpecialMemoryContributionRelation}
    (found : portWriteRelation time port = some row) :
    tuple challenges (memoryWires assignment) row = some (challenges.memory.encode
      ⟨port.address.code assignment, ((rawPair assignment time).1 + port.clock.offset, (rawPair assignment time).2),
        port.writeCode assignment⟩) := by
  simp only [portWriteRelation] at found
  cases relation : addressRelation port.address with
  | none => simp [relation] at found
  | some pair =>
    obtain ⟨space, word⟩ := pair
    simp only [relation, Option.bind_eq_bind, Option.bind_some] at found
    split at found <;> simp only [Option.pure_def, Option.some.injEq, reduceCtorEq] at found
    subst found
    obtain ⟨term, addressFound, addressSame⟩ := address_port challenges assignment port.address relation
    simp only [tuple, addressFound, timestamp, fixedPair, List.toList_toArray, value_word, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq, encode_parts, MemoryPort.writeCode, rawPair]
    rw [← addressSame]
    simp only [Challenges.column, Challenges.embed, memoryWires, map_add, map_natCast]
    ring

/-- A request tuple has the value of the encoded request token. -/
theorem request_tuple (request : Delegation.Requests.Request babyBearModulus) (time : Option (Vector Nat 2))
    {row : SpecialMemoryContributionRelation} (found : requestRelation request.csr time = some row) :
    tuple challenges (memoryWires assignment) row =
      some (challenges.memory.encode (request.token ((time.map (rawPair assignment)).getD (0, 0)))) := by
  simp only [requestRelation] at found
  split at found <;> simp only [Option.some.injEq, reduceCtorEq] at found
  subst found
  cases time with
  | none =>
    simp [tuple, address, timestamp, value, addressSpace, encode_parts, Delegation.Requests.Request.token,
      addressEncoding, valueEncoding, Nat.unpair_pair, Challenges.embed]
  | some time =>
    simp [tuple, address, timestamp, value, addressSpace, encode_parts, Delegation.Requests.Request.token,
      addressEncoding, valueEncoding, Nat.unpair_pair, Challenges.embed, Challenges.column, memoryWires, fixedPair,
      rawPair]
    ring

end Ports

end Airbender.Compiler.NativeMemoryBridge
