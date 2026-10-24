import GKRProtocol.MemorySource

namespace Airbender.Compiler.Source
set_option warningAsError true

private def variableField (index : Nat) : MemoryField := .input (.Variable index)

private def registerOrRamSpace : Boolean → MemoryField
  | .Is index => .add (.constant 1) (.neg (variableField index))
  | .Not index => variableField index
  | .Constant bit => .constant (if bit then 0 else 1)

private def indirectAddress (base : MemoryWord) (dynamic : Option (Triple U32 Nat Nat))
    (offset : Nat) : MemoryWord :=
  let low := match dynamic with
    | none => base.low
    | some contribution => .add base.low (.scale contribution.first.val (variableField contribution.second))
  ⟨.add low (.constant offset), base.high⟩

/-- The source word/address expressions precede native placement and batching.
Integer alignment/range validity is a separate source primitive contract. -/
def MemoryAccess.sourceRows (writeTimestamp : MemoryWord) : MemoryAccess → MemoryRow × MemoryRow
  | .ConstantRegister query =>
      let address : MemoryWord := ⟨.constant query.reg_idx.val, .constant 0⟩
      (⟨.constant 0, address, .original query.read_timestamp, .representation query.read_value⟩,
       ⟨.constant 0, address, writeTimestamp.offset query.local_timestamp_in_cycle.val, .representation query.write_value⟩)
  | .RegisterOnly query =>
      let address : MemoryWord := ⟨variableField query.reg_idx, .constant 0⟩
      (⟨.constant 0, address, .original query.read_timestamp, .representation query.read_value⟩,
       ⟨.constant 0, address, writeTimestamp.offset query.local_timestamp_in_cycle.val, .representation query.write_value⟩)
  | .RegisterOrRam query =>
      let address := MemoryWord.original query.address
      let space := registerOrRamSpace query.is_register
      (⟨space, address, .original query.read_timestamp, .representation query.read_value⟩,
       ⟨space, address, writeTimestamp.offset query.local_timestamp_in_cycle.val, .representation query.write_value⟩)
  | .RamIndirect query =>
      let address := indirectAddress (.original query.base_address) query.variable_offset query.constant_offset.val
      (⟨.constant 1, address, .original query.read_timestamp, .representation query.read_value⟩,
       ⟨.constant 1, address, writeTimestamp.offset query.local_timestamp_in_cycle.val, .representation query.write_value⟩)

structure MemoryRequests where
  execute : Nat
  reads : Array MemoryRow
  writes : Array MemoryRow

private def MemoryRequests.push (requests : MemoryRequests) (rows : MemoryRow × MemoryRow) : MemoryRequests :=
  { requests with reads := requests.reads.push rows.1, writes := requests.writes.push rows.2 }

/-- Read-timestamp history slots use source request order. Native gate order,
cache IDs and lowered request metadata are not arguments to this function. -/
def memoryRequests (inputs : SemanticInputs) : Except String MemoryRequests := do
  match inputs.executor_machine_state, inputs.delegation_circuit_state with
  | some executor, none =>
      unless inputs.register_and_indirect_accesses.isEmpty do throw "executor source contains delegation register accesses"
      let baseTimestamp := MemoryWord.original executor.cycle_start_state.timestamp
      let mut result : MemoryRequests := ⟨executor.execute, #[], #[]⟩
      for query in inputs.memory_queries do result := result.push (query.sourceRows baseTimestamp)
      return result.push
        (⟨.constant 2, .zero, .original executor.cycle_start_state.timestamp, .original executor.cycle_start_state.pc⟩,
         ⟨.constant 2, .zero, .original executor.cycle_end_state.timestamp, .original executor.cycle_end_state.pc⟩)
  | none, some delegation =>
      unless inputs.memory_queries.isEmpty do throw "delegation source contains executor memory queries"
      let baseTimestamp := MemoryWord.original delegation.invocation_timestamp
      let mut result : MemoryRequests := ⟨delegation.execute, #[], #[]⟩
      for access in inputs.register_and_indirect_accesses do
        let (readValue, writeValue) := match access.register_access with
          | .Read readValue => (MemoryWord.original readValue, MemoryWord.original readValue)
          | .Write readValue writeValue => (MemoryWord.original readValue, MemoryWord.original writeValue)
        let registerAddress : MemoryWord := ⟨.constant access.register_index.val, .constant 0⟩
        result := result.push
          (⟨.constant 0, registerAddress, .history result.reads.size, readValue⟩,
           ⟨.constant 0, registerAddress, baseTimestamp.offset 2, writeValue⟩)
        for indirect in access.indirect_accesses do
          let (dataRead, dataWrite, dynamic, offset, aligned) := match indirect with
            | .Read readValue variableDependent constantOffset noOverflow _ =>
                let data := MemoryWord.original readValue
                (data, data, variableDependent, constantOffset.val, noOverflow)
            | .Write readValue writeValue variableDependent constantOffset noOverflow _ =>
                (MemoryWord.original readValue, MemoryWord.original writeValue,
                  variableDependent, constantOffset.val, noOverflow)
          unless aligned do throw "unsupported source indirect access with possible alignment overflow"
          let address := indirectAddress readValue dynamic offset
          result := result.push
            (⟨.constant 1, address, .history result.reads.size, dataRead⟩,
             ⟨.constant 1, address, baseTimestamp.offset 2, dataWrite⟩)
      let markerAddress : MemoryWord := ⟨.constant delegation.delegation_type.val, .constant 0⟩
      return result.push
        (⟨.constant 0, markerAddress, baseTimestamp, .zero⟩,
         ⟨.constant 0, markerAddress, .zero, .zero⟩)
  | _, _ => throw "source memory requires exactly one executor or delegation state"

def initializationRequests (pairs wordBits traceLog2 : Nat) : List (MemoryRow × MemoryRow) :=
  (List.range (2 * pairs)).map fun setIndex =>
    let address : MemoryWord :=
      ⟨.initializationAddress ⟨0, by decide⟩,
       .add (.initializationAddress ⟨1, by decide⟩) (.constant (setIndex * 2 ^ (traceLog2 + wordBits - 16)))⟩
    -- Teardown consumes the final state; initialization writes the zero state.
    (⟨.constant 1, address,
       ⟨.teardownTimestamp setIndex ⟨0, by decide⟩, .teardownTimestamp setIndex ⟨1, by decide⟩⟩,
       ⟨.teardownValue setIndex ⟨0, by decide⟩, .teardownValue setIndex ⟨1, by decide⟩⟩⟩,
     ⟨.constant 1, address, .zero, .zero⟩)

end Airbender.Compiler.Source
