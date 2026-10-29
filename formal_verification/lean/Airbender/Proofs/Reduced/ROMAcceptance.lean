import Airbender.Proofs.Reduced.NativeROM

namespace Airbender.Delegation.Caller.NativeROM.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

theorem row_active [Fact p.Prime] (initial : State) {row : Trace.Row p PooledFamily}
    (active : row.assignment row.columns.execute = 1) :
    (PooledROMView.row initial row).assignment (PooledROMView.row initial row).columns.execute = 1 := by
  rcases row with ⟨family, w⟩
  cases family with
  | wordMemory =>
    dsimp only [PooledROMView.row, ROMView.row]
    split <;> simpa [Trace.Row.columns, CircuitLayout.columns,
      WordMemory.importedConstraintsTraceColumns, ROMView.readData] using active
  | subwordMemory =>
    dsimp only [PooledROMView.row]
    split <;> simpa [Trace.Row.columns, CircuitLayout.columns,
      SubwordMemory.importedConstraintsTraceColumns, PooledROMView.subwordReadData] using active
  | addSub | jumpBranchSlt | mulDiv | shiftBinop => exact active

/-- Public ROM interpretation preserves every native equation and exact matching check. -/
theorem accepted [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072) (initial : State)
    {data : RequestTrace p} {program : List PooledProgramEntry}
    (nativeAccepted : MixedMemoryAccepted data program) (requests : RequestBinding data initial)
    (facts : Transfer.Facts (mixedData data)) {cells : List Cell}
    (seed : data.machine.initialMemory = ROMView.nativeBootImage cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows) :
    MixedMemoryAccepted (view initial data) program := by
  constructor
  · constructor
    · intro row member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact PooledROMView.row_holds initial original data.machine.rom
        (nativeAccepted.constraints original present)
    · intro row member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact row_active initial (nativeAccepted.active original present)
    · simpa only [view, PooledROMView.data, List.map_map, Function.comp_def,
        PooledROMView.row_start, PooledROMView.row_finish] using nativeAccepted.states
    · intro row member
      rw [callers_unchanged] at member
      exact nativeAccepted.decoded row member
    · exact nativeAccepted.workerConstraints
    · exact nativeAccepted.workerActive
    · change Requests.Matching (view initial data).calls data.fulfillments
      rw [calls]
      exact nativeAccepted.requests
  · intro row member outside
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have ordinary : original ∉ data.callers := by
      intro included
      exact outside ((callers initial data).symm ▸ List.mem_map.mpr ⟨original, included, rfl⟩)
    simpa only [PooledROMView.row_query, PooledROMView.row_family] using
      nativeAccepted.ordinaryDecoded original present ordinary
  · have matching := nativeAccepted.memory.map (ROMView.token initial)
    have reads := congrArg (List.map Prod.fst) (steps hp initial nativeAccepted requests facts seed ram)
    have writes := congrArg (List.map Prod.snd) (steps hp initial nativeAccepted requests facts seed ram)
    simp only [List.map_map, Function.comp_def] at reads writes
    change ((data.machine.initialMemory.map (ROMView.token initial)) ++ _).Perm
      ((data.machine.terminalMemory.map (ROMView.token initial)) ++ _)
    rw [reads, writes]
    simpa only [List.map_append, List.map_map, Function.comp_def] using matching

/-- Public ROM bytes give the same value at both ends of each ROM transfer. -/
theorem rom_token_refresh (initial : State) {left right : MemoryToken p}
    (same : left.address = right.address) (pc : BitVec 32)
    (inROM : pc.toNat < ROM.limit) (address : left.address = (Cell.ram pc).addressCode) :
    (ROMView.token initial left).value = (ROMView.token initial right).value := by
  have shadow : ROMView.shadow left.address := by
    rw [address]
    simp [ROMView.shadow, Cell.addressCode, Word.ofBitVec, limbBase]
    dsimp [ROM.limit] at inROM
    omega
  simp only [ROMView.token, ← same, if_pos shadow]

/-- The interpreted shared history preserves original public instruction bytes. -/
theorem rom_unchanged [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072) (initial : State)
    {data : RequestTrace p} {program : List PooledProgramEntry}
    (nativeAccepted : MixedMemoryAccepted data program) (requests : RequestBinding data initial)
    (facts : Transfer.Facts (mixedData data)) {cells : List Cell}
    (seed : data.machine.initialMemory = ROMView.nativeBootImage cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    {event : MemoryAccess} (member : event ∈ (view initial data).mixedSteps.map transferEvent)
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit)
    (address : event.2.1 = (Cell.ram pc).addressCode) : event.2.2.1 = event.2.2.2 := by
  rw [steps hp initial nativeAccepted requests facts seed ram, List.map_map] at member
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  apply rom_token_refresh initial (facts.addresses edge present) pc inROM
  simpa only [Function.comp_apply, transferEvent, ROMView.token_address] using address

end Airbender.Delegation.Caller.NativeROM.Proofs
