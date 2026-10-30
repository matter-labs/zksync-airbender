import Airbender.Proofs.FullUnsigned.CallerPorts
import Airbender.Proofs.FullUnsigned.MemoryFacts
import Airbender.Proofs.Reduced.ROMAcceptance

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open Delegation.Caller AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The full native pool supplies canonical addresses for ROM interpretation.
Both ordinary rows and selected standard or split callers retain exact transfers. -/
theorem unrolled_full_rom_cpu_steps
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    {cells : List Cell} (seed : trace.initialMemory = ROMView.nativeBootImage cells)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows) :
    (machinePorts (PooledROMView.row initial row)).toList.map (fun port =>
      (readToken (PooledROMView.row initial row).assignment port,
        writeToken (PooledROMView.row initial row).columns (PooledROMView.row initial row).assignment port)) =
    ((machinePorts row).toList.map (fun port =>
      (readToken row.assignment port, writeToken row.columns row.assignment port))).map
        (fun edge => (ROMView.token initial edge.1, ROMView.token initial edge.2)) := by
  let data : Delegation.Caller.RequestTrace babyBearModulus := ⟨trace, workers, []⟩
  have addressBounds (ordinary : row ∉ data.callers) :
      ∀ port ∈ row.ports, (port.address.word row.assignment).Bounded := by
    intro port present
    have inMachine : (readToken row.assignment port, writeToken row.columns row.assignment port) ∈ pooledSteps trace := by
      apply List.mem_flatMap.mpr
      refine ⟨row, member, List.mem_map.mpr ⟨port, ?_, rfl⟩⟩
      simpa [machine_ports_ordinary member ordinary] using present
    have inPool : (readToken row.assignment port, writeToken row.columns row.assignment port) ∈
        (unrolledFullMemoryData trace workers splitWorkers).steps :=
      List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inMachine)))
    have origin := keyed_origins MemoryToken.address (fun token => (timeOfPair token.time).value)
      facts.matching facts.addresses facts.order _ inPool
    change (readToken row.assignment port).address ∈ trace.initialMemory.map MemoryToken.address at origin
    rw [seed] at origin
    simp only [ROMView.nativeBootImage, List.map_map, Cell.initialToken] at origin
    obtain ⟨cell, _, equal⟩ := List.mem_map.mp origin
    rw [address_word equal.symm]
    exact cell_address_bound cell
  by_cases caller : row ∈ data.callers
  · rw [Delegation.Caller.NativeROM.Proofs.caller_row initial caller]
    rw [machine_ports_caller caller, List.map_map]
    apply List.map_congr_left
    intro port present
    have chosen : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment := by
      simpa only [Delegation.Caller.RequestTrace.callers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        using (List.mem_filter.mp caller).2
    have same : (readToken row.assignment port).address = (Cell.register 0).addressCode := by
      exact unrolled_full_caller_zero_ports setup lookup accepted excluded initialPC
        row member chosen.1 chosen.2 port (by rw [machine_ports_caller caller]; simpa using present)
    have outside : ¬ ROMView.shadow (readToken row.assignment port).address := by
      rw [same]
      simp [Cell.addressCode, ROMView.shadow]
    have address : (writeToken row.columns row.assignment port).address =
        (readToken row.assignment port).address := rfl
    simp only [Function.comp_apply, ROMView.token, address, outside, if_false]
  · have lifted : PooledROMView.row initial row ∉ (Delegation.Caller.NativeROM.view initial data).callers := by
      rw [Delegation.Caller.NativeROM.Proofs.callers]
      intro included
      obtain ⟨original, present, equal⟩ := List.mem_map.mp included
      have same := congrArg Trace.Row.family equal
      rw [PooledROMView.row_family, PooledROMView.row_family] at same
      have selected := (Delegation.Caller.Proofs.caller_member present).2
      have nativeFamily : row.family = .addSub := same.symm.trans selected
      have nativeView : PooledROMView.row initial row = row := by
        rcases row with ⟨kind, w⟩
        cases nativeFamily
        rfl
      have equalRows : original = row := (Delegation.Caller.NativeROM.Proofs.caller_row initial present).symm.trans (equal.trans nativeView)
      exact caller (equalRows ▸ present)
    have liftedMember : PooledROMView.row initial row ∈ (Delegation.Caller.NativeROM.view initial data).machine.rows :=
      List.mem_map.mpr ⟨row, member, rfl⟩
    rw [machine_ports_ordinary liftedMember lifted,
      machine_ports_ordinary member caller]
    have transfers := PooledROMView.row_transfers (by decide) initial row data.machine.rom
      (accepted.cpuEquations row member) (addressBounds caller)
    calc
      _ = (PooledROMView.row initial row).reads.zip (PooledROMView.row initial row).writes :=
        (Delegation.Caller.NativeROM.Proofs.zip_maps _ _ _).symm
      _ = (row.reads.map (ROMView.token initial)).zip (row.writes.map (ROMView.token initial)) := by
        rw [transfers.1, transfers.2]
      _ = (row.reads.zip row.writes).map
          (Prod.map (ROMView.token initial) (ROMView.token initial)) := List.zip_map
      _ = _ := by rw [Trace.Row.reads, Trace.Row.writes, Delegation.Caller.NativeROM.Proofs.zip_maps]; rfl

/-- Public ROM interpretation maps the entire native transfer pool exactly.
Standard and split worker RAM-domain inputs preserve their actual transfers. -/
theorem unrolled_full_rom_steps
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    {cells : List Cell} (seed : trace.initialMemory = ROMView.nativeBootImage cells)
    (ram : ExternalBoundary.WorkerRAM.Binding workers.rows)
    (splitRAM : ∀ edge ∈ splitWorkers.steps, ¬ ROMView.shadow edge.1.address) :
    (unrolledFullMemoryData (PooledROMView.data initial trace) workers splitWorkers).steps =
      (unrolledFullMemoryData trace workers splitWorkers).steps.map
        (fun edge => (ROMView.token initial edge.1, ROMView.token initial edge.2)) := by
  have standard := ExternalBoundary.WorkerRAM.Proofs.pool_transfers_unchanged initial ram
  have split : splitWorkers.steps.map (fun edge =>
      (ROMView.token initial edge.1, ROMView.token initial edge.2)) = splitWorkers.steps := by
    calc
      _ = splitWorkers.steps.map id := by
        apply List.map_congr_left
        intro edge member
        have same := Keccak.Split.Native.Proofs.preserved_addresses edge member
        have outside := splitRAM edge member
        simp only [ROMView.token, ← same, outside, if_false, id_eq]
      _ = splitWorkers.steps := List.map_id _
  change pooledSteps (PooledROMView.data initial trace) ++ workers.steps ++ splitWorkers.steps =
    (pooledSteps trace ++ workers.steps ++ splitWorkers.steps).map _
  rw [List.map_append, List.map_append, standard, split]
  congr 2
  simp only [pooledSteps, PooledROMView.data, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro row member
  exact unrolled_full_rom_cpu_steps setup lookup accepted excluded initialPC facts seed row member

/-- ROM interpretation preserves native equations, activity and all exact
state, request and memory permutations in the complete full unsigned pool. -/
theorem unrolled_full_rom_acceptance
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    {cells : List Cell} (seed : trace.initialMemory = ROMView.nativeBootImage cells)
    (ram : ExternalBoundary.WorkerRAM.Binding workers.rows)
    (splitRAM : ∀ edge ∈ splitWorkers.steps, ¬ ROMView.shadow edge.1.address) :
    UnrolledAcceptance (PooledROMView.data initial trace) workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)) := by
  refine {
    cpuEquations := ?_
    cpuActive := ?_
    workerEquations := accepted.workerEquations
    workerActive := accepted.workerActive
    states := ?_
    requests := ?_
    ram := ?_ }
  · intro row member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact PooledROMView.row_holds initial original trace.rom (accepted.cpuEquations original present)
  · intro row member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact Delegation.Caller.NativeROM.Proofs.row_active initial (accepted.cpuActive original present)
  · simpa only [PooledROMView.data, List.map_map, Function.comp_def,
      PooledROMView.row_start, PooledROMView.row_finish] using accepted.states
  · have calls : pooledCalls (PooledROMView.data initial trace) = pooledCalls trace :=
      Delegation.Caller.NativeROM.Proofs.calls initial ⟨trace, workers, []⟩
    rw [calls]
    exact accepted.requests
  · have steps := unrolled_full_rom_steps setup lookup accepted excluded initialPC facts seed ram splitRAM
    have reads := congrArg (List.map Prod.fst) steps
    have writes := congrArg (List.map Prod.snd) steps
    simp only [List.map_map, Function.comp_def] at reads writes
    have matching := accepted.ram.map (ROMView.token initial)
    change ((trace.initialMemory.map (ROMView.token initial)) ++
      (unrolledFullMemoryData (PooledROMView.data initial trace) workers splitWorkers).steps.map Prod.snd).Perm
      ((trace.terminalMemory.map (ROMView.token initial)) ++
        (unrolledFullMemoryData (PooledROMView.data initial trace) workers splitWorkers).steps.map Prod.fst)
    rw [reads, writes]
    simpa only [unrolledFullMemoryData, List.map_append, List.map_map, Function.comp_def] using matching

/-- ROM interpretation leaves every full-width public decoder query unchanged. -/
theorem unrolled_full_rom_lookup (initial : State)
    {trace : PooledTrace babyBearModulus}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    (lookup : UnrolledDecoderExactLookup trace masks columns) :
    UnrolledDecoderExactLookup (PooledROMView.data initial trace) masks columns := by
  intro row member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  simpa only [PooledROMView.row_family, PooledROMView.row_query] using lookup original present

/-- The interpreted full memory pool preserves every original public ROM word. -/
theorem unrolled_full_rom_unchanged
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    {cells : List Cell} (seed : trace.initialMemory = ROMView.nativeBootImage cells)
    (ram : ExternalBoundary.WorkerRAM.Binding workers.rows)
    (splitRAM : ∀ edge ∈ splitWorkers.steps, ¬ ROMView.shadow edge.1.address)
    {event : MemoryAccess}
    (member : event ∈ (unrolledFullMemoryData (PooledROMView.data initial trace) workers splitWorkers).steps.map transferEvent)
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit)
    (address : event.2.1 = (Cell.ram pc).addressCode) : event.2.2.1 = event.2.2.2 := by
  rw [unrolled_full_rom_steps setup lookup accepted excluded initialPC facts seed ram splitRAM,
    List.map_map] at member
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  apply Delegation.Caller.NativeROM.Proofs.rom_token_refresh initial (facts.addresses edge present) pc inROM
  simpa only [Function.comp_apply, transferEvent, ROMView.token_address] using address

end Airbender.Compiler.MachineTargets.Proofs
