import Airbender.Review.Helpers.UnifiedReduced.PathPreparation
import Airbender.Proofs.UnifiedReduced.PCRelativePreparation
import Airbender.Proofs.ExternalBoundary.Requests
import Airbender.Proofs.UnifiedReduced.UnissuedWorkers

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- Original stateful decoding is functional at a public instruction address,
    even when the two entries use different native metadata projections. -/
theorem path_source_instruction_unique {Left Right : Type}
    {leftProjection : SailRV32.instruction → Option (DecoderData Left)}
    {rightProjection : SailRV32.instruction → Option (DecoderData Right)}
    {before : State} {left : Trace.ProgramEntry Left} {right : Trace.ProgramEntry Right}
    (leftSource : left.SourceWith before leftProjection)
    (rightSource : right.SourceWith before rightProjection) (pc : left.pc = right.pc) :
    left.instruction = right.instruction := by
  have leftBytes : (Cell.ram right.pc).read before = .ok left.bits before := pc ▸ leftSource.bytes
  have bits : left.bits = right.bits :=
    (EStateM.Result.ok.inj (leftBytes.symm.trans rightSource.bytes)).1
  have decoded := leftSource.decoded
  rw [bits] at decoded
  exact (EStateM.Result.ok.inj (decoded.symm.trans rightSource.decoded)).1

/-- Actual clock matching supplies a cycle at every in-range four-tick cut.
    No formula relating its PC to the elapsed clock is used. -/
theorem path_cycle_row [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p) {data : RequestTrace p} {before : State}
    {addresses : List (BitVec 32)} {cut : Nat}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut)
    (beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value)
    (aligned : cut % 4 = 0) :
    ∃ row ∈ data.machine.rows, Delegation.Caller.startClock row + 4 = cut := by
  have lowerAligned : (cut - 4) % 4 = 0 := by omega
  have count := machine_window_count hp inverse accepted inputs lowerAligned aligned (by omega)
    (by omega : (timeOfPair data.machine.initial.timestamp).value ≤ cut - 4) beforeTerminal
  have one : (data.windowMachineRows (cut - 4) cut).length = 1 := by rw [count]; omega
  have nonempty : data.windowMachineRows (cut - 4) cut ≠ [] := by
    intro empty
    rw [empty] at one
    simp at one
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have present := List.mem_of_mem_filter member
  have range := of_decide_eq_true (List.mem_filter.mp member).2
  have clock := machine_clock_facts hp inverse accepted inputs present
  exact ⟨row, present, by omega⟩

/-- Public preparation bytes cannot also decode as a delegation CSR. -/
theorem path_preparation_ordinary [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5} {write : PathWrite}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathPreparation data program cut register write)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (last : Delegation.Caller.startClock row + 4 = cut) : row ∉ data.callers := by
  obtain ⟨entry, present, pc, encoding⟩ := scope.code row member last
  have source := run_program_sources ordinaryProgram entry present
  intro caller
  have decoded := accepted.decoded row caller
  change ∃ i : Fin data.program.length, row.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  let called := data.program.get i
  have calledSource := run_program_sources publicProgram.image called (List.get_mem _ _)
  have actual : row.start.word = Word.ofBitVec called.pc :=
    caller_query_pc_word (by dsimp [limbBase]; norm_num [timestampBase] at hp; omega) query
  have samePC : entry.pc = called.pc := by rw [pc, actual, Word.ofBitVec_roundtrip]
  have same := path_source_instruction_unique source calledSource samePC
  have fields := calledSource.fields
  rw [← same, encoding] at fields
  cases write with
  | literal literal =>
    cases literal <;> simp [PathWrite.instruction, ControlLiteral.instruction,
      Delegation.Caller.decoderFields] at fields
  | auipc immediate => simp [PathWrite.instruction, Delegation.Caller.decoderFields] at fields

/-- The same recovered public entry supplies the actual ordinary decoder query
    and preparation form; no straight-line registry is required. -/
theorem path_preparation_entry [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5} {write : PathWrite}
    (accepted : MixedMemoryAccepted data program)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathPreparation data program cut register write)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (ordinary : row ∉ data.callers) (last : Delegation.Caller.startClock row + 4 = cut) :
    ∃ entry ∈ program, row.decoderQuery = entry.query ∧
      entry.pc = row.start.word.toBitVec ∧ entry.instruction = write.instruction register := by
  obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded row member ordinary)
  have actual : row.start.word = Word.ofBitVec entry.pc := by
    cases row with
    | mk family w =>
      cases family
      exact native_query_pc_word (by dsimp [limbBase]; norm_num [timestampBase] at hp; omega) query
  have pc : entry.pc = row.start.word.toBitVec := by rw [actual, Word.ofBitVec_roundtrip]
  obtain ⟨selected, included, selectedPC, encoding⟩ := scope.code row member last
  have same := path_source_instruction_unique (run_program_sources ordinaryProgram entry present)
    (run_program_sources ordinaryProgram selected included) (pc.trans selectedPC.symm)
  exact ⟨entry, present, query, pc, same.trans encoding⟩

/-- Native request matching derives an empty worker window for the public
    preparation cycle. Earlier calls, branches, jumps and repeated PCs remain. -/
theorem path_preparation_workers_empty [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {register : BitVec 5} {write : PathWrite}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathPreparation data program cut register write) (aligned : cut % 4 = 0) :
    data.workers.windowRows (cut - 4) cut = [] := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨row, present, last⟩ := path_cycle_row size inverse accepted.toRequestChecks publicProgram
    scope.afterInitial scope.beforeTerminal aligned
  have positive := machine_native_clock_positive size inverse accepted publicProgram image present
  have lowerAligned : (cut - 4) % 4 = 0 := by omega
  have requests := request_windows size inverse accepted.toRequestChecks publicProgram
    lowerAligned aligned (by omega : 2 ≤ cut - 4)
  by_contra nonempty
  obtain ⟨worker, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨caller, matched, _⟩ := requests.workerMatches worker member
  have called : caller ∈ data.callers := List.mem_of_mem_filter matched.1
  have machine : caller ∈ data.machine.rows := List.mem_of_mem_filter called
  have range := of_decide_eq_true (List.mem_filter.mp matched.1).2
  have clock := machine_clock_facts size inverse accepted.toRequestChecks publicProgram machine
  have final : Delegation.Caller.startClock caller + 4 = cut := by omega
  exact path_preparation_ordinary size accepted publicProgram ordinaryProgram scope machine final called

/-- The public literal form derives the native value from canonical x0 reads.
    The zero-read fact is obtained from raw initialized token matching below. -/
theorem path_literal_row_output [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5} {literal : ControlLiteral}
    (accepted : MixedMemoryAccepted data program)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathPreparation data program cut register (.literal literal)) (nonzero : register ≠ 0)
    (zeroReads : ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register register).addressCode ∧
      (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).word.toBitVec = literal.value := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, present, query, _, encoding⟩ := path_preparation_entry hp accepted
    ordinaryProgram scope member ordinary last
  change decoderQuery w = entry.query at query
  have source := run_program_sources ordinaryProgram entry present
  have fields := source.fields
  rw [encoding, PathWrite.instruction, literal_fields nonzero] at fields
  have data : entry.data = ⟨.machine, 0, 0, register, Word.ofBitVec literal.value, 1, 0⟩ := (Option.some.inj fields).symm
  have size : 524288 < p := by norm_num [timestampBase] at hp; omega
  have flags := UnifiedReduced.Proofs.decoder_selectors size core (by rw [data]; change 1 < 524288; decide) query
  have selected : w 11 = 1 := by simpa [data, importedConstraintsDecoderColumns] using flags 0
  have sourceRAM : w 28 = 0 := by simpa [data, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 17
  have destinationRAM : w 29 = 0 := by simpa [data, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 18
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have indices : (w 5).val = 0 ∧ (w 6).val = 0 ∧ (w 7).val = register.toNat := by
    simpa [data, importedConstraintsDecoderColumns] using indices
  have lower := Verification.assertion_of_holds core ⟨29, by rw [UnifiedReduced.constraint_count]; decide⟩
  have upper := Verification.assertion_of_holds core ⟨30, by rw [UnifiedReduced.constraint_count]; decide⟩
  have destinationLower := Verification.assertion_of_holds core ⟨31, by rw [UnifiedReduced.constraint_count]; decide⟩
  have destinationUpper := Verification.assertion_of_holds core ⟨32, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, sourceRAM] at lower upper
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, destinationRAM] at destinationLower destinationUpper
  have rightLocation : w 38 = w 6 := by linear_combination lower
  have rightUpper : w 39 = 0 := by linear_combination upper
  have outputLocation : w 44 = w 7 := by linear_combination destinationLower
  have outputUpper : w 45 = 0 := by linear_combination destinationUpper
  have portMember (i : Fin 3) : importedConstraintsMemoryPorts[i] ∈ machinePorts (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by
    rw [machine_ports_ordinary member ordinary]
    simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  have firstZero := zeroReads _ (mixed_machine_member member (portMember 0)) (by
    simpa [readToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, Cell.register, pairCode]
      using congrArg (Nat.pair 0) indices.1)
  have secondZero := zeroReads _ (mixed_machine_member member (portMember 1)) (by
    simpa [readToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
      sourceRAM, rightLocation, rightUpper] using congrArg (Nat.pair 0) indices.2.1)
  change Nat.pair (w 36).val (w 37).val = Nat.pair 0 0 at firstZero
  change Nat.pair (w 42).val (w 43).val = Nat.pair 0 0 at secondZero
  have first := Nat.pair_eq_pair.mp firstZero
  have second := Nat.pair_eq_pair.mp secondZero
  have operands : w 36 = 0 ∧ w 37 = 0 ∧ w 42 = 0 ∧ w 43 = 0 :=
    ⟨(ZMod.val_eq_zero _).mp first.1, (ZMod.val_eq_zero _).mp first.2,
      (ZMod.val_eq_zero _).mp second.1, (ZMod.val_eq_zero _).mp second.2⟩
  have immediate := native_query_immediate_word (by dsimp [limbBase]; omega)
    (by rw [data]; exact Word.ofBitVec_bound _) query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at immediate
  rw [data] at immediate
  have result := literal_operands_result (by omega) core (accepted.active _ member) selected operands
    (immediate.symm ▸ Word.ofBitVec_bound literal.value)
  rw [immediate, Word.ofBitVec_roundtrip] at result
  constructor
  · simp [writeToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
      destinationRAM, outputLocation, outputUpper, indices.2.2]
  · simpa [write_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using result

/-- AUIPC uses the recovered occurrence PC, including after jumps and on loop
    revisits. No elapsed-clock address is substituted. -/
theorem path_auipc_row_output [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5} {immediate : BitVec 20}
    (accepted : MixedMemoryAccepted data program)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathPreparation data program cut register (.auipc immediate)) (nonzero : register ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register register).addressCode ∧
      (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).word.toBitVec =
        (⟨.machine, w⟩ : Trace.Row p UnifiedFamily).start.word.toBitVec +
          (immediate ++ (0 : BitVec 12)) := by
  have size : 524288 < p := by norm_num [timestampBase] at hp; omega
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, present, query, address, encoding⟩ := path_preparation_entry hp accepted
    ordinaryProgram scope member ordinary last
  change decoderQuery w = entry.query at query
  have fields := (run_program_sources ordinaryProgram entry present).fields
  rw [encoding, PathWrite.instruction, auipc_fields nonzero] at fields
  have metadata : entry.data = ⟨.machine, 0, 0, register, Word.ofBitVec (immediate ++ (0 : BitVec 12)), 4, 0⟩ :=
    (Option.some.inj fields).symm
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core
    (by rw [metadata]; change 4 < 524288; decide) query
  have selected : w 13 = 1 := by simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 2
  have destinationRAM : w 29 = 0 := by
    simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 18
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have target : (w 7).val = register.toNat := by simpa [metadata, importedConstraintsDecoderColumns] using indices.2.2
  have lower := Verification.assertion_of_holds core ⟨31, by rw [UnifiedReduced.constraint_count]; decide⟩
  have upper := Verification.assertion_of_holds core ⟨32, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, destinationRAM] at lower upper
  have location : w 44 = w 7 := by linear_combination lower
  have top : w 45 = 0 := by linear_combination upper
  have pc := native_query_pc_word (by dsimp [limbBase]; omega) query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at pc
  have imm := native_query_immediate_word (by dsimp [limbBase]; omega)
    (by rw [metadata]; exact Word.ofBitVec_bound _) query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at imm
  rw [metadata] at imm
  have result := auipc_result (by omega) core (accepted.active _ member) selected
    (pc.symm ▸ Word.ofBitVec_bound entry.pc) (imm.symm ▸ Word.ofBitVec_bound _)
  rw [pc, imm, Word.ofBitVec_roundtrip, Word.ofBitVec_roundtrip] at result
  constructor
  · simp [writeToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
      destinationRAM, location, top, target]
  · simpa [write_word, importedConstraintsMemoryPorts, WordColumns.evaluate, address] using result

/-- Raw initialized matching derives the actual preparation token before any
    extended-round mask or architectural execution assumption is available. -/
theorem path_preparation_token [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {register : BitVec 5} {write : PathWrite} {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathPreparation data program cut register write) (nonzero : register ≠ 0)
    (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ row ∈ data.machine.rows, Delegation.Caller.startClock row + 4 = cut ∧
      ∃ entry ∈ program, entry.pc = row.start.word.toBitVec ∧
        entry.instruction = write.instruction register ∧
        ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
          (timeOfPair token.time).value = cut - 2 ∧
          token.word = Word.ofBitVec (write.value entry.pc) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size inverse accepted publicProgram image requests
  have zero := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero image)
    (mixed_zero_rules_of_program size inverse accepted publicProgram ordinaryProgram requests)
  have empty := path_preparation_workers_empty hp inverse accepted publicProgram ordinaryProgram image scope aligned
  obtain ⟨w, member, last, ordinary, present, timestamp, bounded⟩ := preparation_output_token hp inverse
    accepted publicProgram image empty scope.afterInitial scope.beforeTerminal aligned matching
  let row : Trace.Row p UnifiedFamily := ⟨.machine, w⟩
  let token := writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]
  have output : token.address = (Cell.register register).addressCode ∧
      token.word.toBitVec = write.value row.start.word.toBitVec := by
    cases write with
    | literal literal =>
      exact path_literal_row_output size accepted ordinaryProgram scope nonzero zero member ordinary last
    | auipc immediate =>
      exact path_auipc_row_output size accepted ordinaryProgram scope nonzero member ordinary last
  obtain ⟨entry, included, address, encoding⟩ := scope.code row member last
  have word : token.word = Word.ofBitVec (write.value entry.pc) := by
    apply Word.eq_of_value bounded (Word.ofBitVec_bound _)
    have equal := congrArg BitVec.toNat output.2
    rw [Word.toBitVec_toNat bounded, ← address] at equal
    exact equal.trans (Word.ofBitVec_value _).symm
  exact ⟨row, member, last, entry, included, address, encoding,
    token, present, output.1, timestamp, word⟩

/-- A boundary supplied by the separate memory argument turns the derived token
    into the actual architectural read, retaining its occurrence PC and time. -/
theorem path_preparation_at_boundary [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before atCut : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {register : BitVec 5} {write : PathWrite} {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathPreparation data program cut register write) (nonzero : register ≠ 0)
    (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst))
    (boundary : NativeBoundary tokens atCut cells) :
    PathPreparedControl data program tokens atCut cut register write := by
  obtain ⟨row, member, last, entry, included, pc, encoding,
    token, present, address, timestamp, word⟩ := path_preparation_token hp inverse accepted
      publicProgram ordinaryProgram image scope nonzero aligned matching
  obtain ⟨cell, _, code, read⟩ := native_boundary_read boundary present
  have same : cell = Cell.register register := cell_address_injective (code.trans address)
  subst cell
  have bits : token.word.toBitVec = write.value entry.pc := by rw [word, Word.ofBitVec_roundtrip]
  exact ⟨row, member, last, entry, included, pc, encoding, bits ▸ read,
    token, present, address, timestamp, word⟩

end Airbender.UnifiedReduced.Caller.Proofs
