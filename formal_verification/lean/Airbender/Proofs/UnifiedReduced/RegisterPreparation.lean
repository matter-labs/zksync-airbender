import Airbender.Review.Trace.UnifiedReduced.RegisterPreparation
import Airbender.Proofs.UnifiedReduced.PCRelativePreparation
import Airbender.Proofs.UnifiedReduced.WorkerExecution
import Airbender.Proofs.Trace.PortReads

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem register_immediate_fields {source register : BitVec 5} {immediate : BitVec 12}
    (nonzero : register ≠ 0) :
    Mixed.decoderFields (.ITYPE (immediate, .Regidx source, .Regidx register, .ADDI)) =
      some ⟨.machine, source, 0, register,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) immediate), 1, 0⟩ := by
  change register ≠ 0#5 at nonzero
  simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
    UnifiedReduced.arithmeticFields, Trace.arithmeticFields, DecoderData.mapFamily, nonzero]

/-- Native decoding and public modular clocks identify the actual ADDI metadata. -/
theorem register_immediate_preparation_entry [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {source register : BitVec 5} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : RegisterImmediatePreparation data program cut source register immediate) (nonzero : register ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.data = ⟨.machine, source, 0, register,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) immediate), 1, 0⟩ := by
  obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded _ member ordinary)
  have schedule := wrapped_program_pc_clock hp clockInverse setup accepted publicProgram ordinaryProgram scope.registry _ member
  have pc := native_query_pc_word (by dsimp [limbBase]; omega) query
  have bits : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily).start.word.toBitVec = entry.pc := by
    change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at pc
    change (Word.mk (w 0).val (w 1).val).toBitVec = entry.pc
    rw [pc, Word.ofBitVec_roundtrip]
  have clock : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) = cut - 4 := by omega
  have address : entry.pc = wrappedProgramAddress data (cut - 4) := by simpa only [bits, clock, wrappedProgramAddress] using schedule
  have fields := (run_program_sources ordinaryProgram entry present).fields
  rw [scope.atCut entry present address, register_immediate_fields nonzero] at fields
  have metadata : entry.data = ⟨.machine, source, 0, register,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) immediate), 1, 0⟩ := (Option.some.inj fields).symm
  change decoderQuery w = entry.query at query
  exact ⟨entry, present, query, metadata⟩

/-- Public ADDI decoding identifies the actual destination port independently
    of operand values, bounds and arithmetic results. -/
theorem register_immediate_row_destination [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {source register : BitVec 5} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : RegisterImmediatePreparation data program cut source register immediate) (nonzero : register ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register register).addressCode := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, _, query, metadata⟩ := register_immediate_preparation_entry hp clockInverse setup accepted
    publicProgram ordinaryProgram scope nonzero member ordinary last
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core (by rw [metadata]; change 1 < 524288; decide) query
  have destinationRAM : w 29 = 0 := by simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 18
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have index : (w 7).val = register.toNat := by simpa [metadata, importedConstraintsDecoderColumns] using indices.2.2
  have lower := Verification.assertion_of_holds core ⟨31, by rw [UnifiedReduced.constraint_count]; decide⟩
  have upper := Verification.assertion_of_holds core ⟨32, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, destinationRAM] at lower upper
  have location : w 44 = w 7 := by linear_combination lower
  have high : w 45 = 0 := by linear_combination upper
  simp [writeToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
    destinationRAM, location, high, index]

theorem register_immediate_row_output [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {source register : BitVec 5} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : RegisterImmediatePreparation data program cut source register immediate) (nonzero : register ≠ 0)
    (zeroReads : ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut)
    (leftBound : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded) :
    importedConstraintsMemoryPorts[0].address.code w = (Cell.register source).addressCode ∧
      (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register register).addressCode ∧
      (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).word.toBitVec =
        registerImmediateValue (readToken w importedConstraintsMemoryPorts[0]).word.toBitVec immediate := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, _, query, metadata⟩ := register_immediate_preparation_entry hp clockInverse setup accepted
    publicProgram ordinaryProgram scope nonzero member ordinary last
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core (by rw [metadata]; change 1 < 524288; decide) query
  have selected : w 11 = 1 := by simpa [metadata, importedConstraintsDecoderColumns] using flags 0
  have sourceRAM : w 28 = 0 := by simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 17
  have destinationRAM : w 29 = 0 := by simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 18
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have indices : (w 5).val = source.toNat ∧ (w 6).val = 0 ∧ (w 7).val = register.toNat := by
    simpa [metadata, importedConstraintsDecoderColumns] using indices
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
  have portMember : importedConstraintsMemoryPorts[1] ∈ machinePorts (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by
    rw [machine_ports_ordinary member ordinary]
    simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  have secondZero := zeroReads _ (mixed_machine_member member portMember) (by
    simpa [readToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
      sourceRAM, rightLocation, rightUpper] using congrArg (Nat.pair 0) indices.2.1)
  change Nat.pair (w 42).val (w 43).val = Nat.pair 0 0 at secondZero
  have second := Nat.pair_eq_pair.mp secondZero
  have right : w 42 = 0 ∧ w 43 = 0 := ⟨(ZMod.val_eq_zero _).mp second.1, (ZMod.val_eq_zero _).mp second.2⟩
  have readWord : (readToken w importedConstraintsMemoryPorts[0]).word = Word.mk (w 36).val (w 37).val := by
    simp [readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code]
  rw [readWord] at leftBound
  have imm := native_query_immediate_word (by dsimp [limbBase]; omega) (by rw [metadata]; exact Word.ofBitVec_bound _) query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at imm
  rw [metadata] at imm
  have result := immediate_add_result (by omega) core (accepted.active _ member) selected right leftBound
    (imm.symm ▸ Word.ofBitVec_bound _)
  rw [imm, Word.ofBitVec_roundtrip] at result
  refine ⟨?_, ?_, ?_⟩
  · simp [MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, indices.1]
  · simp [writeToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
      destinationRAM, outputLocation, outputUpper, indices.2.2]
  · change _ = (readToken w importedConstraintsMemoryPorts[0]).word.toBitVec + SailRV32.Functions.sign_extend (m := 32) immediate
    rw [readWord]
    simpa [write_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using result

/-- The actual first ADDI read consumes the retained source token at the
    preceding instruction cut. This raw matching lemma is shared by finite
    public dataflow proofs and does not require Sail states or round masks. -/
theorem register_immediate_source_word_of_value [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {source register : BitVec 5} {value : BitVec 32} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (scope : RegisterImmediatePreparation data program cut source register immediate)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register source).addressCode ∧
        token.word = Word.ofBitVec value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (readToken w importedConstraintsMemoryPorts[0]).word = Word.ofBitVec value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have floor := sourceFloor
  have cutFloor : 8 ≤ cut := by omega
  have sourceAligned : (cut - 4) % 4 = 0 := by omega
  have requests := request_binding size clockInverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size clockInverse accepted publicProgram initialization requests
  obtain ⟨start, earlier, later⟩ := Transfer.split_at facts (cut - 5)
  have prefixMatching := earlier.matching
  have cutoff : cut - 5 = (cut - 4) - 1 := by omega
  rw [cutoff, mixed_prefix_steps data (by omega)] at prefixMatching
  obtain ⟨token, present, address, word⟩ := seedToken start prefixMatching
  obtain ⟨entry, _, query, metadata⟩ := register_immediate_preparation_entry (by omega) clockInverse setup accepted
    publicProgram ordinaryProgram scope nonzero member ordinary last
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have sourceIndex : (w 5).val = source.toNat := by
    simpa [metadata, importedConstraintsDecoderColumns] using indices.1
  have sourceAddress : (readToken w importedConstraintsMemoryPorts[0]).address = (Cell.register source).addressCode := by
    simp [readToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, sourceIndex]
  have portMember : importedConstraintsMemoryPorts[0] ∈ machinePorts (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by
    rw [machine_ports_ordinary member ordinary]
    simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  have edge := mixed_machine_member member portMember
  have clocks := state_clock_inputs size clockInverse accepted.constraints accepted.states
    publicProgram.initialClock publicProgram.initialAligned _ member
  have writeTime := (write_time (by omega) (base := rawPair w importedConstraintsTraceColumns.initialTime)
    clocks.1 clocks.2 (by decide : importedConstraintsMemoryPorts[0].clock.offset < 4)).2
  have writeTime : (timeOfPair (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[0]).time).value = cut - 4 := by
    change (timeOfPair (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[0]).time).value =
      Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 0 at writeTime
    omega
  have inSuffix : (readToken w importedConstraintsMemoryPorts[0],
      writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[0]) ∈ Transfer.afterSteps (mixedData data) (cut - 5) := by
    apply List.mem_filter.mpr
    exact ⟨edge, by simp only [writeTime]; simp; omega⟩
  have readMember := later.matching.mem_iff.mpr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, inSuffix, rfl⟩)))
  have inStart : readToken w importedConstraintsMemoryPorts[0] ∈ start := by
    rcases List.mem_append.mp readMember with initial | written
    · exact initial
    · obtain ⟨previous, included, same⟩ := List.mem_map.mp written
      have previousTime : cut - 5 < (timeOfPair previous.2.time).value := by
        simpa only [Transfer.afterSteps, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] using
          (List.mem_filter.mp included).2
      have strict := facts.order _ edge
      change (timeOfPair (readToken w importedConstraintsMemoryPorts[0]).time).value <
        (timeOfPair (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[0]).time).value at strict
      change previous.2 = readToken w importedConstraintsMemoryPorts[0] at same
      rw [← same, writeTime] at strict
      omega
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp uniqueSeeds
  have equal := List.inj_on_of_nodup_map unique inStart present (sourceAddress.trans address.symm)
  exact congrArg MemoryToken.word equal |>.trans word

theorem register_immediate_preparation_token_of_value [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {source register : BitVec 5} {value : BitVec 32} {immediate : BitVec 12}
    {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (scope : RegisterImmediatePreparation data program cut source register immediate)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register source).addressCode ∧
        token.word = Word.ofBitVec value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧
      token.word = Word.ofBitVec (registerImmediateValue value immediate) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨w, member, last, ordinary, present, timestamp, bound⟩ := preparation_output_token hp clockInverse
    accepted publicProgram initialization scope.prefixScope scope.afterInitial scope.beforeTerminal aligned matching
  have sourceWord := register_immediate_source_word_of_value hp clockInverse setup accepted publicProgram ordinaryProgram
    initialization scope uniqueSeeds sourceFloor seedToken nonzero aligned member ordinary last
  have requests := request_binding size clockInverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size clockInverse accepted publicProgram initialization requests
  have zero := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero initialization)
    (mixed_zero_rules_of_program size clockInverse accepted publicProgram ordinaryProgram requests)
  have output := register_immediate_row_output (by omega) clockInverse setup accepted publicProgram ordinaryProgram
    scope nonzero zero member ordinary last (sourceWord.symm ▸ Word.ofBitVec_bound _)
  rw [sourceWord, Word.ofBitVec_roundtrip] at output
  refine ⟨_, present, output.2.1, timestamp, ?_⟩
  apply Word.eq_of_value bound (Word.ofBitVec_bound _)
  have equal := congrArg BitVec.toNat output.2.2
  rw [Word.toBitVec_toNat bound] at equal
  exact equal.trans (Word.ofBitVec_value _).symm

theorem register_immediate_source_word [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {source register : BitVec 5} {value : BitVec 32} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (scope : RegisterImmediatePreparation data program cut source register immediate)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register source).addressCode ∧
        (timeOfPair token.time).value = (cut - 4) - 2 ∧ token.word = Word.ofBitVec value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (readToken w importedConstraintsMemoryPorts[0]).word = Word.ofBitVec value := by
  exact register_immediate_source_word_of_value hp clockInverse setup accepted publicProgram ordinaryProgram initialization
    scope uniqueSeeds sourceFloor (fun start matching => by
      obtain ⟨token, present, address, _, word⟩ := seedToken start matching
      exact ⟨token, present, address, word⟩) nonzero aligned member ordinary last

theorem register_immediate_preparation_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {source register : BitVec 5} {value : BitVec 32} {immediate : BitVec 12}
    {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (scope : RegisterImmediatePreparation data program cut source register immediate)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register source).addressCode ∧
        (timeOfPair token.time).value = (cut - 4) - 2 ∧ token.word = Word.ofBitVec value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧
      token.word = Word.ofBitVec (registerImmediateValue value immediate) := by
  exact register_immediate_preparation_token_of_value hp clockInverse setup accepted publicProgram ordinaryProgram initialization
    scope uniqueSeeds sourceFloor (fun start prefixMatching => by
      obtain ⟨token, present, address, _, word⟩ := seedToken start prefixMatching
      exact ⟨token, present, address, word⟩) nonzero aligned matching

/-- Legacy literal→ADDI source interface, sharing the raw token proof. -/
theorem literal_addi_source_word [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {source register : BitVec 5} {literal : ControlLiteral} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (scope : LiteralAddiPreparation data program cut source register literal immediate)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (readToken w importedConstraintsMemoryPorts[0]).word = Word.ofBitVec literal.value := by
  exact register_immediate_source_word hp clockInverse setup accepted publicProgram ordinaryProgram initialization
    scope.step scope.initialUnique scope.seed.afterInitial
    (fun _ matching => preparation_token hp clockInverse accepted publicProgram ordinaryProgram initialization
      scope.seed scope.sourceNonzero (by have floor := scope.seed.afterInitial; omega) matching)
    nonzero aligned member ordinary last

/-- Legacy literal→ADDI token interface, sharing the public-chain derivation. -/
theorem literal_addi_preparation_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {source register : BitVec 5} {literal : ControlLiteral} {immediate : BitVec 12}
    {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (scope : LiteralAddiPreparation data program cut source register literal immediate)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧
      token.word = Word.ofBitVec (registerImmediateValue literal.value immediate) := by
  exact register_immediate_preparation_token hp clockInverse setup accepted publicProgram ordinaryProgram initialization
    scope.step scope.initialUnique scope.seed.afterInitial
    (fun _ matching => preparation_token hp clockInverse accepted publicProgram ordinaryProgram initialization
      scope.seed scope.sourceNonzero (by have floor := scope.seed.afterInitial; omega) matching)
    nonzero aligned matching

theorem register_immediate_control_preparation [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {source register : BitVec 5} {immediate : BitVec 12}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (scope : RegisterImmediatePreparation data program cut source register immediate)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    RegisterImmediatePreparedBoundaryExecution data before cells cut source register immediate := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  have initialized : Transfer.Inputs (mixedData data) before cells := ⟨inputs.initialization, inputs.distinct⟩
  have rules := mixed_write_rules hp rotationInverse accepted inputs
  have zeroRules := mixed_zero_rules size clockInverse accepted inputs requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero inputs.initialization) zeroRules
  have zero : ∀ edge ∈ (mixedData data).steps, edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
    intro edge member same
    have value := zeroRules edge member same (by
      intro previous present _ address
      exact zeroReads previous present address)
    rw [value]
    rfl
  obtain ⟨tokens, earlierFacts, _⟩ := Transfer.split_at facts (cut - 1)
  have matching := earlierFacts.matching
  rw [mixed_prefix_steps data (by have floor := scope.afterInitial; omega)] at matching
  obtain ⟨w, member, last, ordinary, tokenMember, timestamp, tokenBound⟩ := preparation_output_token hp clockInverse
    accepted inputs.publicProgram inputs.initialization scope.prefixScope scope.afterInitial scope.beforeTerminal aligned matching
  let row : Trace.Row p UnifiedFamily := ⟨.machine, w⟩
  have atClock : Delegation.Caller.startClock row = cut - 4 := by dsimp [row]; omega
  have portMember : importedConstraintsMemoryPorts[0] ∈ machinePorts row := by
    rw [machine_ports_ordinary member ordinary]
    simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  have leftBound := Transfer.read_bounds facts initialized rules _ (mixed_machine_member member portMember)
  have output := register_immediate_row_output (by omega) clockInverse inputs.setup accepted inputs.publicProgram
    inputs.ordinaryProgram scope nonzero zeroReads member ordinary last leftBound
  obtain ⟨_, events, _, _, permutation, order, history, _⟩ :=
    Transfer.native_sail_history facts initialized inputs.aligned zero
  have floor := machine_native_clock_positive size clockInverse accepted inputs.publicProgram inputs.initialization member
  have clocks := machine_clock_facts size clockInverse accepted.toRequestChecks inputs.publicProgram member
  change 4 ≤ Delegation.Caller.startClock row at floor
  change Delegation.Caller.startClock row % 4 = 0 ∧
    Delegation.Caller.finishClock row = Delegation.Caller.startClock row + 4 at clocks
  obtain ⟨atSource, atCut, _, past, current, _⟩ := history_window order history
    (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
  have cyclePerm := cycle_window_permutation size clockInverse accepted.toRequestChecks inputs.publicProgram requests permutation member (by omega)
  have cycleOrder : (events.filter fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)).Pairwise
      (fun a b => b.1 ≤ a.1) := order.sublist List.filter_sublist
  have native := ordinary_cycle_history size clockInverse accepted.toRequestChecks inputs.publicProgram
    member ordinary cyclePerm cycleOrder current
  have pastPerm := permutation.filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)
  have pastEqual : ((data.mixedSteps.map transferEvent).filter fun event =>
      decide (event.1 ≤ Delegation.Caller.startClock row)) = ((data.prefixSteps (cut - 4)).map transferEvent) := by
    rw [List.filter_map]
    apply congrArg (List.map transferEvent)
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def, decide_eq_true_eq, transferEvent]
    rw [atClock]
    omega
  change (events.filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)).Perm
    ((data.mixedSteps.map transferEvent).filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)) at pastPerm
  rw [pastEqual] at pastPerm
  have read := native_history_read (columns := importedConstraintsTraceColumns) (ports := importedConstraintsMemoryPorts)
    (w := w) 1 rfl rfl rfl native (by simp [importedConstraintsMemoryPorts]) output.1
  have read : (Cell.register source).read atSource = .ok (readToken w importedConstraintsMemoryPorts[0]).word.toBitVec atSource := by
    simpa only [readToken, MemoryToken.word, memoryWord, Word.toBitVec, Word.value] using read
  have written := native_history_write (columns := importedConstraintsTraceColumns) (ports := importedConstraintsMemoryPorts)
    (w := w) 1 rfl rfl rfl native rfl output.2.1
  change run ((Cell.register register).write
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).word.toBitVec) atSource = .ok () atCut at written
  rw [output.2.2] at written
  obtain ⟨after, actual, readback⟩ := cell_write_readback (Cell.register register)
    (registerImmediateValue (readToken w importedConstraintsMemoryPorts[0]).word.toBitVec immediate) atSource (by
      intro same
      exact False.elim (nonzero (Cell.register.inj same)))
  have same := (EStateM.Result.ok.inj (actual.symm.trans written)).2
  subst after
  have word : (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).word =
      Word.ofBitVec (registerImmediateValue (readToken w importedConstraintsMemoryPorts[0]).word.toBitVec immediate) := by
    apply Word.eq_of_value tokenBound (Word.ofBitVec_bound _)
    have equal := congrArg BitVec.toNat output.2.2
    rw [Word.toBitVec_toNat tokenBound] at equal
    exact equal.trans (Word.ofBitVec_value _).symm
  exact ⟨row, member, last, tokens, _, atSource, atCut, pastPerm, past, native, matching,
    _, read, readback, _, tokenMember, output.2.1, timestamp, word⟩

end Airbender.UnifiedReduced.Caller.Proofs
