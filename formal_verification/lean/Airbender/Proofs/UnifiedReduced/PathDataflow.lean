import Airbender.Review.Helpers.UnifiedReduced.PathDataflow
import Airbender.Proofs.UnifiedReduced.PathPreparation
import Airbender.Proofs.UnifiedReduced.RegisterDataflow

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- A public instruction known syntactically to be outside the CSR projection
    cannot be selected as a caller at this occurrence. -/
theorem path_instruction_ordinary [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {instruction : SailRV32.instruction}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathInstructionPreparation data program cut instruction)
    (notCaller : Delegation.Caller.decoderFields instruction = none)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (last : Delegation.Caller.startClock row + 4 = cut) : row ∉ data.callers := by
  obtain ⟨entry, present, pc, encoding⟩ := scope.code row member last
  intro caller
  have decoded := accepted.decoded row caller
  change ∃ i : Fin data.program.length, row.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  let called := data.program.get i
  have source := run_program_sources ordinaryProgram entry present
  have calledSource := run_program_sources publicProgram.image called (List.get_mem _ _)
  have actual : row.start.word = Word.ofBitVec called.pc :=
    caller_query_pc_word (by dsimp [limbBase]; norm_num [timestampBase] at hp; omega) query
  have samePC : entry.pc = called.pc := by rw [pc, actual, Word.ofBitVec_roundtrip]
  have same := path_source_instruction_unique source calledSource samePC
  have fields := calledSource.fields
  rw [← same, encoding, notCaller] at fields
  cases fields

/-- Query and original instruction at a recovered actual occurrence. -/
theorem path_instruction_entry [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {oa : List (BitVec 32)} {cut : Nat} {instruction : SailRV32.instruction}
    (accepted : MixedMemoryAccepted data program)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathInstructionPreparation data program cut instruction)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (ordinary : row ∉ data.callers) (last : Delegation.Caller.startClock row + 4 = cut) :
    ∃ entry ∈ program, row.decoderQuery = entry.query ∧
      entry.pc = row.start.word.toBitVec ∧ entry.instruction = instruction := by
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

/-- Public non-CSR code and native request matching exclude workers only from
    this occurrence's final cycle, without making earlier gaps inert. -/
theorem path_instruction_workers_empty [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {instruction : SailRV32.instruction}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathInstructionPreparation data program cut instruction)
    (notCaller : Delegation.Caller.decoderFields instruction = none) (aligned : cut % 4 = 0) :
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
  exact path_instruction_ordinary size accepted publicProgram ordinaryProgram scope notCaller machine final called

/-- Pure arithmetic writes to x0 retain the original native NOP metadata.
    Discarded loads are outside this syntax and this statement. -/
theorem path_discarded_arithmetic_fields {instruction : SailRV32.instruction}
    (form : ArithmeticRegisterWrite instruction 0) :
    Mixed.decoderFields instruction = some ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by
  cases form <;> rfl

/-- Every admitted public frame form is syntactically outside the CSR family. -/
theorem path_frame_not_caller {register : BitVec 5} {instruction : SailRV32.instruction}
    (form : PathRegisterFrame register instruction) : Delegation.Caller.decoderFields instruction = none := by
  cases form with
  | write form _ _ =>
    cases form with
    | arithmetic form => cases form <;> rfl
    | binary form => cases form <;> rfl
    | comparison form => cases form <;> rfl
    | custom form => cases form <;> rfl
  | discarded form => cases form <;> rfl
  | load => rfl
  | store => rfl
  | branch => rfl
  | jal => rfl
  | jalr => rfl

/-- Public syntax identifies the destination footprint, including branch/jump
    destinations and RAM stores. This is not an assumed state frame. -/
theorem path_frame_fields {register : BitVec 5} {instruction : SailRV32.instruction}
    {fields : DecoderData UnifiedFamily} (form : PathRegisterFrame register instruction)
    (nonzero : register ≠ 0) (decoded : Mixed.decoderFields instruction = some fields) :
    fields.mask < 524288 ∧ (fields.mask.testBit 18 = true ∨
      (fields.mask.testBit 18 = false ∧ fields.rd ≠ register)) := by
  cases form with
  | write form destinationNonzero different =>
    obtain ⟨destination, bound, bank⟩ := public_register_write_fields form destinationNonzero decoded
    refine ⟨bound, Or.inr ⟨bank, ?_⟩⟩
    rw [destination]
    exact different
  | discarded form =>
    rw [path_discarded_arithmetic_fields form] at decoded
    have same := Option.some.inj decoded
    subst fields
    exact ⟨by decide, Or.inr ⟨by decide, Ne.symm nonzero⟩⟩
  | load immediate source destination different =>
    by_cases zero : destination = 0#5
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        Trace.arithmeticFields, UnifiedReduced.arithmeticFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 1 < 524288; decide, Or.inr ⟨rfl, Ne.symm nonzero⟩⟩
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        UnifiedReduced.arithmeticFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 131072 < 524288; decide, Or.inr ⟨by change (131072 : Nat).testBit 18 = false; decide, different⟩⟩
  | store immediate stored source =>
    simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      UnifiedReduced.arithmeticFields, DecoderData.mapFamily] at decoded
    subst fields
    exact ⟨by change 262144 < 524288; decide, Or.inl (by change (262144 : Nat).testBit 18 = true; decide)⟩
  | branch immediate right left operation =>
    simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily] at decoded
    subst fields
    exact ⟨by change 24576 < 524288; decide, Or.inr ⟨by change (24576 : Nat).testBit 18 = false; decide, Ne.symm nonzero⟩⟩
  | jal immediate destination different =>
    by_cases zero : destination = 0#5
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 17408 < 524288; decide, Or.inr ⟨by change (17408 : Nat).testBit 18 = false; decide, Ne.symm nonzero⟩⟩
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 1024 < 524288; decide, Or.inr ⟨by change (1024 : Nat).testBit 18 = false; decide, different⟩⟩
  | jalr immediate source destination different =>
    by_cases zero : destination = 0#5
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 18432 < 524288; decide, Or.inr ⟨by change (18432 : Nat).testBit 18 = false; decide, Ne.symm nonzero⟩⟩
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 2048 < 524288; decide, Or.inr ⟨by change (2048 : Nat).testBit 18 = false; decide, different⟩⟩

/-- The actual native write address is disjoint from the tracked register,
    derived from original instruction syntax and native decoder/mapping equations. -/
theorem path_frame_row_disjoint [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5} {instruction : SailRV32.instruction}
    (accepted : MixedMemoryAccepted data program)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathInstructionPreparation data program cut instruction)
    (form : PathRegisterFrame register instruction) (nonzero : register ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address ≠
      (Cell.register register).addressCode := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, present, query, _, encoding⟩ := path_instruction_entry (by norm_num [timestampBase]; omega)
    accepted ordinaryProgram scope member ordinary last
  change decoderQuery w = entry.query at query
  have fields := (run_program_sources ordinaryProgram entry present).fields
  rw [encoding] at fields
  obtain ⟨bound, bank | ⟨bank, different⟩⟩ := path_frame_fields form nonzero fields
  · have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core bound query
    have ram : w 29 = 1 := by
      simpa [importedConstraintsDecoderColumns, bank] using flags 18
    intro same
    simp [writeToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode, ram] at same
  · have destination := decoded_frame_row_destination hp core query (destination := entry.data.rd) rfl bound bank
    intro same
    have cells : Cell.register entry.data.rd = Cell.register register :=
      cell_address_injective (destination.symm.trans same)
    exact different (Cell.register.inj cells)

/-- Every actual access to the tracked GPR in this ordinary gap preserves its
    word. Reads may still refresh timestamps, and other native writes remain. -/
theorem path_frame_refreshes [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {register : BitVec 5} {instruction : SailRV32.instruction}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathInstructionPreparation data program cut instruction)
    (form : PathRegisterFrame register instruction) (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, edge.1.address = (Cell.register register).addressCode →
      edge.2.value = edge.1.value := by
  have empty := path_instruction_workers_empty hp inverse accepted publicProgram ordinaryProgram image
    scope (path_frame_not_caller form) aligned
  apply ordinary_frame_refreshes hp inverse accepted.toRequestChecks publicProgram empty
    scope.afterInitial scope.beforeTerminal aligned
  intro w member ordinary last
  exact path_frame_row_disjoint (by omega) accepted ordinaryProgram scope form nonzero member ordinary last

/-- Public ADDI syntax identifies all native metadata at the actual occurrence. -/
theorem path_addi_entry [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {oa : List (BitVec 32)} {cut : Nat} {source register : BitVec 5} {immediate : BitVec 12}
    (accepted : MixedMemoryAccepted data program)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathInstructionPreparation data program cut
      (.ITYPE (immediate, .Regidx source, .Regidx register, .ADDI))) (nonzero : register ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.data = ⟨.machine, source, 0, register,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) immediate), 1, 0⟩ := by
  obtain ⟨entry, present, query, _, encoding⟩ := path_instruction_entry hp accepted
    ordinaryProgram scope member ordinary last
  have fields := (run_program_sources ordinaryProgram entry present).fields
  rw [encoding, register_immediate_fields nonzero] at fields
  exact ⟨entry, present, query, (Option.some.inj fields).symm⟩

/-- The ADDI result uses its actual matched source word and encoded immediate. -/
theorem path_addi_row_output [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {oa : List (BitVec 32)} {cut : Nat} {source register : BitVec 5} {immediate : BitVec 12}
    (accepted : MixedMemoryAccepted data program)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathInstructionPreparation data program cut
      (.ITYPE (immediate, .Regidx source, .Regidx register, .ADDI))) (nonzero : register ≠ 0)
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
  obtain ⟨entry, _, query, metadata⟩ := path_addi_entry (by norm_num [timestampBase]; omega) accepted
    ordinaryProgram scope nonzero member ordinary last
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core (by rw [metadata]; change 1 < 524288; decide) query
  have selected : w 11 = 1 := by simpa [metadata, importedConstraintsDecoderColumns] using flags 0
  have sourceRAM : w 28 = 0 := by simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 17
  have destinationRAM : w 29 = 0 := by simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 18
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have indices : (w 5).val = source.toNat ∧ (w 6).val = 0 ∧ (w 7).val = register.toNat := by
    simpa [metadata, importedConstraintsDecoderColumns] using indices
  have lower := Verification.assertion_of_holds core ⟨26, by rw [UnifiedReduced.constraint_count]; decide⟩
  have upper := Verification.assertion_of_holds core ⟨27, by rw [UnifiedReduced.constraint_count]; decide⟩
  have destinationLower := Verification.assertion_of_holds core ⟨28, by rw [UnifiedReduced.constraint_count]; decide⟩
  have destinationUpper := Verification.assertion_of_holds core ⟨29, by rw [UnifiedReduced.constraint_count]; decide⟩
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

/-- The derived source value is consumed from the unique raw prefix token.
    This internal transport lemma is instantiated by dataflow induction below. -/
theorem path_addi_source_word [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {source register : BitVec 5} {value : BitVec 32} {immediate : BitVec 12}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (scope : PathInstructionPreparation data program cut
      (.ITYPE (immediate, .Regidx source, .Regidx register, .ADDI)))
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register source).addressCode ∧ token.word = Word.ofBitVec value)
    (nonzero : register ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (readToken w importedConstraintsMemoryPorts[0]).word = Word.ofBitVec value := by
  obtain ⟨start, prefixMatching, inStart, unique⟩ := first_port_prefix_token hp clockInverse
    accepted publicProgram initialization uniqueSeeds (by omega) member ordinary last
  obtain ⟨token, present, address, word⟩ := seedToken start prefixMatching
  obtain ⟨entry, _, query, metadata⟩ := path_addi_entry (by norm_num [timestampBase]; omega) accepted
    ordinaryProgram scope nonzero member ordinary last
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have sourceIndex : (w 5).val = source.toNat := by
    simpa [metadata, importedConstraintsDecoderColumns] using indices.1
  have sourceAddress : (readToken w importedConstraintsMemoryPorts[0]).address = (Cell.register source).addressCode := by
    simp [readToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, sourceIndex]
  have equal := List.inj_on_of_nodup_map unique inStart present (sourceAddress.trans address.symm)
  exact congrArg MemoryToken.word equal |>.trans word

/-- A dependent public ADDI derives its canonical output token. The source
    provider is supplied by the recursive public-dataflow proof, not a read axiom. -/
theorem path_addi_token [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {source register : BitVec 5} {value : BitVec 32} {immediate : BitVec 12}
    {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathInstructionPreparation data program cut
      (.ITYPE (immediate, .Regidx source, .Regidx register, .ADDI)))
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register source).addressCode ∧ token.word = Word.ofBitVec value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧
      token.word = Word.ofBitVec (registerImmediateValue value immediate) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have notCaller : Delegation.Caller.decoderFields
      (.ITYPE (immediate, .Regidx source, .Regidx register, .ADDI)) = none := rfl
  have empty := path_instruction_workers_empty hp inverse accepted publicProgram ordinaryProgram image
    scope notCaller aligned
  obtain ⟨w, member, last, ordinary, present, timestamp, bound⟩ := preparation_output_token hp inverse
    accepted publicProgram image empty scope.afterInitial scope.beforeTerminal aligned matching
  have sourceWord := path_addi_source_word hp inverse accepted publicProgram ordinaryProgram
    image scope uniqueSeeds sourceFloor seedToken nonzero member ordinary last
  have requests := request_binding size inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size inverse accepted publicProgram image requests
  have zero := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero image)
    (mixed_zero_rules_of_program size inverse accepted publicProgram ordinaryProgram requests)
  have output := path_addi_row_output (by omega) accepted ordinaryProgram scope nonzero zero
    member ordinary last (sourceWord.symm ▸ Word.ofBitVec_bound _)
  rw [sourceWord, Word.ofBitVec_roundtrip] at output
  refine ⟨_, present, output.2.1, timestamp, ?_⟩
  apply Word.eq_of_value bound (Word.ofBitVec_bound _)
  have equal := congrArg BitVec.toNat output.2.2
  rw [Word.toBitVec_toNat bound] at equal
  exact equal.trans (Word.ofBitVec_value _).symm

/-- Every public dataflow tree starts after a real preparation cycle. -/
theorem path_register_dataflow_after_initial [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (flow : PathRegisterDataflow data program cut register value) :
    (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut := by
  cases flow with
  | literal scope => exact scope.afterInitial
  | auipc scope _ => exact scope.afterInitial
  | addi _ scope _ => exact scope.afterInitial
  | frame _ scope _ => exact scope.afterInitial

/-- Public syntax computes every tracked value along the actual accepted path,
    including read-refreshing branch/jump/load/store gaps. Matching supplies the
    real source tokens; no operand read, successful Sail run or valid control is
    an input. Other register and RAM writes retain their actual effects. -/
theorem path_register_dataflow_token [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (flow : PathRegisterDataflow data program cut register value) :
    ∀ {tokens : List (MemoryToken p)}, register ≠ 0 → cut % 4 = 0 →
      (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
        (tokens ++ (data.prefixSteps cut).map Prod.fst) →
      ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  induction flow with
  | literal scope =>
    intro tokens nonzero aligned matching
    obtain ⟨row, member, last, entry, included, pc, encoding,
      token, present, address, timestamp, word⟩ := path_preparation_token hp inverse
        accepted publicProgram ordinaryProgram image scope nonzero aligned matching
    exact ⟨token, present, address, word⟩
  | auipc scope placement =>
    intro tokens nonzero aligned matching
    obtain ⟨row, member, last, entry, included, pc, encoding,
      token, present, address, timestamp, word⟩ := path_preparation_token hp inverse
        accepted publicProgram ordinaryProgram image scope nonzero aligned matching
    have placed := placement row member last entry included pc encoding
    refine ⟨token, present, address, ?_⟩
    simpa only [PathWrite.value, placed] using word
  | addi prior scope sourceNonzero ih =>
    intro tokens nonzero aligned matching
    have floor := path_register_dataflow_after_initial prior
    obtain ⟨token, present, address, _, word⟩ := path_addi_token hp inverse accepted publicProgram
      ordinaryProgram image scope uniqueSeeds floor
      (fun _ prefixMatching => ih sourceNonzero (by omega) prefixMatching) nonzero aligned matching
    exact ⟨token, present, address, word⟩
  | frame prior scope form ih =>
    intro tokens nonzero aligned matching
    have floor := path_register_dataflow_after_initial prior
    exact frame_value_token hp inverse accepted publicProgram image uniqueSeeds floor
      (fun _ prefixMatching => ih nonzero (by omega) prefixMatching) aligned
      (path_frame_refreshes hp inverse accepted publicProgram ordinaryProgram image scope form nonzero aligned) matching

/-- The separate memory boundary realizes the syntactically computed value in
    the actual architectural state; this adapter still needs no round mask. -/
theorem path_register_dataflow_at_boundary [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before atCut : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup)
    (flow : PathRegisterDataflow data program cut register value) (nonzero : register ≠ 0)
    (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) (boundary : NativeBoundary tokens atCut cells) :
    (Cell.register register).read atCut = .ok value atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses image]
    exact distinct
  obtain ⟨token, present, address, word⟩ := path_register_dataflow_token hp inverse accepted
    publicProgram ordinaryProgram image unique flow nonzero aligned matching
  obtain ⟨cell, _, code, read⟩ := native_boundary_read boundary present
  have same : cell = Cell.register register := cell_address_injective (code.trans address)
  subst cell
  have bits : token.word.toBitVec = value := by rw [word, Word.ofBitVec_roundtrip]
  exact ⟨bits ▸ read, token, present, address, word⟩

end Airbender.UnifiedReduced.Caller.Proofs
