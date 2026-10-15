import Airbender.Review.Trace.UnifiedReduced.RegisterDataflow
import Airbender.Proofs.UnifiedReduced.RegisterChains

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- The public instruction constructor determines the destination bank/index.
    No arithmetic operand, range or result is needed for this footprint. -/
theorem arithmetic_register_write_fields {instruction : SailRV32.instruction} {destination : BitVec 5}
    (form : ArithmeticRegisterWrite instruction destination) (nonzero : destination ≠ 0) :
    ∃ fields, Mixed.decoderFields instruction = some fields ∧ fields.rd = destination ∧
      fields.mask < 524288 ∧ fields.mask.testBit 18 = false := by
  change destination ≠ 0#5 at nonzero
  cases form <;>
    simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      UnifiedReduced.arithmeticFields, Trace.arithmeticFields, DecoderData.mapFamily, nonzero,
      Nat.testBit, Nat.shiftRight_eq_div_pow]

/-- Successful public decoding supplies supported shift payloads; no legality
    flag, native selector, operand range or arithmetic result is assumed. -/
theorem binary_register_write_fields {instruction : SailRV32.instruction} {destination : BitVec 5}
    {fields : DecoderData UnifiedFamily} (form : BinaryRegisterWrite instruction destination)
    (nonzero : destination ≠ 0) (decoded : Mixed.decoderFields instruction = some fields) :
    fields.rd = destination ∧ fields.mask < 524288 ∧ fields.mask.testBit 18 = false := by
  change destination ≠ 0#5 at nonzero
  cases form <;>
    simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, ShiftBinop.instructionFields,
      binaryFields, customDecoderFields, DecoderData.mapFamily, ShiftBinop.Operation.isShift,
      ShiftBinop.Operation.tag, nonzero] at decoded
  all_goals first
    | (subst fields; simp [Nat.testBit, Nat.shiftRight_eq_div_pow])
    | (rcases decoded with ⟨_, rfl⟩; simp [Nat.testBit, Nat.shiftRight_eq_div_pow])

/-- Original comparison metadata binds the destination independently of its
    predicate, sign bits, operand ranges and PC-cleanup result. -/
theorem comparison_register_write_fields {instruction : SailRV32.instruction} {destination : BitVec 5}
    {fields : DecoderData UnifiedFamily} (form : ComparisonRegisterWrite instruction destination)
    (nonzero : destination ≠ 0) (decoded : Mixed.decoderFields instruction = some fields) :
    fields.rd = destination ∧ fields.mask < 524288 ∧ fields.mask.testBit 18 = false := by
  change destination ≠ 0#5 at nonzero
  cases form <;>
    simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily, nonzero] at decoded
  all_goals subst fields
  all_goals simp [Nat.testBit, Nat.shiftRight_eq_div_pow]

/-- The admitted custom projections derive the same native GPR destination.
    Pinned custom execution clauses and their semantic boundaries stay separate. -/
theorem custom_register_write_fields {instruction : SailRV32.instruction} {destination : BitVec 5}
    {fields : DecoderData UnifiedFamily} (form : CustomRegisterWrite instruction destination)
    (nonzero : destination ≠ 0) (decoded : Mixed.decoderFields instruction = some fields) :
    fields.rd = destination ∧ fields.mask < 524288 ∧ fields.mask.testBit 18 = false := by
  change destination ≠ 0#5 at nonzero
  cases form <;>
    simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, customDecoderFields,
      customRotationTag, nonzero] at decoded
  all_goals subst fields
  all_goals simp [Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem public_register_write_fields {instruction : SailRV32.instruction} {destination : BitVec 5}
    {fields : DecoderData UnifiedFamily} (form : PublicRegisterWrite instruction destination)
    (nonzero : destination ≠ 0) (decoded : Mixed.decoderFields instruction = some fields) :
    fields.rd = destination ∧ fields.mask < 524288 ∧ fields.mask.testBit 18 = false := by
  cases form with
  | arithmetic form =>
    obtain ⟨actual, metadata, destination, bound, bank⟩ := arithmetic_register_write_fields form nonzero
    rw [decoded] at metadata
    have same := Option.some.inj metadata
    subst actual
    exact ⟨destination, bound, bank⟩
  | binary form => exact binary_register_write_fields form nonzero decoded
  | comparison form => exact comparison_register_write_fields form nonzero decoded
  | custom form => exact custom_register_write_fields form nonzero decoded

theorem ordinary_frame_entry [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (registry : WrappedSequentialProgram program)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    ∃ entry ∈ program, decoderQuery w = entry.query ∧ entry.pc = wrappedProgramAddress data (cut - 4) := by
  obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded _ member ordinary)
  have schedule := wrapped_program_pc_clock hp clockInverse setup accepted publicProgram ordinaryProgram registry _ member
  have pc := native_query_pc_word (by dsimp [limbBase]; omega) query
  have bits : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily).start.word.toBitVec = entry.pc := by
    change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at pc
    change (Word.mk (w 0).val (w 1).val).toBitVec = entry.pc
    rw [pc, Word.ofBitVec_roundtrip]
  have clock : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) = cut - 4 := by omega
  have address : entry.pc = wrappedProgramAddress data (cut - 4) := by simpa only [bits, clock, wrappedProgramAddress] using schedule
  exact ⟨entry, present, query, address⟩

theorem public_frame_preparation_entry [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {destination : BitVec 5}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : RegisterFramePreparation data program cut destination) (nonzero : destination ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    ∃ entry ∈ program, decoderQuery w = entry.query ∧ entry.data.rd = destination ∧
      entry.data.mask < 524288 ∧ entry.data.mask.testBit 18 = false := by
  obtain ⟨entry, present, query, address⟩ := ordinary_frame_entry hp clockInverse setup accepted publicProgram ordinaryProgram
    scope.registry member ordinary last
  have metadata := (run_program_sources ordinaryProgram entry present).fields
  obtain ⟨destination, bound, bank⟩ := public_register_write_fields (scope.atCut entry present address) nonzero metadata
  exact ⟨entry, present, query, destination, bound, bank⟩

theorem decoded_frame_row_destination [Fact p.Prime] (hp : 4194304 ≤ p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {entry : UnifiedReduced.ProgramEntry}
    {destination : BitVec 5}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (query : decoderQuery w = entry.query) (destinationIndex : entry.data.rd = destination)
    (bound : entry.data.mask < 524288) (bank : entry.data.mask.testBit 18 = false) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register destination).addressCode := by
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core bound query
  have destinationRAM : w 29 = 0 := by simpa [importedConstraintsDecoderColumns, bank] using flags 18
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have index : (w 7).val = destination.toNat := by simpa [destinationIndex, importedConstraintsDecoderColumns] using indices.2.2
  have lower := Verification.assertion_of_holds core ⟨31, by rw [UnifiedReduced.constraint_count]; decide⟩
  have upper := Verification.assertion_of_holds core ⟨32, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, destinationRAM] at lower upper
  have location : w 44 = w 7 := by linear_combination lower
  have high : w 45 = 0 := by linear_combination upper
  simp [writeToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
    destinationRAM, location, high, index]

theorem public_frame_row_destination [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {destination : BitVec 5}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : RegisterFramePreparation data program cut destination) (nonzero : destination ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register destination).addressCode := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, _, query, destinationIndex, bound, bank⟩ := public_frame_preparation_entry hp clockInverse setup accepted
    publicProgram ordinaryProgram scope nonzero member ordinary last
  exact decoded_frame_row_destination hp core query destinationIndex bound bank

theorem public_register_dataflow_after_initial [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (preparation : PublicRegisterDataflow data program cut register value) :
    (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut := by
  cases preparation with
  | prepared source => exact public_register_preparation_after_initial source
  | addi _ scope _ => exact scope.afterInitial
  | frame _ scope _ _ => exact scope.afterInitial
  | arithmeticFrame _ scope _ _ => exact scope.afterInitial
  | registerFrame _ scope _ _ => exact scope.afterInitial
  | loadFrame _ scope _ => exact scope.afterInitial
  | storeFrame _ scope => exact scope.afterInitial
  | callerFrame _ scope _ _ => exact scope.afterInitial

/-- Decoded public GPR writes to another GPR only refresh any access to the tracked cell.
    The actual row and every selected edge follow from native clocks and public
    decoding. Neither an empty transfer window nor an inert gap is assumed. -/
theorem ordinary_frame_refreshes [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State}
    {ca : List (BitVec 32)} {cut : Nat} {register : BitVec 5}
    (accepted : RequestChecks data) (publicProgram : RequestInputs data before ca)
    (prefixScope : data.workers.windowRows (cut - 4) cut = [])
    (afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut)
    (beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value)
    (aligned : cut % 4 = 0)
    (disjoint : ∀ w : Nat → ZMod p, (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows →
      (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers →
      Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut →
      (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address ≠ (Cell.register register).addressCode) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, edge.1.address = (Cell.register register).addressCode →
      edge.2.value = edge.1.value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨row, member, last, ordinary⟩ := preparation_cycle_row size clockInverse accepted publicProgram
    prefixScope afterInitial beforeTerminal aligned
  cases row with
  | mk family w =>
    cases family
    have output := disjoint w member ordinary last
    intro edge selected same
    simp only [RequestTrace.windowSteps, prefixScope, List.flatMap_nil, List.append_nil] at selected
    obtain ⟨other, otherMember, edgeMember⟩ := List.mem_flatMap.mp selected
    have present := List.mem_of_mem_filter otherMember
    have interval := of_decide_eq_true (List.mem_filter.mp otherMember).2
    have clocks := machine_clock_facts size clockInverse accepted publicProgram present
    have equalClock : Delegation.Caller.startClock other =
        Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by omega
    have equal := List.inj_on_of_nodup_map (machine_clocks_unique size clockInverse accepted publicProgram)
      present member equalClock
    subst other
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp edgeMember
    have ports : port ∈ importedConstraintsMemoryPorts := by
      rw [machine_ports_ordinary member ordinary] at included
      simpa [Trace.Row.ports, CircuitLayout.ports] using included
    simp [importedConstraintsMemoryPorts] at ports
    rcases ports with rfl | rfl | rfl
    · rfl
    · rfl
    · exact False.elim (output same)

theorem public_frame_refreshes [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register destination : BitVec 5}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : RegisterFramePreparation data program cut destination)
    (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register) (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, edge.1.address = (Cell.register register).addressCode →
      edge.2.value = edge.1.value := by
  apply ordinary_frame_refreshes hp clockInverse accepted.toRequestChecks publicProgram scope.prefixScope scope.afterInitial
    scope.beforeTerminal aligned
  intro w member ordinary last same
  have output := public_frame_row_destination (by omega) clockInverse setup accepted publicProgram ordinaryProgram
    scope destinationNonzero member ordinary last
  have equal : Cell.register destination = Cell.register register := cell_address_injective (output.symm.trans same)
  exact preserves (Cell.register.inj equal)

/-- Raw initialized matching transports the tracked value through an actual
    unrelated public GPR write. Readonly accesses may replace its timestamp, while the other
    destination's real write remains in the window. No round mask is needed. -/
theorem frame_value_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca : List (BitVec 32)} {cells : List Cell} {cut : Nat} {value : BitVec 32}
    {register : BitVec 5} {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value)
    (aligned : cut % 4 = 0)
    (refreshes : ∀ edge ∈ data.windowSteps (cut - 4) cut,
      edge.1.address = (Cell.register register).addressCode → edge.2.value = edge.1.value)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have first : (cut - 4) % 4 = 0 := by omega
  have requests := request_binding size clockInverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size clockInverse accepted publicProgram initialization requests
  obtain ⟨start, earlier, later⟩ := Transfer.split_at facts ((cut - 4) - 1)
  have prefixMatching := earlier.matching
  rw [mixed_prefix_steps data (by omega)] at prefixMatching
  obtain ⟨sourceToken, sourceMember, sourceAddress, sourceWord⟩ := seedToken start prefixMatching
  obtain ⟨finish, window, _⟩ := Transfer.split_at later (cut - 1)
  change Transfer.Facts ⟨start, finish, Transfer.windowSteps (mixedData data) ((cut - 4) - 1) (cut - 1)⟩ at window
  rw [← mixed_window_steps size clockInverse accepted.toRequestChecks publicProgram first aligned (by omega) (by omega)] at window
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp uniqueSeeds
  have seed : ∀ token ∈ start, token.address = (Cell.register register).addressCode → token.value = sourceToken.value := by
    intro token present address
    have equal := List.inj_on_of_nodup_map unique present sourceMember (address.trans sourceAddress.symm)
    exact congrArg MemoryToken.value equal
  have values := Transfer.produced_cell_values window (Cell.register register).addressCode sourceToken.value seed
    (by intro edge member address read; exact (refreshes edge member address).trans read)
  have boundaryKeys := boundary_keys MemoryToken.address window.matching window.addresses
  obtain ⟨token, present, address⟩ := List.mem_map.mp (boundaryKeys.mem_iff.mp (List.mem_map.mpr ⟨sourceToken, sourceMember, rfl⟩))
  have atTarget : token.address = (Cell.register register).addressCode := address.trans sourceAddress
  have raw := values token (window.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl present))) atTarget
  have word : token.word = Word.ofBitVec value := by simpa only [MemoryToken.word, raw] using sourceWord
  have complete := matching_at_next_cut size clockInverse accepted.toRequestChecks publicProgram first aligned
    (by omega) (by omega) prefixMatching window.matching
  have permutation : finish.Perm tokens := by
    apply List.perm_iff_count.mpr
    intro cell
    have left := complete.count_eq cell
    have right := matching.count_eq cell
    simp only [List.count_append] at left right
    omega
  exact ⟨token, permutation.mem_iff.mp present, atTarget, word⟩

theorem public_frame_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {value : BitVec 32}
    {register destination : BitVec 5} {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (scope : RegisterFramePreparation data program cut destination)
    (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value)
    (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  exact frame_value_token hp clockInverse accepted publicProgram initialization uniqueSeeds sourceFloor seedToken aligned
    (public_frame_refreshes hp clockInverse setup accepted publicProgram ordinaryProgram scope destinationNonzero preserves aligned) matching

theorem arithmetic_frame_preparation_entry [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {destination : BitVec 5}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : ArithmeticFramePreparation data program cut destination) (nonzero : destination ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    ∃ entry ∈ program, decoderQuery w = entry.query ∧ entry.data.rd = destination ∧
      entry.data.mask < 524288 ∧ entry.data.mask.testBit 18 = false := by
  exact public_frame_preparation_entry hp clockInverse setup accepted publicProgram ordinaryProgram scope.registerFrame nonzero member ordinary last

theorem arithmetic_frame_row_destination [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {destination : BitVec 5}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : ArithmeticFramePreparation data program cut destination) (nonzero : destination ≠ 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register destination).addressCode := by
  exact public_frame_row_destination hp clockInverse setup accepted publicProgram ordinaryProgram scope.registerFrame nonzero member ordinary last

theorem arithmetic_frame_refreshes [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register destination : BitVec 5}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : ArithmeticFramePreparation data program cut destination)
    (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register) (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, edge.1.address = (Cell.register register).addressCode →
      edge.2.value = edge.1.value := by
  exact public_frame_refreshes hp clockInverse setup accepted publicProgram ordinaryProgram scope.registerFrame destinationNonzero preserves aligned

theorem arithmetic_frame_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {value : BitVec 32}
    {register destination : BitVec 5} {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (scope : ArithmeticFramePreparation data program cut destination)
    (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value)
    (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  exact public_frame_token hp clockInverse setup accepted publicProgram ordinaryProgram initialization uniqueSeeds scope.registerFrame
    destinationNonzero preserves sourceFloor seedToken aligned matching

theorem register_frame_refreshes [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register source destination : BitVec 5} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : RegisterImmediatePreparation data program cut source destination immediate)
    (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register) (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, edge.1.address = (Cell.register register).addressCode →
      edge.2.value = edge.1.value := by
  exact arithmetic_frame_refreshes hp clockInverse setup accepted publicProgram ordinaryProgram scope.arithmeticFrame
    destinationNonzero preserves aligned

theorem register_frame_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {value : BitVec 32}
    {register source destination : BitVec 5} {immediate : BitVec 12} {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (scope : RegisterImmediatePreparation data program cut source destination immediate)
    (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value)
    (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  exact arithmetic_frame_token hp clockInverse setup accepted publicProgram ordinaryProgram initialization uniqueSeeds
    scope.arithmeticFrame destinationNonzero preserves sourceFloor seedToken aligned matching

/-- LW-to-x0 remains its native NOP projection. Both branches have a GPR
    destination, without a successful Sail load or a nonzero-destination premise. -/
theorem word_load_frame_fields {source destination : BitVec 5} {immediate : BitVec 12}
    {fields : DecoderData UnifiedFamily}
    (decoded : Mixed.decoderFields (.LOAD (immediate, .Regidx source, .Regidx destination, false, 4)) = some fields) :
    fields.rd = destination ∧ fields.mask < 524288 ∧ fields.mask.testBit 18 = false := by
  by_cases zero : destination = 0#5
  all_goals simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
    Trace.arithmeticFields, UnifiedReduced.arithmeticFields, DecoderData.mapFamily, zero] at decoded
  all_goals subst fields
  all_goals simp [zero, Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem word_store_frame_fields {source stored : BitVec 5} {immediate : BitVec 12}
    {fields : DecoderData UnifiedFamily}
    (decoded : Mixed.decoderFields (.STORE (immediate, .Regidx stored, .Regidx source, 4)) = some fields) :
    fields.mask = 262144 := by
  simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
    UnifiedReduced.arithmeticFields, DecoderData.mapFamily] at decoded
  subst fields
  rfl

theorem load_frame_row_destination [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {source destination : BitVec 5} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : LoadFramePreparation data program cut source destination immediate)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register destination).addressCode := by
  obtain ⟨entry, present, query, address⟩ := ordinary_frame_entry hp clockInverse setup accepted publicProgram ordinaryProgram
    scope.registry member ordinary last
  have metadata := (run_program_sources ordinaryProgram entry present).fields
  rw [scope.atCut entry present address] at metadata
  obtain ⟨index, bound, bank⟩ := word_load_frame_fields metadata
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  exact decoded_frame_row_destination hp core query index bound bank

theorem store_frame_row_disjoint [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register source stored : BitVec 5} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : StoreFramePreparation data program cut source stored immediate)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address ≠ (Cell.register register).addressCode := by
  obtain ⟨entry, present, query, address⟩ := ordinary_frame_entry hp clockInverse setup accepted publicProgram ordinaryProgram
    scope.registry member ordinary last
  have metadata := (run_program_sources ordinaryProgram entry present).fields
  rw [scope.atCut entry present address] at metadata
  have mask := word_store_frame_fields metadata
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core (by rw [mask]; decide) query
  have destinationRAM : w 29 = 1 := by simpa [importedConstraintsDecoderColumns, mask, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 18
  have one : (1 : ZMod p).val = 1 := by rw [ZMod.val_one]
  intro same
  change Nat.pair (w 29).val (Nat.pair (w 44).val (w 45).val) = Nat.pair 0 (Nat.pair register.toNat 0) at same
  have banks := (Nat.pair_eq_pair.mp same).1
  rw [destinationRAM, one] at banks
  omega

theorem load_frame_refreshes [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register source destination : BitVec 5} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : LoadFramePreparation data program cut source destination immediate)
    (preserves : destination ≠ register) (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, edge.1.address = (Cell.register register).addressCode →
      edge.2.value = edge.1.value := by
  apply ordinary_frame_refreshes hp clockInverse accepted.toRequestChecks publicProgram scope.prefixScope scope.afterInitial
    scope.beforeTerminal aligned
  intro w member ordinary last same
  have output := load_frame_row_destination (by omega) clockInverse setup accepted publicProgram ordinaryProgram scope member ordinary last
  have equal : Cell.register destination = Cell.register register := cell_address_injective (output.symm.trans same)
  exact preserves (Cell.register.inj equal)

theorem load_frame_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {value : BitVec 32}
    {register source destination : BitVec 5} {immediate : BitVec 12} {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (scope : LoadFramePreparation data program cut source destination immediate)
    (preserves : destination ≠ register)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value)
    (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  exact frame_value_token hp clockInverse accepted publicProgram initialization uniqueSeeds sourceFloor seedToken aligned
    (load_frame_refreshes hp clockInverse setup accepted publicProgram ordinaryProgram scope preserves aligned) matching

theorem store_frame_refreshes [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register source stored : BitVec 5} {immediate : BitVec 12}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : StoreFramePreparation data program cut source stored immediate)
    (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, edge.1.address = (Cell.register register).addressCode →
      edge.2.value = edge.1.value := by
  apply ordinary_frame_refreshes hp clockInverse accepted.toRequestChecks publicProgram scope.prefixScope scope.afterInitial
    scope.beforeTerminal aligned
  intro w member ordinary last
  exact store_frame_row_disjoint (by omega) clockInverse setup accepted publicProgram ordinaryProgram scope member ordinary last

theorem store_frame_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {value : BitVec 32}
    {register source stored : BitVec 5} {immediate : BitVec 12} {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (scope : StoreFramePreparation data program cut source stored immediate)
    (sourceFloor : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut - 4)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value)
    (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  exact frame_value_token hp clockInverse accepted publicProgram initialization uniqueSeeds sourceFloor seedToken aligned
    (store_frame_refreshes hp clockInverse setup accepted publicProgram ordinaryProgram scope aligned) matching

private def registerFramePort (port : MemoryPort) : Bool :=
  port.writeValue.isNone || match port.address with
    | .constantRegister index => index == 10 || index == 12
    | .indirect _ => true
    | _ => false

theorem worker_register_refreshes (row : Delegation.Row p) {port : MemoryPort}
    (member : port ∈ row.ports) {register : BitVec 5}
    (notPointer : register ≠ 10) (notControl : register ≠ 12)
    (same : (readToken row.assignment port).address = (Cell.register register).addressCode) :
    (row.writeToken port).value = (readToken row.assignment port).value := by
  have checked : row.ports.toList.all registerFramePort = true := by
    cases row with
    | mk family w => cases family <;> dsimp only [Delegation.Row.ports] <;> decide +kernel
  have valid := List.all_eq_true.mp checked port (by simpa using member)
  by_cases readonly : port.writeValue = none
  · simp only [Delegation.Row.writeToken, readToken, MemoryPort.writeCode, readonly,
      Option.getD_none, MemoryPort.readCode]
  have written : port.writeValue.isNone = false := by cases h : port.writeValue <;> simp_all
  simp only [registerFramePort, written, Bool.false_or] at valid
  cases address : port.address with
  | constantRegister index =>
    have indexSame : index = register.toNat := by
      simpa only [readToken, address, MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair,
        true_and, and_true] using same
    have options : index = 10 ∨ index = 12 := by simpa [address] using valid
    rcases options with eq | eq
    · have equal : register.toNat = 10 := indexSame.symm.trans eq
      exact False.elim (notPointer (BitVec.eq_of_toNat_eq equal))
    · have equal : register.toNat = 12 := indexSame.symm.trans eq
      exact False.elim (notControl (BitVec.eq_of_toNat_eq equal))
  | register _ => simp [address] at valid
  | mixed _ _ _ => simp [address] at valid
  | indirect _ => simp [readToken, address, MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair] at same

theorem caller_frame_refreshes [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : CallerFramePreparation data program cut)
    (nonzero : register ≠ 0) (notPointer : register ≠ 10) (notControl : register ≠ 12)
    (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, edge.1.address = (Cell.register register).addressCode →
      edge.2.value = edge.1.value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks publicProgram
  intro edge selected same
  rcases List.mem_append.mp selected with machine | worker
  · obtain ⟨row, selected, edgeMember⟩ := List.mem_flatMap.mp machine
    obtain ⟨member, range⟩ := List.mem_filter.mp selected
    have range := of_decide_eq_true range
    have clocks := machine_clock_facts size clockInverse accepted.toRequestChecks publicProgram member
    have last : Delegation.Caller.startClock row + 4 = cut := by omega
    have caller : row ∈ data.callers := by
      by_contra ordinary
      cases row with
      | mk family w =>
        cases family
        obtain ⟨entry, present, _, address⟩ := ordinary_frame_entry (by omega) clockInverse setup accepted
          publicProgram ordinaryProgram scope.registry member ordinary last
        exact scope.ordinary entry present address
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp edgeMember
    rw [machine_ports_caller caller] at included
    have ports : port = importedConstraintsMemoryPorts[0] ∨ port = importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using included
    have binding := (requests.callers row caller).registers
    have notZero : (Cell.register 0).addressCode ≠ (Cell.register register).addressCode := by
      intro equal
      exact nonzero (Cell.register.inj (cell_address_injective equal).symm)
    rcases ports with rfl | rfl
    · exact False.elim (notZero (binding.1.symm.trans same))
    · have address : (readToken row.assignment importedConstraintsMemoryPorts[2]).address =
          (Cell.register 0).addressCode := binding.2.1
      exact False.elim (notZero (address.symm.trans same))
  · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
    exact worker_register_refreshes row (by simpa using included) notPointer notControl same

theorem public_register_dataflow_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (preparation : PublicRegisterDataflow data program cut register value) :
    ∀ {tokens : List (MemoryToken p)}, register ≠ 0 → cut % 4 = 0 →
      (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
        (tokens ++ (data.prefixSteps cut).map Prod.fst) →
      ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  induction preparation with
  | prepared source =>
    intro tokens nonzero aligned matching
    obtain ⟨token, present, address, _, word⟩ := public_register_preparation_token hp clockInverse setup accepted
      publicProgram ordinaryProgram initialization uniqueSeeds source nonzero aligned matching
    exact ⟨token, present, address, word⟩
  | addi prior scope sourceNonzero ih =>
    intro tokens nonzero aligned matching
    have floor := public_register_dataflow_after_initial prior
    obtain ⟨token, present, address, _, word⟩ := register_immediate_preparation_token_of_value hp clockInverse setup accepted
      publicProgram ordinaryProgram initialization scope uniqueSeeds floor
      (fun _ prefixMatching => ih sourceNonzero (by omega) prefixMatching) nonzero aligned matching
    exact ⟨token, present, address, word⟩
  | frame prior scope destinationNonzero preserves ih =>
    intro tokens nonzero aligned matching
    have floor := public_register_dataflow_after_initial prior
    exact register_frame_token hp clockInverse setup accepted publicProgram ordinaryProgram initialization uniqueSeeds scope
      destinationNonzero preserves floor (fun _ prefixMatching => ih nonzero (by omega) prefixMatching) aligned matching
  | arithmeticFrame prior scope destinationNonzero preserves ih =>
    intro tokens nonzero aligned matching
    have floor := public_register_dataflow_after_initial prior
    exact arithmetic_frame_token hp clockInverse setup accepted publicProgram ordinaryProgram initialization uniqueSeeds scope
      destinationNonzero preserves floor (fun _ prefixMatching => ih nonzero (by omega) prefixMatching) aligned matching
  | registerFrame prior scope destinationNonzero preserves ih =>
    intro tokens nonzero aligned matching
    have floor := public_register_dataflow_after_initial prior
    exact public_frame_token hp clockInverse setup accepted publicProgram ordinaryProgram initialization uniqueSeeds scope
      destinationNonzero preserves floor (fun _ prefixMatching => ih nonzero (by omega) prefixMatching) aligned matching
  | loadFrame prior scope preserves ih =>
    intro tokens nonzero aligned matching
    have floor := public_register_dataflow_after_initial prior
    exact load_frame_token hp clockInverse setup accepted publicProgram ordinaryProgram initialization uniqueSeeds scope
      preserves floor (fun _ prefixMatching => ih nonzero (by omega) prefixMatching) aligned matching
  | storeFrame prior scope ih =>
    intro tokens nonzero aligned matching
    have floor := public_register_dataflow_after_initial prior
    exact store_frame_token hp clockInverse setup accepted publicProgram ordinaryProgram initialization uniqueSeeds scope
      floor (fun _ prefixMatching => ih nonzero (by omega) prefixMatching) aligned matching
  | callerFrame prior scope notPointer notControl ih =>
    intro tokens nonzero aligned matching
    have floor := public_register_dataflow_after_initial prior
    exact frame_value_token hp clockInverse accepted publicProgram initialization uniqueSeeds floor
      (fun _ prefixMatching => ih nonzero (by omega) prefixMatching) aligned
      (caller_frame_refreshes hp clockInverse setup accepted publicProgram ordinaryProgram scope nonzero notPointer notControl aligned)
      matching

theorem public_register_dataflow_control_preparation [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (preparation : PublicRegisterDataflow data program cut register value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    RegisterDataflowBoundaryExecution data before cells cut register value := by
  have floor := public_register_dataflow_after_initial preparation
  obtain ⟨tokens, _, events, _, atCut, _, permutation, _, history, _, matching, _, boundary, _⟩ :=
    (mixed_window_execution (lower := cut) (upper := cut) hp clockInverse rotationInverse accepted inputs aligned aligned (by omega) (by omega)).execution
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses inputs.initialization]
    exact inputs.distinct
  obtain ⟨token, present, address, word⟩ := public_register_dataflow_token hp clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.initialization unique preparation nonzero aligned matching
  obtain ⟨cell, _, code, read⟩ := native_boundary_read boundary present
  have same : cell = Cell.register register := cell_address_injective (code.trans address)
  subst cell
  have bits : token.word.toBitVec = value := by rw [word, Word.ofBitVec_roundtrip]
  exact ⟨tokens, events, atCut, permutation, history, matching, boundary, bits ▸ read, token, present, address, word⟩

end Airbender.UnifiedReduced.Caller.Proofs
