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
  obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded _ member ordinary)
  have schedule := wrapped_program_pc_clock hp clockInverse setup accepted publicProgram ordinaryProgram scope.registry _ member
  have pc := native_query_pc_word (by dsimp [limbBase]; omega) query
  have bits : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily).start.word.toBitVec = entry.pc := by
    change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at pc
    change (Word.mk (w 0).val (w 1).val).toBitVec = entry.pc
    rw [pc, Word.ofBitVec_roundtrip]
  have clock : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) = cut - 4 := by omega
  have address : entry.pc = wrappedProgramAddress data (cut - 4) := by simpa only [bits, clock, wrappedProgramAddress] using schedule
  have metadata := (run_program_sources ordinaryProgram entry present).fields
  obtain ⟨destination, bound, bank⟩ := public_register_write_fields (scope.atCut entry present address) nonzero metadata
  exact ⟨entry, present, query, destination, bound, bank⟩

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

/-- Decoded public GPR writes to another GPR only refresh any access to the tracked cell.
    The actual row and every selected edge follow from native clocks and public
    decoding. Neither an empty transfer window nor an inert gap is assumed. -/
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
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨row, member, last, ordinary⟩ := preparation_cycle_row size clockInverse accepted.toRequestChecks publicProgram
    scope.prefixScope scope.afterInitial scope.beforeTerminal aligned
  cases row with
  | mk family w =>
    cases family
    have output := public_frame_row_destination (by omega) clockInverse setup accepted publicProgram ordinaryProgram
      scope destinationNonzero member ordinary last
    intro edge selected same
    simp only [RequestTrace.windowSteps, scope.prefixScope, List.flatMap_nil, List.append_nil] at selected
    obtain ⟨other, otherMember, edgeMember⟩ := List.mem_flatMap.mp selected
    have present := List.mem_of_mem_filter otherMember
    have interval := of_decide_eq_true (List.mem_filter.mp otherMember).2
    have clocks := machine_clock_facts size clockInverse accepted.toRequestChecks publicProgram present
    have equalClock : Delegation.Caller.startClock other =
        Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by omega
    have equal := List.inj_on_of_nodup_map (machine_clocks_unique size clockInverse accepted.toRequestChecks publicProgram)
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
    · have equal : Cell.register destination = Cell.register register := cell_address_injective (output.symm.trans same)
      exact False.elim (preserves (Cell.register.inj equal))

/-- Raw initialized matching transports the tracked value through an actual
    unrelated public GPR write. Readonly accesses may replace its timestamp, while the other
    destination's real write remains in the window. No round mask is needed. -/
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
  have refreshes := public_frame_refreshes hp clockInverse setup accepted publicProgram ordinaryProgram scope destinationNonzero preserves aligned
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
