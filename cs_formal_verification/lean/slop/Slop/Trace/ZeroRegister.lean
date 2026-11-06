import Slop.Trace.ZeroValues
import Slop.Trace.Program
import Slop.Trace.Values

namespace Airbender.Trace.Proofs
open Arithmetic

private theorem arithmetic_zero_fields (rs1 rs2 rd : BitVec 5) (bits : BitVec 32) (mask : Nat)
    (zero : (arithmeticFields rs1 rs2 rd bits mask).rd = 0) :
    arithmeticFields rs1 rs2 rd bits mask = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by
  unfold arithmeticFields at *
  split at zero <;> simp_all

private theorem arithmetic_family (rs1 rs2 rd : BitVec 5) (bits : BitVec 32) (mask : Nat) :
    (arithmeticFields rs1 rs2 rd bits mask).family = .addSub := by
  unfold arithmeticFields
  split <;> rfl

/-- The retained native decoder projection turns every selected arithmetic
    write to x0 (including a discarded LW) into the same zero-operand ADD row. -/
theorem decoder_zero_nop {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : decoderFields instruction = some data) (family : data.family = .addSub)
    (zero : data.rd = 0) : data = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by
  unfold decoderFields at fields
  split at fields
  case h_6 =>
    rename_i original imm rs1 rd
    change (if (rd : BitVec 5) = 0 then some (arithmeticFields 0 0 0 0 1)
      else some ⟨.wordMemory, rs1, 0, rd,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩) = some data at fields
    by_cases discarded : (rd : BitVec 5) = 0
    · rw [ite_eq_left discarded, Option.some.injEq] at fields
      subst data
      rfl
    · rw [ite_eq_right discarded, Option.some.injEq] at fields
      subst data
      cases family
  all_goals first
    | (simp only [Option.some.injEq] at fields
       subst data
       exact arithmetic_zero_fields _ _ _ _ _ zero)
    | (simp only [Option.some.injEq] at fields
       subst data
       cases family)
    | cases fields

theorem decoder_load_nonzero {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : decoderFields instruction = some data) (family : data.family = .wordMemory)
    (load : data.mask = 0) : data.rd ≠ 0 := by
  unfold decoderFields at fields
  split at fields
  case h_6 =>
    rename_i original imm rs1 rd
    change (if (rd : BitVec 5) = 0 then some (arithmeticFields 0 0 0 0 1)
      else some ⟨.wordMemory, rs1, 0, rd,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩) = some data at fields
    by_cases discarded : (rd : BitVec 5) = 0
    · rw [ite_eq_left discarded, Option.some.injEq] at fields
      subst data
      cases family
    · rw [ite_eq_right discarded, Option.some.injEq] at fields
      subst data
      exact discarded
  all_goals first
    | (simp only [Option.some.injEq] at fields
       subst data
       have impossible : Family.addSub = .wordMemory := by
         simpa only [arithmetic_family] using family
       cases impossible)
    | (simp only [Option.some.injEq] at fields
       subst data
       change 1 = 0 at load
       cases load)
    | cases fields

/-- Proof-only metadata facts needed by the shared native x0/history argument.
    These are proved for each projection, not assumed by the public trace claim. -/
structure DecoderRules (projection : SailRV32.instruction → Option DecoderData) : Prop where
  bounds : ∀ instruction data, projection instruction = some data →
    data.immediate.Bounded ∧ data.mask < 512
  zeroNop : ∀ instruction data, projection instruction = some data →
    data.family = .addSub → data.rd = 0 → data = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩
  loadNonzero : ∀ instruction data, projection instruction = some data →
    data.family = .wordMemory → data.mask = 0 → data.rd ≠ 0

def standardDecoderRules : DecoderRules decoderFields where
  bounds instruction data fields := by
    have bound := decoder_field_bounds fields
    exact ⟨bound.1, by omega⟩
  zeroNop _ _ := decoder_zero_nop
  loadNonzero _ _ := decoder_load_nonzero

theorem addsub_zero_preprocessing {p : Nat}
    {projection : SailRV32.instruction → Option DecoderData} (rules : DecoderRules projection) (hp : limbBase < p) {w : Nat → ZMod p}
    {before : Reference.RiscV.Sail.State} (fetched : (⟨.addSub, w⟩ : Row p).Fetched before projection)
    (zero : AddSub.importedConstraintsMemoryPorts[2].address.code w = (Cell.register 0).addressCode) :
    w 5 = 0 ∧ w 6 = 0 ∧ w 8 = 0 ∧ w 9 = 0 ∧ w 10 = 1 ∧
      ∀ k, 11 ≤ k → k ≤ 16 → w k = 0 := by
  obtain ⟨entry, source, family, query, _, flags⟩ := fetched
  have rd := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
  change w 7 = (entry.data.rd.toNat : ZMod p) at rd
  have columnZero : (w 7).val = 0 := by
    simpa [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, Cell.addressCode] using zero
  have value := congrArg ZMod.val rd
  rw [ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt (by dsimp [limbBase] at hp; omega))] at value
  have nop := rules.zeroNop _ _ source.fields family
    (BitVec.eq_of_toNat_eq (by simpa [columnZero] using value.symm))
  have rs1 := congrArg (fun q : Vector (ZMod p) 9 => q[2]) query
  have rs2 := congrArg (fun q : Vector (ZMod p) 9 => q[3]) query
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
  change w 5 = (entry.data.rs1.toNat : ZMod p) at rs1
  change w 6 = (entry.data.rs2.toNat : ZMod p) at rs2
  change w 8 = (entry.data.immediate.lo : ZMod p) at low
  change w 9 = (entry.data.immediate.hi : ZMod p) at high
  rw [nop] at rs1 rs2 low high flags
  change ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] =
    if (1 : Nat).testBit i.val then 1 else 0 at flags
  refine ⟨by simpa using rs1, by simpa using rs2, by simpa using low, by simpa using high,
    ?_, ?_⟩
  · exact flags ⟨0, by decide⟩
  · intro k lower upper
    interval_cases k
    all_goals first
      | exact flags ⟨1, by decide⟩
      | exact flags ⟨2, by decide⟩
      | exact flags ⟨3, by decide⟩
      | exact flags ⟨4, by decide⟩
      | exact flags ⟨5, by decide⟩
      | exact flags ⟨6, by decide⟩

theorem word_memory_write_nonzero {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option DecoderData} (rules : DecoderRules projection) (hp : limbBase < p)
    {w : Nat → ZMod p} {rom : Table (ZMod p) (fields 9)} {before : Reference.RiscV.Sail.State}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.importedConstraints rom))
    (fetched : (⟨.wordMemory, w⟩ : Row p).Fetched before projection) :
    WordMemory.importedConstraintsMemoryPorts[2].address.code w ≠ (Cell.register 0).addressCode := by
  intro zero
  have address : w 10 = 0 ∧ w 25 = 0 ∧ w 26 = 0 := by
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, Cell.addressCode] using zero
  have rdZero : w 7 = 0 := by
    have register := WordMemory.Proofs.register_address false constraints address.1
    change w 25 = w 7 ∧ w 26 = 0 at register
    rw [← register.1, address.2.1]
  obtain ⟨entry, source, family, query, _, _⟩ := fetched
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) query
  change (∑ i : Fin 1, (2 ^ i.val : Nat) * w #[10][i]) = (entry.data.mask : ZMod p) at packed
  have selected : w 10 = (entry.data.mask : ZMod p) := by simpa using packed
  have mask := congrArg ZMod.val selected
  have small := (rules.bounds _ _ source.fields).2
  rw [ZMod.val_natCast_of_lt (by dsimp [limbBase] at hp; omega), address.1, ZMod.val_zero] at mask
  have nonzero := rules.loadNonzero _ _ source.fields family mask.symm
  have rd := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
  change w 7 = (entry.data.rd.toNat : ZMod p) at rd
  have value := congrArg ZMod.val rd
  rw [ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt (by dsimp [limbBase] at hp; omega)),
    rdZero, ZMod.val_zero] at value
  exact nonzero (BitVec.eq_of_toNat_eq (by simpa using value.symm))

theorem row_zero_write_from_reads [Fact p.Prime]
    {projection : SailRV32.instruction → Option DecoderData} (rules : DecoderRules projection) (hp : 196608 < p)
    {before : Reference.RiscV.Sail.State} (row : Row p)
    (setup : Table (ZMod p) (fields 9))
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup)) (fetched : row.Fetched before projection)
    (port : MemoryPort) (present : port ∈ row.ports)
    (zero : port.address.code row.assignment = (Cell.register 0).addressCode)
    (reads : ∀ source ∈ row.ports,
      (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 →
      source.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment source).value = 0) :
    (writeToken row.columns row.assignment port).value = 0 := by
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      simp [Row.ports, AddSub.importedConstraintsMemoryPorts] at present
      rcases present with rfl | rfl | rfl
      · exact reads _ (by simp [Row.ports, AddSub.importedConstraintsMemoryPorts]) le_rfl zero
      · exact reads _ (by simp [Row.ports, AddSub.importedConstraintsMemoryPorts]) le_rfl zero
      · obtain ⟨rs1, rs2, immediateLo, immediateHi, selected, others⟩ :=
          addsub_zero_preprocessing rules (lt_trans (by decide) hp) fetched zero
        have left := reads AddSub.importedConstraintsMemoryPorts[0]
          (by simp [Row.ports, AddSub.importedConstraintsMemoryPorts])
          (by change (decodeTimestamp w _).value + 0 ≤ (decodeTimestamp w _).value + 2; omega)
          (by simp [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, rs1])
        have right := reads AddSub.importedConstraintsMemoryPorts[1]
          (by simp [Row.ports, AddSub.importedConstraintsMemoryPorts])
          (by change (decodeTimestamp w _).value + 1 ≤ (decodeTimestamp w _).value + 2; omega)
          (by simp [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, rs2])
        have leftLimbs : w 25 = 0 ∧ w 26 = 0 := by
          change Nat.pair (w 25).val (w 26).val = Nat.pair 0 0 at left
          simpa using Nat.pair_eq_pair.mp left
        have rightLimbs : w 29 = 0 ∧ w 30 = 0 := by
          change Nat.pair (w 29).val (w 30).val = Nat.pair 0 0 at right
          simpa using Nat.pair_eq_pair.mp right
        have result := AddSub.Proofs.zero_operands_result hp core selected others
          ⟨leftLimbs.1, leftLimbs.2, rightLimbs.1, rightLimbs.2, immediateLo, immediateHi⟩
        have value := congrArg BitVec.toNat result
        rw [Word.toBitVec_toNat (AddSub.Proofs.written_limb_bounds core)] at value
        have limbs : (w 33).val = 0 ∧ (w 34).val = 0 := by
          change (w 33).val + limbBase * (w 34).val = 0 at value
          dsimp [limbBase] at value
          omega
        simp [writeToken, MemoryPort.writeCode, pairCode, limbs.1, limbs.2]
        rfl
    | wordMemory =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (WordMemory.importedConstraints setup)
          WordMemory.importedConstraintsTimestampLookups)
      simp [Row.ports, WordMemory.importedConstraintsMemoryPorts] at present
      rcases present with rfl | rfl | rfl
      · exact reads _ (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]) le_rfl zero
      · exact reads _ (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]) le_rfl zero
      · exact False.elim (word_memory_write_nonzero rules (lt_trans (by decide) hp) core fetched zero)

private theorem zero_write_from_reads [Fact p.Prime]
    {projection : SailRV32.instruction → Option DecoderData} (rules : DecoderRules projection) (hp : 196608 < p) {trace : Data p}
    (accepted : Accepted trace) {before : Reference.RiscV.Sail.State}
    (row : Row p) (member : row ∈ trace.rows) (fetched : row.Fetched before projection)
    (port : MemoryPort) (present : port ∈ row.ports)
    (zero : port.address.code row.assignment = (Cell.register 0).addressCode)
    (reads : ∀ source ∈ row.ports,
      (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 →
      source.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment source).value = 0) :
    (writeToken row.columns row.assignment port).value = 0 :=
  row_zero_write_from_reads rules hp row trace.rom (accepted.constraints row member)
    fetched port present zero reads

/-- Native matching and strict prior-write clocks propagate Sail's x0 value
    through every selected row; decoder membership supplies the NOP case. -/
theorem native_zero_reads [Fact p.Prime]
    {projection : SailRV32.instruction → Option DecoderData} (rules : DecoderRules projection) (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : Trace.programImageWith projection before addresses = some program) (decoded : Decoded trace program)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured before := by find_configured) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      port.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment port).value = 0 := by
  have field : 196608 < p := by dsimp [timestampBase] at hp; omega
  have fetched := decoder_soundness_with (lt_trans (by decide) field)
    (fun _ _ fields => (rules.bounds _ _ fields).2) accepted programImage decoded
  apply zero_reads_of_preserving hp inverse accepted boundary image
  intro row member port present address reads
  exact zero_write_from_reads rules field accepted row member (fetched row member)
    port present address reads

theorem native_zero_writes [Fact p.Prime]
    {projection : SailRV32.instruction → Option DecoderData} (rules : DecoderRules projection) (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : Trace.programImageWith projection before addresses = some program) (decoded : Decoded trace program)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured before := by find_configured) :
    ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 := by
  have field : 196608 < p := by dsimp [timestampBase] at hp; omega
  have fetched := decoder_soundness_with (lt_trans (by decide) field)
    (fun _ _ fields => (rules.bounds _ _ fields).2) accepted programImage decoded
  have reads := native_zero_reads rules hp inverse accepted boundary image programImage decoded
  intro event member address
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value, edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp member
  subst event
  change edge ∈ trace.rows.flatMap Row.memorySteps at edgeMember
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp rowEdge
  have present : port ∈ row.ports := by simpa using present
  have zero := zero_write_from_reads rules field accepted row rowMember (fetched row rowMember)
    port present address (fun source member _ => reads row rowMember source member)
  change memoryWord (writeToken row.columns row.assignment port).value = 0
  rw [zero]
  rfl

/-- Accepted restricted native accesses now realize Sail state without a
    separate x0/read-value premise. Public image/domain and logical decoder
    membership remain the explicit boundaries. Instruction/PC stepping is later. -/
theorem decoded_sail_history [Fact p.Prime]
    {projection : SailRV32.instruction → Option DecoderData} (rules : DecoderRules projection) (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : Trace.programImageWith projection before addresses = some program) (decoded : Decoded trace program)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured before := by find_configured) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess)
      (seed : TimestampSortedMemoryAccessList) (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ List.append (α := MemoryAccess) events seed.val = history.val ∧
      events.Perm trace.nativeEvents ∧ SailHistory cells events before after ∧
      SailStateMatches cells history after :=
  native_sail_history hp inverse accepted boundary image domain aligned
    (native_zero_writes rules hp inverse accepted boundary image programImage decoded)

end Airbender.Trace.Proofs
