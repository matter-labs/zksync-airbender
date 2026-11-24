module
public import Proven.WordMemory
public import Proven.Trace.Family.Timestamps
public import Proven.Trace.RVProgram
public import Proven.JumpBranchSlt.Trace
public import Proven.MulDiv.Trace
public import Proven.ShiftBinop.Trace
public import Proven.SubwordMemory.Trace
public import Proven.JumpBranchSlt.RVDecoder
public import Proven.MulDiv.RVDecoder
public import Proven.ShiftBinop.RVDecoder
public import Proven.SubwordMemory.RVDecoder
public import Proven.AddSub
public import Proven.CleanCore.Circuit.Operations
public import Proven.Defs.Helpers.Memory.Ports

@[expose] public section

/-! RV-route twins of the per-family x0 row lemmas (piece E0, row level).

    The originals take `source : entry.SourceWith before projection` (public bytes, decoding and the metadata
    projection). Their proofs read only the projection equation. Here an `RVProgramEntry` is passed with the
    equation `projection i = some entry.data` for an `RV.Instr` `i`, and the decoder facts are the RV twins
    (`rv_decoder_*`, `rv_native_query_*`). -/

namespace Airbender.Trace.RVZero
open Arithmetic Trace.Proofs

/-- A family row's fetch facts: its RV program entry, the projection equation, family, query and selectors. -/
def RVFetched {p : Nat} (row : Row p) (projection : RV.Instr → Option DecoderData) : Prop :=
  ∃ (entry : RVProgramEntry) (i : RV.Instr), projection i = some entry.data ∧ entry.data.family = row.family ∧
    row.decoderQuery = entry.query ∧
    ∀ i : Fin row.decoderColumns.flags.size,
      row.assignment row.decoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0

theorem addsub_zero_preprocessing {p : Nat} [Fact p.Prime]
    {projection : RV.Instr → Option DecoderData} (rules : RVDecoderRules projection) (hp : limbBase < p)
    {w : Nat → ZMod p}
    (fetched : RVFetched (⟨.addSub, w⟩ : Row p) projection)
    (zero : AddSub.importedConstraintsMemoryPorts[2].address.code w = (Cell.register 0).addressCode) :
    w 5 = 0 ∧ w 6 = 0 ∧ w 8 = 0 ∧ w 9 = 0 ∧ w 10 = 1 ∧
      ∀ k, 11 ≤ k → k ≤ 16 → w k = 0 := by
  obtain ⟨entry, i, fields, family, query, flags⟩ := fetched
  have rd := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
  change w 7 = (entry.data.rd.toNat : ZMod p) at rd
  have columnZero : (w 7).val = 0 := by
    simpa [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, Cell.addressCode] using zero
  have value := congrArg ZMod.val rd
  rw [ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt (by dsimp [limbBase] at hp; omega))] at value
  have nop := rules.zeroNop _ _ fields family
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
    {projection : RV.Instr → Option DecoderData} (rules : RVDecoderRules projection) (hp : limbBase < p)
    {w : Nat → ZMod p} {rom : Table (ZMod p) (fields 9)}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.importedConstraints rom))
    (fetched : RVFetched (⟨.wordMemory, w⟩ : Row p) projection) :
    WordMemory.importedConstraintsMemoryPorts[2].address.code w ≠ (Cell.register 0).addressCode := by
  intro zero
  have address : w 10 = 0 ∧ w 25 = 0 ∧ w 26 = 0 := by
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, Cell.addressCode] using zero
  have rdZero : w 7 = 0 := by
    have register := WordMemory.Proofs.register_address false constraints address.1
    change w 25 = w 7 ∧ w 26 = 0 at register
    rw [← register.1, address.2.1]
  obtain ⟨entry, i, fields, family, query, flags⟩ := fetched
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) query
  change (∑ i : Fin 1, (2 ^ i.val : Nat) * w #[10][i]) = (entry.data.mask : ZMod p) at packed
  have selected : w 10 = (entry.data.mask : ZMod p) := by simpa using packed
  have mask := congrArg ZMod.val selected
  have small := (rules.bounds _ _ fields).2
  rw [ZMod.val_natCast_of_lt (by dsimp [limbBase] at hp; omega), address.1, ZMod.val_zero] at mask
  have nonzero := rules.loadNonzero _ _ fields family mask.symm
  have rd := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
  change w 7 = (entry.data.rd.toNat : ZMod p) at rd
  have value := congrArg ZMod.val rd
  rw [ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt (by dsimp [limbBase] at hp; omega)),
    rdZero, ZMod.val_zero] at value
  exact nonzero (BitVec.eq_of_toNat_eq (by simpa using value.symm))

/-- RV twin of `row_zero_write_from_reads` for the ADD-family and load/store families. -/
theorem row_zero_write_from_reads {p : Nat} [Fact p.Prime]
    {projection : RV.Instr → Option DecoderData} (rules : RVDecoderRules projection) (hp : 196608 < p)
    (row : Row p)
    (setup : Table (ZMod p) (fields 9))
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup)) (fetched : RVFetched row projection)
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
        rw [Word.toBitVec_toNat (word := ⟨(w 33).val, (w 34).val⟩) (AddSub.Proofs.written_limb_bounds core)] at value
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

/-- x0 destination of a JumpBranchSlt row: decoding discards it (`mask` bit 4 set), so the row's write is zero. -/
private theorem jumpBranch_zero_destination {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) JumpBranchSlt.importedConstraints)
    (discarded : w 15 = 1) : w 30 = 0 ∧ w 31 = 0 := by
  have low := Verification.assertion_of_holds h
    ⟨10, by rw [JumpBranchSlt.constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h
    ⟨11, by rw [JumpBranchSlt.constraint_count]; decide⟩
  op_index at low high
  simp [Expression.eval, Verification.environment, discarded] at low high
  exact ⟨low, high⟩

theorem jumpBranch_row_zero_preserving {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    (row : Row p JumpBranchSlt.TraceKind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) JumpBranchSlt.importedConstraints)
    (entry : JumpBranchSlt.RVProgramEntry) {i : RV.Instr} (fields : JumpBranchSlt.rvDecoderFields i = some entry.data)
    (query : row.decoderQuery = entry.query)
    (flags : ∀ i : Fin 5, row.assignment JumpBranchSlt.importedConstraintsDecoderColumns.flags[i] =
      if entry.data.mask.testBit i.val then 1 else 0) :
    Trace.Proofs.RowZeroPreserving row := by
  intro port present address reads
  simp [Row.ports, JumpBranchSlt.importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, JumpBranchSlt.importedConstraintsMemoryPorts]) le_rfl address
  · exact reads _ (by simp [Row.ports, JumpBranchSlt.importedConstraintsMemoryPorts]) le_rfl address
  · have index := (Trace.Proofs.rv_native_query_indices hp query).2.2
    change (row.assignment 7).val = entry.data.rd.toNat at index
    have nativeZero : (row.assignment 7).val = 0 := by
      change Nat.pair 0 (Nat.pair (row.assignment 7).val 0) = Nat.pair 0 (Nat.pair 0 0) at address
      exact (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp address).2).1
    have zero : entry.data.rd = 0 := by
      apply BitVec.eq_of_toNat_eq
      change entry.data.rd.toNat = 0
      exact index.symm.trans nativeZero
    have mask := JumpBranchSlt.Proofs.rv_decoder_zero_discarded fields zero
    have selected : row.assignment 15 = 1 := by
      simpa [JumpBranchSlt.importedConstraintsDecoderColumns, mask] using flags ⟨4, by decide⟩
    obtain ⟨low, high⟩ := jumpBranch_zero_destination h selected
    simp [writeToken, MemoryPort.writeCode, pairCode, low, high]
    rfl

theorem mulDiv_row_zero_preserving {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    (row : Row p MulDiv.TraceKind) (entry : MulDiv.RVProgramEntry) {i : RV.Instr}
    (fields : MulDiv.rvDecoderFields i = some entry.data)
    (query : row.decoderQuery = entry.query) :
    Trace.Proofs.RowZeroPreserving row := by
  intro port present address reads
  simp [Row.ports, MulDiv.importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, MulDiv.importedConstraintsMemoryPorts]) le_rfl address
  · exact reads _ (by simp [Row.ports, MulDiv.importedConstraintsMemoryPorts]) le_rfl address
  · have index := (Trace.Proofs.rv_native_query_indices hp query).2.2
    change (row.assignment 7).val = entry.data.rd.toNat at index
    have nativeZero : (row.assignment 7).val = 0 := by
      change Nat.pair 0 (Nat.pair (row.assignment 7).val 0) = Nat.pair 0 (Nat.pair 0 0) at address
      exact (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp address).2).1
    have zero : entry.data.rd = 0 := by
      apply BitVec.eq_of_toNat_eq
      change entry.data.rd.toNat = 0
      exact index.symm.trans nativeZero
    exact (MulDiv.Proofs.rv_decoder_nonzero_destination fields zero).elim

theorem shiftBinop_row_zero_preserving {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    (row : Row p ShiftBinop.TraceKind) (entry : ShiftBinop.RVProgramEntry) {i : RV.Instr}
    (fields : ShiftBinop.rvDecoderFields i = some entry.data)
    (query : row.decoderQuery = entry.query) :
    Trace.Proofs.RowZeroPreserving row := by
  intro port present address reads
  simp [Row.ports, ShiftBinop.importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, ShiftBinop.importedConstraintsMemoryPorts]) le_rfl address
  · exact reads _ (by simp [Row.ports, ShiftBinop.importedConstraintsMemoryPorts]) le_rfl address
  · have index := (Trace.Proofs.rv_native_query_indices hp query).2.2
    change (row.assignment 7).val = entry.data.rd.toNat at index
    have nativeZero : (row.assignment 7).val = 0 := by
      change Nat.pair 0 (Nat.pair (row.assignment 7).val 0) = Nat.pair 0 (Nat.pair 0 0) at address
      exact (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp address).2).1
    have zero : entry.data.rd = 0 := by
      apply BitVec.eq_of_toNat_eq
      change entry.data.rd.toNat = 0
      exact index.symm.trans nativeZero
    exact (ShiftBinop.Proofs.rv_decoder_nonzero_destination fields zero).elim

theorem subword_row_zero_preserving {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    (row : Row p SubwordMemory.TraceKind) (setup : Table (ZMod p) (fields 9))
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (SubwordMemory.importedConstraints setup))
    (entry : SubwordMemory.RVProgramEntry) {i : RV.Instr}
    (fields : SubwordMemory.rvDecoderFields i = some entry.data)
    (query : row.decoderQuery = entry.query) :
    Trace.Proofs.RowZeroPreserving row := by
  intro port present address reads
  simp [Row.ports, SubwordMemory.importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, SubwordMemory.importedConstraintsMemoryPorts]) le_rfl address
  · exact reads _ (by simp [Row.ports, SubwordMemory.importedConstraintsMemoryPorts]) le_rfl address
  · have flag := SubwordMemory.Proofs.rv_decoder_selectors hp core
      (SubwordMemory.Proofs.rv_decoder_field_bounds fields).2.1 query 0
    change row.assignment 10 = (if entry.data.mask.testBit 0 then 1 else 0) at flag
    change Nat.pair (row.assignment 10).val
      (Nat.pair (row.assignment 27).val (row.assignment 28).val) =
      Nat.pair 0 (Nat.pair 0 0) at address
    cases store : entry.data.mask.testBit 0
    · have selected : row.assignment 10 = 0 := by simpa only [store, Bool.false_eq_true, ite_false] using flag
      have register := SubwordMemory.Proofs.register_address false core selected
      simp only [Bool.false_eq_true, ite_false] at register
      have index := (Trace.Proofs.rv_native_query_indices hp query).2.2
      change (row.assignment 7).val = entry.data.rd.toNat at index
      rw [selected, ZMod.val_zero] at address
      have zeroLo := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp address).2).1
      rw [register.1] at zeroLo
      have zero : entry.data.rd = 0 := by
        apply BitVec.eq_of_toNat_eq
        exact index.symm.trans zeroLo
      exact (SubwordMemory.Proofs.rv_decoder_load_nonzero fields store zero).elim
    · have selected : row.assignment 10 = 1 := by simpa only [store, ite_true] using flag
      simp [selected, ZMod.val_one] at address

end Airbender.Trace.RVZero
