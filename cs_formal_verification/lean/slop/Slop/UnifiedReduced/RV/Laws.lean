import Slop.UnifiedReduced.RV.Row
import Slop.UnifiedReduced.ZeroRegister
import Slop.UnifiedReduced.Values
import Slop.UnifiedReduced.Trace
import Slop.Trace.RVZero
import Slop.Trace.RVValues
import Slop.Trace.RVProgram

/-! Whole-trace laws of an accepted unified trace on the RV route, from the RV program table: every native write to
    x0 carries zero, and all port values are bounded words. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem rv_custom_rd {i : RV.Instr} {d : DecoderData UnifiedFamily}
    (custom : rvCustomFields i = some d) (nop : rvNopWrite i = false) : d.rd ≠ 0 := by
  unfold rvCustomFields at custom
  split at custom
  · obtain rfl := Option.some.inj custom
    simpa [rvNopWrite] using nop
  · obtain ⟨tag, _, rfl⟩ := Option.map_eq_some_iff.mp custom
    simpa [rvNopWrite] using nop
  · cases custom

/-- An x0 destination of the RV table is the NOP row, a jump/branch with its discarded-write marker, or a store. -/
theorem rv_decoder_zero_cases {i : RV.Instr} {d : DecoderData UnifiedFamily}
    (fields : rvDecoderFields i = some d) (zero : d.rd = 0) :
    d = rvNopFields ∨
      (d.mask.testBit 14 = true ∧ ∃ k : Fin 4, d.mask.testBit (10 + k.val) = true) ∨
      d.mask.testBit 18 = true := by
  rcases rv_fields_cases fields with ⟨_, rfl⟩ | ⟨nop, word⟩ | ⟨_, _, j, jump, rfl⟩ |
      ⟨_, _, _, j, binary, rfl⟩ | ⟨nop, _, _, _, custom⟩
  · exact Or.inl rfl
  · unfold rvWordFields at word
    split at word
    all_goals first
      | (cases word; done)
      | (obtain rfl := Option.some.inj word
         first
           | (simp only at zero; subst zero; simp [rvNopWrite] at nop)
           | (right; right; norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]))
  · have marker := JumpBranchSlt.Proofs.rv_decoder_zero_discarded jump zero
    have masks := JumpBranchSlt.Proofs.rv_decoder_masks jump
    right; left
    change (1024 * j.mask).testBit 14 = true ∧ ∃ k : Fin 4, (1024 * j.mask).testBit (10 + k.val) = true
    rcases masks with m | m | m | m | m | m
    · rw [m] at marker; exact absurd marker (by decide)
    · rw [m] at marker; exact absurd marker (by decide)
    · rw [m] at marker; exact absurd marker (by decide)
    · rw [m]; exact ⟨by decide, ⟨0, by decide⟩⟩
    · rw [m]; exact ⟨by decide, ⟨1, by decide⟩⟩
    · rw [m]; exact ⟨by decide, ⟨3, by decide⟩⟩
  · exact False.elim (ShiftBinop.Proofs.rv_decoder_nonzero_destination binary zero)
  · exfalso
    exact rv_custom_rd custom nop zero

/-- RV sibling of `row_zero_preserving`: a row fetched from the RV table never writes a nonzero x0 value. -/
theorem rv_row_zero_preserving [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) {entry : RVProgramEntry} {i : RV.Instr}
    (fields : rvDecoderFields i = some entry.data) (query : decoderQuery w = entry.query) :
    Trace.Proofs.RowZeroPreserving (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by
  have flags := rv_decoder_selectors hp h (rv_field_bounds fields).2.1 query
  intro port present zero reads
  simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
  · exact reads _ (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
  · have address : (w 29).val = 0 ∧ (w 44).val = 0 ∧ (w 45).val = 0 := by
      simpa [MemoryAddress.code, pairCode, Cell.addressCode, Nat.pair_eq_pair] using zero
    have noRAM : w 29 = 0 := by simpa using address.1
    have location := Verification.assertion_of_holds h ⟨28, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, noRAM] at location
    have targetZero : w 7 = 0 := by
      have lo : w 44 = 0 := by simpa using address.2.1
      rw [lo] at location
      linear_combination -location
    have rd := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
    change w 7 = (entry.data.rd.toNat : ZMod p) at rd
    have originalZero : entry.data.rd = 0 := by
      have value := congrArg ZMod.val rd
      rw [targetZero, ZMod.val_zero, ZMod.val_natCast_of_lt (by have := entry.data.rd.isLt; omega)] at value
      exact BitVec.eq_of_toNat_eq value.symm
    rcases rv_decoder_zero_cases fields originalZero with nop | ⟨marker, _k, _operation⟩ | store
    · rw [nop] at flags
      have rs1 := congrArg (fun q : Vector (ZMod p) 9 => q[2]) query
      have rs2 := congrArg (fun q : Vector (ZMod p) 9 => q[3]) query
      have immLo := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
      have immHi := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
      change w 5 = (entry.data.rs1.toNat : ZMod p) at rs1
      change w 6 = (entry.data.rs2.toNat : ZMod p) at rs2
      change w 8 = (entry.data.immediate.lo : ZMod p) at immLo
      change w 9 = (entry.data.immediate.hi : ZMod p) at immHi
      rw [nop] at rs1 rs2 immLo immHi
      norm_num [rvNopFields] at rs1 rs2 immLo immHi
      have selected : w 11 = 1 := by
        simpa [rvNopFields, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 0
      have noReadRAM : w 28 = 0 := by
        simpa [rvNopFields, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using
          (show w importedConstraintsDecoderColumns.flags[17] = _ from flags 17)
      have low := Verification.assertion_of_holds h ⟨26, by rw [constraint_count]; decide⟩
      have high := Verification.assertion_of_holds h ⟨27, by rw [constraint_count]; decide⟩
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, noReadRAM, rs2] at low high
      have secondLo : w 38 = 0 := by linear_combination low
      have secondHi : w 39 = 0 := by linear_combination high
      have left := reads importedConstraintsMemoryPorts[0]
        (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
        (by change (decodeTimestamp w _).value + 0 ≤ (decodeTimestamp w _).value + 2; omega)
        (by simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, rs1])
      have right := reads importedConstraintsMemoryPorts[1]
        (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
        (by change (decodeTimestamp w _).value + 1 ≤ (decodeTimestamp w _).value + 2; omega)
        (by simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
          Cell.addressCode, noReadRAM, secondLo, secondHi])
      have leftLimbs : w 36 = 0 ∧ w 37 = 0 := by
        change Nat.pair (w 36).val (w 37).val = Nat.pair 0 0 at left
        simpa using Nat.pair_eq_pair.mp left
      have rightLimbs : w 42 = 0 ∧ w 43 = 0 := by
        change Nat.pair (w 42).val (w 43).val = Nat.pair 0 0 at right
        simpa using Nat.pair_eq_pair.mp right
      have result := zero_operands_result (by omega) h active selected
        ⟨leftLimbs.1, leftLimbs.2, rightLimbs.1, rightLimbs.2, immLo, immHi⟩
      have value := congrArg BitVec.toNat result
      rw [Word.toBitVec_toNat (destination_bounds h)] at value
      have limbs : (w 50).val = 0 ∧ (w 51).val = 0 := by
        change (w 50).val + limbBase * (w 51).val = 0 at value
        dsimp [limbBase] at value
        omega
      simp [writeToken, MemoryPort.writeCode, pairCode, limbs.1, limbs.2]
      rfl
    · have marked : w 25 = 1 := by
        simpa [marker, importedConstraintsDecoderColumns] using flags 14
      have low := Verification.assertion_of_holds h ⟨22, by rw [constraint_count]; decide⟩
      have high := Verification.assertion_of_holds h ⟨23, by rw [constraint_count]; decide⟩
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, marked] at low high
      simp [writeToken, MemoryPort.writeCode, pairCode, low, high]
      rfl
    · have ram : w 29 = 1 := by simpa [store, importedConstraintsDecoderColumns] using flags 18
      exact False.elim (zero_ne_one (noRAM.symm.trans ram))

theorem rv_zero_preserving [Fact p.Prime] (hp : 524288 < p) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {initial : RV.State}
    {addresses : List (BitVec 32)} {program : List RVProgramEntry}
    (image : rvProgramImageWith rvDecoderFields initial addresses = some program)
    (decoded : RVDecoded trace program) : ZeroPreserving trace := by
  intro row member
  cases row with
  | mk kind w =>
    cases kind
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
    obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded _ member)
    obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch image entry present
    exact rv_row_zero_preserving hp core (accepted.active _ member) fields query

/-- Read, write and terminal values of an accepted trace seeded by an RV image are bounded words. -/
theorem rv_value_bounds {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have sources : WriteSources trace :=
    fun row present => row_write_sources row (accepted.constraints row present)
  have rules := write_rules_of_sources sources
  have seed := RVValues.rv_image_bounds image
  exact ⟨read_bounds_of_rules hp inverse accepted clocks seed rules,
    write_bounds_of_rules hp inverse accepted clocks seed rules,
    terminal_bounds_of_rules hp inverse accepted clocks seed rules⟩

end Airbender.UnifiedReduced.Proofs.RV
