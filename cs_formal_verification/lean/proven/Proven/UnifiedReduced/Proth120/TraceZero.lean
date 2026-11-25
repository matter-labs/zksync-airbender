module
public import Proven.UnifiedReduced.Proth120.TraceLaws
public import Proven.UnifiedReduced.RV.Row
public import Proven.UnifiedReduced.ZeroRegister
public import Proven.UnifiedReduced.RV.Laws

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Arithmetic Trace Trace.Proofs
set_option maxRecDepth 8192

private theorem modular_rd {i : RV.Instr} {d : DecoderData UnifiedFamily}
    (old : rvDecoderFields i = none) (fields : decoderFields i = some d) : d.rd ≠ 0 := by
  have nop : rvNopWrite i = false := by
    cases h : rvNopWrite i <;> simp_all [rvDecoderFields]
  simp only [decoderFields, old] at fields
  cases i <;> simp_all [rvNopWrite]
  rename_i o rd rs1 rs2
  cases o <;> simp_all <;> subst d <;> exact nop

private theorem modular_zero {row : Row proth120Modulus Kind} {setup : Table (ZMod proth120Modulus) (fields 10)}
    {entry : UnifiedReduced.RVProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints setup))
    (rd : entry.data.rd ≠ 0)
    (query : nativeDecoderQuery row.columns row.decoderColumns row.assignment = entry.query) :
    RowZeroPreserving row := by
  let w := row.assignment
  intro port present zero reads
  simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
  · exact reads _ (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
  · exfalso
    have address : (w 29).val = 0 ∧ (w 44).val = 0 ∧ (w 45).val = 0 := by
      simpa [MemoryAddress.code, pairCode, Cell.addressCode, Nat.pair_eq_pair, w] using zero
    have noRAM : w 29 = 0 := by simpa using address.1
    have low : w 44 = 0 := by simpa using address.2.1
    have location := Verification.assertion_of_holds h ⟨28, by rw [constraint_count]; decide⟩
    op_index at location
    simp [Expression.eval, Verification.environment, ← show w = row.assignment from rfl, noRAM, low] at location
    have register := congrArg (fun q : Vector (ZMod proth120Modulus) 9 => q[4]) query
    change w 7 = (entry.data.rd.toNat : ZMod proth120Modulus) at register
    have value := congrArg ZMod.val register
    rw [location, ZMod.val_zero, ZMod.val_natCast_of_lt (by
      have := entry.data.rd.isLt; change _ < 7 * 2 ^ 120 + 1; omega)] at value
    exact rd (BitVec.eq_of_toNat_eq value.symm)

private theorem standard_zero {row : Row proth120Modulus Kind} {setup : Table (ZMod proth120Modulus) (fields 10)}
    {entry : UnifiedReduced.RVProgramEntry} {i : RV.Instr}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints setup))
    (active : row.assignment row.columns.execute = 1) (fields : rvDecoderFields i = some entry.data)
    (query : nativeDecoderQuery row.columns row.decoderColumns row.assignment = entry.query) :
    RowZeroPreserving row := by
  cases row with | mk kind w =>
  cases kind
  exact UnifiedReduced.Standard.Proofs.RV.rv_row_zero_preserving (profile := .proth120) (entry := entry) (i := i) (by decide)
    (Standard.holds core) active fields query

theorem zero_writes {trace : WrapTrace} {initial cells} (inputs : TraceInputs trace initial cells)
    (accepted : Accepted trace) :
    ∀ e ∈ trace.nativeEvents, e.2.1 = (Cell.register 0).addressCode → memoryWord e.2.2.2 = 0 := by
  apply RVZero.rv_zero_writes_of_preserving (by decide) time_inverse accepted inputs.clocks inputs.image
  intro row member
  have core := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have active := accepted.active row member
  let pc := row.start.word.toBitVec
  let entry (d : DecoderData UnifiedFamily) : UnifiedReduced.RVProgramEntry := ⟨pc, RV.read initial.rom pc 4, d⟩
  obtain ⟨_, _, decoded⟩ := inputs.decoded row member
  rcases decoded with ⟨_, i, d, _, fields, query⟩ | ⟨reg, nonzero, _, query⟩
  · cases old : rvDecoderFields i with
    | none => exact modular_zero (entry := entry d) core (modular_rd old fields) query
    | some other =>
      obtain rfl : other = d := by simpa [decoderFields, old] using fields
      exact standard_zero (entry := entry other) core active old query
  · cases sel : isRead row
    · apply standard_zero (entry := entry rvNopFields) (i := .lui 0 0) core active (by rfl)
      simpa only [sel, Bool.false_eq_true, ↓reduceIte] using query
    · apply modular_zero (entry := entry ⟨.machine, 0, 0, reg, ⟨0, 0⟩, 256, 0⟩) core nonzero
      simpa only [sel, ↓reduceIte] using query

end Airbender.UnifiedReduced.Proth120
