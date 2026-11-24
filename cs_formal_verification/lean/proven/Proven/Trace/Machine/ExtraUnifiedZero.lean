module
public import Proven.Trace.Machine.FieldCases
public import Proven.Trace.Machine.CPUWriteBounds
public import Proven.UnifiedReduced.RV.Laws

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs UnifiedReduced UnifiedReduced.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Extra unified instructions preserve x0 when the native caller selector is absent. -/
theorem extra_unified_zero {setup : Table (ZMod babyBearModulus) (fields 10)}
    {w : Nat → ZMod babyBearModulus} {entry : RVMachineProgramEntry} {instruction : _root_.RV.Instr}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1)
    (fields : rvMachineExtraFields .unified instruction = some entry.data)
    (query : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (notCaller : w 18 ≠ 1) : RowZeroPreserving (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) := by
  by_cases discarded : entry.data.rd = 0
  · rcases extra_zero_shape fields discarded with nop | caller
    · let ordinary : Trace.RVProgramEntry UnifiedFamily := ⟨entry.pc, entry.bits, rvNopFields⟩
      have same : entry.data = RVMachineDecoderData.ofOrdinary (family := fun _ => .unified) ordinary.data := by
        rw [nop]
        rfl
      have nativeQuery : decoderQuery w = ordinary.query := by
        rw [same] at query
        exact query.trans (ordinary_query (fun _ => .unified) ordinary)
      exact RV.rv_row_zero_preserving (by decide) h active
        (entry := ordinary) (i := .op .add 0 0 0) (by rfl) nativeQuery
    · let bits (i : Fin 19) := w importedConstraintsDecoderColumns.flags[i]
      have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
        intro i
        have flag := local_flags h ⟨i.val + 1, by omega⟩
        fin_cases i <;> simpa [bits, importedConstraintsDecoderColumns] using flag
      have packed := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[8]) query
      simp only [Row.decoderQuery, nativeDecoderQuery, Row.columns, Row.decoderColumns,
        CircuitLayout.columns, CircuitLayout.decoderColumns, importedConstraintsTraceColumns,
        importedConstraintsDecoderColumns, RVMachineDecoderData.row, Vector.getElem_map] at packed
      change (∑ i : Fin 19, (2 ^ i.val : Nat) * bits i) = (entry.data.mask : ZMod babyBearModulus) at packed
      have small : entry.data.mask < 2 ^ 19 := by have bound := extra_mask_bound fields; omega
      have flags := unpack_decoder_bits_general (by decide : 2 ^ 19 < babyBearModulus) small boolean packed
      have mode := flags ⟨7, by decide⟩
      rw [caller] at mode
      have selected : w 18 = 1 := by simpa [bits, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using mode
      exact False.elim (notCaller selected)
  · intro port present zero reads
    simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at present
    rcases present with rfl | rfl | rfl
    · exact reads _ (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
    · exact reads _ (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
    · have address : (w 29).val = 0 ∧ (w 44).val = 0 ∧ (w 45).val = 0 := by
        simpa [MemoryAddress.code, pairCode, Cell.addressCode, Nat.pair_eq_pair] using zero
      have noRAM : w 29 = 0 := by simpa using address.1
      have location := Verification.assertion_of_holds h ⟨28, by rw [constraint_count]; decide⟩
      op_index at location
      simp [Expression.eval, Verification.environment, noRAM] at location
      have targetZero : w 7 = 0 := by
        have lo : w 44 = 0 := by simpa using address.2.1
        rw [lo] at location
        linear_combination -location
      have rd := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[4]) query
      have rdValue : w 7 = (entry.data.rd : ZMod babyBearModulus) := by
        simpa [Row.decoderQuery, nativeDecoderQuery, Row.columns, Row.decoderColumns,
          CircuitLayout.columns, CircuitLayout.decoderColumns, RVMachineDecoderData.row,
          importedConstraintsTraceColumns, importedConstraintsDecoderColumns] using rd
      have value := congrArg ZMod.val rdValue
      rw [targetZero, ZMod.val_zero, ZMod.val_natCast_of_lt
        (by have bound := extra_destination_bound fields; unfold babyBearModulus; omega)] at value
      exact False.elim (discarded value.symm)

end Airbender.Trace.Machine.Proofs
