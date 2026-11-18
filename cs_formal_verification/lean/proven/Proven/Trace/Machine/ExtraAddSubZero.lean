module
public import Proven.Trace.Machine.FieldCases
public import Proven.Trace.Machine.CPUWriteBounds
public import Proven.Trace.RVZeroPooled
public import Proven.Trace.RVPooled.Arithmetic

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Extra non-caller arithmetic rows preserve x0 through the existing NOP proof or a nonzero destination. -/
theorem extra_addsub_zero {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {w : Nat → ZMod babyBearModulus}
    {entry : RVMachineProgramEntry} {instruction : RV.Instr}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      ((⟨.addSub, w⟩ : Trace.Row babyBearModulus PooledFamily).constraints trace.rom))
    (fields : rvMachineExtraFields config instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Trace.Row babyBearModulus PooledFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (notCaller : w 17 ≠ 1) : RowZeroPreserving (⟨.addSub, w⟩ : Trace.Row babyBearModulus PooledFamily) := by
  by_cases discarded : entry.data.rd = 0
  · rcases extra_zero_shape fields discarded with nop | caller
    · have configured : config.arithmeticFamily = .pooled .addSub := by
        cases config <;> simp_all [RVMachineConfig.arithmeticFamily]
      let ordinary : RVPooledProgramEntry := ⟨entry.pc, entry.bits, rvNopData.mapFamily pooledArithmeticFamily⟩
      have same : entry.data = RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled) ordinary.data := by
        rw [nop, configured]
        rfl
      have nativeQuery : (⟨.addSub, w⟩ : Trace.Row babyBearModulus PooledFamily).decoderQuery = ordinary.query := by
        rw [same] at query
        exact query.trans (ordinary_query RVMachineDecoderFamily.pooled ordinary)
      exact RVZero.rv_pooled_row_zero_preserving (by decide) trace.rom _ constraints
        (entry := ordinary) (i := .op .add 0 0 0) (by rfl) rfl nativeQuery
    · have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      have flags := (AddSub.Proofs.local_flags core).2
      have boolean : ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 0 ∨
          w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 1 := by
        intro i
        have bit := flags i
        fin_cases i <;> simpa using bit
      have packed := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[8]) query
      simp only [Row.decoderQuery, nativeDecoderQuery, Row.columns, Row.decoderColumns,
        CircuitLayout.columns, CircuitLayout.decoderColumns, AddSub.importedConstraintsTraceColumns,
        AddSub.importedConstraintsDecoderColumns, RVMachineDecoderData.row, Vector.getElem_map] at packed
      change (∑ i : Fin 9, (2 ^ i.val : Nat) * w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) =
        (entry.data.mask : ZMod babyBearModulus) at packed
      have bits := unpack_decoder_bits (by decide) (extra_mask_bound fields) boolean packed
      have mode := bits ⟨7, by decide⟩
      rw [caller] at mode
      change w 17 = 1 at mode
      exact False.elim (notCaller mode)
  · intro port present address reads
    simp [Trace.Row.ports, CircuitLayout.ports, AddSub.importedConstraintsMemoryPorts] at present
    rcases present with rfl | rfl | rfl
    · exact reads _ (by simp [Trace.Row.ports, CircuitLayout.ports, AddSub.importedConstraintsMemoryPorts]) le_rfl address
    · exact reads _ (by simp [Trace.Row.ports, CircuitLayout.ports, AddSub.importedConstraintsMemoryPorts]) le_rfl address
    · have columnZero : (w 7).val = 0 := by
        simpa [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] using address
      have rd := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[4]) query
      have rdValue : w 7 = (entry.data.rd : ZMod babyBearModulus) := by
        simpa [Row.decoderQuery, nativeDecoderQuery, Row.columns, Row.decoderColumns,
          CircuitLayout.columns, CircuitLayout.decoderColumns, AddSub.importedConstraintsTraceColumns,
          AddSub.importedConstraintsDecoderColumns, RVMachineDecoderData.row] using rd
      have value := congrArg ZMod.val rdValue
      rw [ZMod.val_natCast_of_lt (by have bound := extra_destination_bound fields; unfold babyBearModulus; omega)] at value
      exact False.elim (discarded (by omega))

end Airbender.Trace.Machine.Proofs
