module
public import Proven.Trace.Machine.CPUWriteBounds
public import Proven.UnifiedReduced.RV.Row
public import Proven.Trace.DecoderBits
public import Proven.AddSub.Selectors

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Public machine metadata fixes every unrolled arithmetic selector, including full-CSR callers. -/
theorem unrolled_machine_selectors {w : Nat → ZMod babyBearModulus} {entry : RVMachineProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (query : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (small : entry.data.mask < 512) :
    ∀ i : Fin 9, w AddSub.importedConstraintsDecoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0 := by
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
  exact unpack_decoder_bits (by decide) small boolean packed

/-- Public unified metadata fixes all nineteen native selector bits. -/
theorem unified_machine_selectors {setup : Table (ZMod babyBearModulus) (fields 10)}
    {w : Nat → ZMod babyBearModulus} {entry : RVMachineProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints setup))
    (query : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (small : entry.data.mask < 524288) :
    ∀ i : Fin 19, w UnifiedReduced.importedConstraintsDecoderColumns.flags[i] =
      if entry.data.mask.testBit i.val then 1 else 0 := by
  let bits (i : Fin 19) := w UnifiedReduced.importedConstraintsDecoderColumns.flags[i]
  have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    have bit := UnifiedReduced.Proofs.local_flags core ⟨i.val + 1, by omega⟩
    fin_cases i <;> simpa [bits, UnifiedReduced.importedConstraintsDecoderColumns] using bit
  have packed := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[8]) query
  simp only [Row.decoderQuery, nativeDecoderQuery, Row.columns, Row.decoderColumns,
    CircuitLayout.columns, CircuitLayout.decoderColumns, UnifiedReduced.importedConstraintsTraceColumns,
    UnifiedReduced.importedConstraintsDecoderColumns, RVMachineDecoderData.row, Vector.getElem_map] at packed
  change (∑ i : Fin 19, (2 ^ i.val : Nat) * bits i) = (entry.data.mask : ZMod babyBearModulus) at packed
  exact unpack_decoder_bits_general (by decide) (by simpa using small) boolean packed

end Airbender.Trace.Machine.Proofs
