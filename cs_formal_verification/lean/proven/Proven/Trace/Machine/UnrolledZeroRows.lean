module
public import Proven.Trace.Machine.ExtraAddSubZero
public import Human.Trace.Machine.Model

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Every unrolled row outside the caller path preserves x0 under its public decoder metadata. -/
theorem unrolled_noncaller_zero {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {row : Trace.Row babyBearModulus PooledFamily}
    {entry : RVMachineProgramEntry} {instruction : RV.Instr}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom))
    (fields : rvMachineDecoderFields config instruction = some entry.data)
    (family : entry.data.family = .pooled row.family)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (notCaller : (row.family == .addSub && decide (Delegation.Requests.Selected row.assignment)) ≠ true) :
    RowZeroPreserving row := by
  rcases machine_fields_cases fields with extra | ⟨impossible, _⟩ | ⟨_, ordinary, projected, same⟩
  · have configured := (extra_family extra).symm.trans family
    have arithmetic : config.arithmeticFamily = .pooled .addSub := by
      cases config <;> simp_all [RVMachineConfig.arithmeticFamily]
    rw [arithmetic] at configured
    have tag : row.family = .addSub := (RVMachineDecoderFamily.pooled.inj configured).symm
    obtain ⟨kind, w⟩ := row
    change kind = .addSub at tag
    subst kind
    apply extra_addsub_zero unrolled constraints extra query
    intro selected
    apply notCaller
    simpa [Delegation.Requests.Selected, AddSub.importedConstraintsDecoderColumns] using selected
  · exact False.elim (unrolled impossible)
  · let native : RVPooledProgramEntry := ⟨entry.pc, entry.bits, ordinary⟩
    have nativeFamily : ordinary.family = row.family := by
      rw [same] at family
      exact RVMachineDecoderFamily.pooled.inj family
    have nativeQuery : row.decoderQuery = native.query := by
      rw [same] at query
      exact query.trans (ordinary_query RVMachineDecoderFamily.pooled native)
    exact RVZero.rv_pooled_row_zero_preserving (by decide) trace.rom row constraints projected nativeFamily nativeQuery

end Airbender.Trace.Machine.Proofs
