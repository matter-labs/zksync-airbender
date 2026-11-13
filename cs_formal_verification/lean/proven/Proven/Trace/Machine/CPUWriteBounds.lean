module
public import Proven.Trace.Machine.Projection
public import Human.Helpers.Core.BabyBearPrime
public import Proven.Trace.RVValuesPooled
public import Proven.UnifiedReduced.Values

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- All unrolled arithmetic selectors use the existing native write bounds.
    Other families retain their existing ordinary decoder proofs. -/
theorem unrolled_row_write_bounds {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {row : Trace.Row babyBearModulus PooledFamily}
    {initial : RV.State} {cells : List Cell}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom))
    (active : row.assignment row.columns.execute = 1)
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial))
    {entry : RVMachineProgramEntry} {instruction : RV.Instr}
    (fields : rvMachineDecoderFields config instruction = some entry.data)
    (family : entry.data.family = .pooled row.family)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    RowWriteBoundsFromReads row := by
  by_cases arithmetic : row.family = .addSub
  · obtain ⟨kind, w⟩ := row
    change kind = .addSub at arithmetic
    subst kind
    apply row_write_rule_of_sources
    exact row_write_source ⟨.addSub, w⟩ trace.rom.wordMemory constraints
      (fun query included inactive => RVValues.rv_rom_disabled (by decide)
        (by rwa [wordSetup] at included) inactive)
      (fun query included => RVValues.rv_rom_bounds (by decide) (by rwa [wordSetup] at included))
  · have configured : config.arithmeticFamily = .pooled .addSub := by
      cases config <;> simp_all [RVMachineConfig.arithmeticFamily]
    have nonArithmetic : entry.data.family ≠ config.arithmeticFamily := by
      rw [family, configured]
      intro same
      exact arithmetic (RVMachineDecoderFamily.pooled.inj same)
    obtain ⟨ordinary, ordinaryFields, same⟩ := unrolled_ordinary_fields unrolled nonArithmetic fields
    have ordinaryFamily : ordinary.family = row.family := by
      rw [same] at family
      exact RVMachineDecoderFamily.pooled.inj family
    have ordinaryQuery : row.decoderQuery = (⟨entry.pc, entry.bits, ordinary⟩ : RVPooledProgramEntry).query := by
      rw [same] at query
      exact query.trans (ordinary_query RVMachineDecoderFamily.pooled ⟨entry.pc, entry.bits, ordinary⟩)
    exact RVValues.rv_pooled_row_write_rule (by decide) constraints active wordSetup subwordSetup
      ordinaryFields ordinaryFamily ordinaryQuery

/-- Every unified selector uses the existing decoder-independent native write bounds. -/
theorem unified_row_write_bounds {trace : UnifiedTrace babyBearModulus}
    {row : Trace.Row babyBearModulus UnifiedFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom)) :
    RowWriteBoundsFromReads row :=
  row_write_rule_of_sources (UnifiedReduced.Proofs.row_write_sources row constraints)

end Airbender.Trace.Machine.Proofs
