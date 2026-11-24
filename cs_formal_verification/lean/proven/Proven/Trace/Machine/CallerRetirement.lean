module
public import Proven.Trace.Machine.Selectors
public import Proven.Trace.Machine.DelegateData
public import Proven.Trace.Machine.Fetch
public import Proven.Trace.RVPooled.AddSub

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The unrolled native caller retires to the public entry PC plus four. -/
theorem unrolled_caller_retirement {w : Nat → ZMod babyBearModulus} {entry : RVMachineProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (query : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).finish.word.toBitVec = entry.pc + 4 := by
  have word := machine_native_query_pc_word (by decide : limbBase < babyBearModulus) query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at word
  have successor := AddSub.Proofs.pc_successor (by decide) (by decide) core
    (initial := Word.ofBitVec entry.pc) (final := Word.mk (w 19).val (w 20).val)
    ⟨by rw [← word]; exact (ZMod.natCast_zmod_val _).symm,
     by rw [← word]; exact (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ (Word.ofBitVec_bound _)
  change (Word.mk (w 19).val (w 20).val).toBitVec = _
  rw [successor.2.2, Word.ofBitVec_roundtrip]

/-- Public delegation metadata disables unified branch/jump control and fixes caller retirement. -/
theorem unified_caller_retirement {kind : RV.DelegationKind}
    {setup : Table (ZMod babyBearModulus) (fields 10)} {w : Nat → ZMod babyBearModulus} {entry : RVMachineProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints setup))
    (active : w 4 = 1) (fields : rvMachineDecoderFields .unified (.delegate kind) = some entry.data)
    (query : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).finish.word.toBitVec = entry.pc + 4 := by
  have data := (machine_delegate_fields fields).2
  have flags := unified_machine_selectors core query (by rw [data]; change (128 : Nat) < 524288; decide)
  have outside (k : Fin 4) : w (21 + k.val) = 0 := by
    have flag := flags ⟨10 + k.val, by omega⟩
    rw [data] at flag
    fin_cases k <;>
      simpa [UnifiedReduced.importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  have word := machine_native_query_pc_word (by decide : limbBase < babyBearModulus) query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at word
  have successor := UnifiedReduced.Proofs.pc_successor (by decide) core active
    ⟨outside 0, outside 1, outside 2, outside 3⟩
    (initial := Word.ofBitVec entry.pc) (final := Word.mk (w 30).val (w 31).val)
    ⟨by rw [← word]; exact (ZMod.natCast_zmod_val _).symm,
     by rw [← word]; exact (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ (Word.ofBitVec_bound _)
  change (Word.mk (w 30).val (w 31).val).toBitVec = _
  rw [successor.2.2, Word.ofBitVec_roundtrip]

/-- The public fetched delegation and native retirement turn a worker call into an actual CPU step. -/
theorem fetched_delegate_cycle {Kind : Type} [CircuitLayout Kind]
    {config : RVMachineConfig} {initial before after : RV.State} {addresses : List (BitVec 32)}
    {program : List RVMachineProgramEntry} {row : Row babyBearModulus Kind} {entry : RVMachineProgramEntry}
    {kind : RV.DelegationKind} (image : rvMachineProgramImage config initial addresses = some program)
    (present : entry ∈ program) (decoded : RV.decode entry.bits = some (.delegate kind))
    (rom : before.rom = initial.rom) (retirement : row.finish.word.toBitVec = entry.pc + 4)
    (call : ∃ next, RV.exec (before.setPC entry.pc) (.delegate kind) = some next ∧
      RV.Same next (after.setPC (entry.pc + 4))) :
    ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec) := by
  obtain ⟨instruction, source, _, fetch⟩ := machine_current_fetch image present rom (before := before.setPC entry.pc) rfl
  have same : instruction = .delegate kind := Option.some.inj (source.symm.trans decoded)
  subst instruction
  obtain ⟨next, executed, agreement⟩ := call
  exact ⟨next, fetch.trans executed, by simpa only [retirement] using agreement⟩

end Airbender.Trace.Machine.Proofs
