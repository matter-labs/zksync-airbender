module
public import Proven.Trace.Machine.DelegateData
public import Proven.Trace.Machine.ExtraFlags
public import Proven.Trace.Machine.ExtraViews
public import Proven.Trace.Machine.WorkerKind

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A public decoded delegation uses the extra native caller projection. -/
theorem delegate_extra_fields {config : RVMachineConfig} {kind : RV.DelegationKind} {data : RVMachineDecoderData}
    (fields : rvMachineDecoderFields config (.delegate kind) = some data) :
    rvMachineExtraFields config (.delegate kind) = some data := by
  rcases machine_fields_cases fields with extra | ⟨_, ordinary, projected, _⟩ | ⟨_, ordinary, projected, _⟩
  · exact extra
  · have rejected : UnifiedReduced.rvDecoderFields (.delegate kind) = none := rfl
    rw [rejected] at projected
    cases projected
  · have rejected : rvPooledDecoderFields (.delegate kind) = none := rfl
    rw [rejected] at projected
    cases projected

/-- Native unrolled equations turn a public delegation entry into an actual full-CSR caller. -/
theorem unrolled_decoded_caller {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {row : Row babyBearModulus PooledFamily} {setup : PooledSetup babyBearModulus}
    {entry : RVMachineProgramEntry} {kind : RV.DelegationKind}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup))
    (family : entry.data.family = .pooled row.family)
    (fields : rvMachineDecoderFields config (.delegate kind) = some entry.data)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    (row.family == .addSub && decide (Requests.Selected row.assignment)) = true ∧
      (Requests.caller row.assignment).csr = kind.csr.toNat := by
  have extra := delegate_extra_fields fields
  have rowFamily : row.family = .addSub := RVMachineDecoderFamily.pooled.inj
    (family.symm.trans ((extra_family extra).trans (unrolled_arithmetic_family unrolled)))
  obtain ⟨tag, w⟩ := row
  change tag = .addSub at rowFamily
  subst tag
  have constraints := Verification.holds_of_sublist core
    (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
  have flags := unrolled_extra_flags constraints extra query
  constructor
  · simpa only [beq_self_eq_true, Bool.true_and, isCallerInstruction] using flags.1
  · exact machine_csr_value fields query

/-- The public unified delegation entry selects the caller bit and retains its full CSR. -/
theorem unified_decoded_caller {row : Row babyBearModulus UnifiedFamily}
    {setup : Table (ZMod babyBearModulus) (fields 10)} {entry : RVMachineProgramEntry} {kind : RV.DelegationKind}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup))
    (fields : rvMachineDecoderFields .unified (.delegate kind) = some entry.data)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    decide (UnifiedReduced.Caller.Selected row.assignment) = true ∧
      (UnifiedReduced.Caller.request row.assignment).csr = kind.csr.toNat := by
  obtain ⟨tag, w⟩ := row
  cases tag
  have constraints := Verification.holds_of_sublist core
    (List.sublist_append_left (UnifiedReduced.importedConstraints setup) UnifiedReduced.importedConstraintsTimestampLookups)
  have flags := unified_extra_flags constraints (delegate_extra_fields fields) query
  constructor
  · simpa only [isCallerInstruction] using flags.1
  · exact machine_csr_value fields query

/-- Actual public bytes determine the machine projection of every decoded program entry. -/
theorem machine_entry_fields {config : RVMachineConfig} {initial : RV.State} {addresses : List (BitVec 32)}
    {program : List RVMachineProgramEntry} {entry : RVMachineProgramEntry} {instruction : RV.Instr}
    (image : rvMachineProgramImage config initial addresses = some program) (present : entry ∈ program)
    (decoded : RV.decode entry.bits = some instruction) : rvMachineDecoderFields config instruction = some entry.data := by
  obtain ⟨_, _, actual, source, fields⟩ := machine_entry_fetch image entry present
  have same : actual = instruction := Option.some.inj (source.symm.trans decoded)
  subst actual
  exact fields

end Airbender.Trace.Machine.Proofs
