module
public import Proven.Trace.Machine.StandardCall
public import Proven.Trace.Machine.AnyWorker
public import Proven.Trace.Machine.DelegateData
public import Proven.KeccakSplit.RVSpec

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The RV delegation kind of either native worker pool. -/
def AnyWorker.kind (row : AnyWorker p) : RV.DelegationKind :=
  match row with
  | .inl standard => standardKind standard.family
  | .inr split => split.kind.delegation

/-- The native request retains the exact full CSR of its RV delegation. -/
theorem any_worker_csr (row : AnyWorker p) : row.request.csr = row.kind.csr.toNat := by
  cases row with
  | inl standard => cases standard with | mk family w => cases family <;> rfl
  | inr split => cases split with | mk kind w => cases kind <;> rfl

/-- Full CSR identities distinguish all seven native worker kinds. -/
theorem delegation_csr_injective : Function.Injective (fun kind : RV.DelegationKind => kind.csr.toNat) := by
  intro first last same
  cases first <;> cases last <;> first | rfl | (norm_num [RV.DelegationKind.csr] at same)

/-- A full native CSR equality selects the same RV worker kind. -/
theorem any_worker_kind {row : AnyWorker p} {kind : RV.DelegationKind}
    (same : row.request.csr = kind.csr.toNat) : row.kind = kind :=
  delegation_csr_injective ((any_worker_csr row).symm.trans same)

/-- The native rs2 value of a decoded delegation is its full CSR, without register truncation. -/
theorem machine_csr_value {Kind : Type} [CircuitLayout Kind] {row : Row babyBearModulus Kind}
    {config : RVMachineConfig} {kind : RV.DelegationKind} {entry : RVMachineProgramEntry}
    (fields : rvMachineDecoderFields config (.delegate kind) = some entry.data)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    (row.assignment row.decoderColumns.rs2).val = kind.csr.toNat := by
  have data := (machine_delegate_fields fields).2
  have source := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[3]) query
  rw [data] at source
  simp only [Row.decoderQuery, nativeDecoderQuery, RVMachineDecoderData.row, Vector.getElem_map] at source
  change row.assignment row.decoderColumns.rs2 = (kind.csr.toNat : ZMod babyBearModulus) at source
  rw [source, ZMod.val_natCast_of_lt]
  cases kind <;> norm_num [RV.DelegationKind.csr, babyBearModulus]

end Airbender.Trace.Machine.Proofs
