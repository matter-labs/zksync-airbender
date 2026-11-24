module
public import Proven.KeccakSplit.Contract
public import Proven.KeccakSplit.Chain.RVCalls
public import Proven.KeccakSplit.RVLink
public import Proven.Trace.Machine.WorkerKind

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Native controller constraints and shared-memory reads supply the split call arguments. -/
theorem split_native_call {row : Keccak.Split.Native.Row babyBearModulus} {before after : RV.State}
    {cells : List Cell} {events : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints)
    (active : row.assignment row.columns.execute = 1)
    (reads : ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded)
    (ports : ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
      cell.readRV before = some (memoryWord (port.readCode row.assignment)) ∧
      cell.readRV after = some (memoryWord (port.writeCode row.assignment)))
    (history : RVHistory cells events before after) (permutation : events.Perm (row.memorySteps.map transferEvent))
    (pc : RV.Word) :
    ∃ next, RV.exec (before.setPC pc) (.delegate row.kind.delegation) = some next ∧
      RV.Same next (after.setPC (pc + 4)) := by
  obtain ⟨index, kind, control, _, _⟩ := Keccak.Split.Native.Proofs.row_facts.effects row holds active reads
  have register (offset register : Nat) (small : register < 32)
      (placement : ∃ bound : offset < row.ports.size, (row.ports[offset]).address = .constantRegister register) :
      (Cell.register register).readRV before = some (row.readWord offset).toBitVec := by
    obtain ⟨bound, address⟩ := placement
    obtain ⟨cell, _, code, read, _⟩ := ports _ (Array.getElem_mem bound)
    have same : cell = .register register := by
      apply cell_address_injective
      rw [code, address]
      simp [MemoryAddress.code, Cell.addressCode, Nat.mod_eq_of_lt small]
    rw [same] at read
    rw [Keccak.Split.Native.Proofs.readWord_eq row bound]
    exact read
  have arguments : Keccak.Split.Call.RVArgumentsAt index.val before := by
    refine ⟨_, _, register 0 10 (by decide) (Keccak.Split.Native.Proofs.register_ports row).1,
      register 1 11 (by decide) (Keccak.Split.Native.Proofs.register_ports row).2, ?_, ?_⟩
    · rw [control]
      rfl
    · have aligned := Keccak.Split.Native.Proofs.row_facts.aligned row holds
      simp only [Word.toBitVec, BitVec.toNat_ofNat]
      omega
  have execution := Keccak.Split.Native.Proofs.rv_row_executes row index holds active arguments reads history permutation
    (fun port present => by
      obtain ⟨cell, _, code, read, _⟩ := ports port present
      exact ⟨cell, code, read⟩)
  obtain ⟨next, call, same⟩ := Keccak.Split.Call.Proofs.split_call_link index execution pc
  rw [kind] at call
  exact ⟨next, by simpa only [RV.calls, RV.exec, Option.bind_some, Option.bind_fun_some] using call, same⟩

end Airbender.Trace.Machine.Proofs
