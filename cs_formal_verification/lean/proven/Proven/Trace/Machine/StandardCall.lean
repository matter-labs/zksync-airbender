module
public import Human.Trace.Machine.Model
public import Proven.Trace.RVPooledRow
public import Proven.Bigint.RVCallStep
public import Proven.Blake2G.RVNativeCall
public import Proven.Blake2Round.Mask.RVNativeCall

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- RV operation tags of the existing standard native worker layouts. -/
def standardKind : Delegation.Family → RV.DelegationKind
  | .bigint => .bigint
  | .blakeG => .blakeG
  | .blakeRound => .blakeRound
  | .keccak => .keccak

/-- Every production standard worker executes the native RV delegation from its actual memory cut. -/
theorem standard_native_call {row : Delegation.Row babyBearModulus} {before after : RV.State}
    {cells : List Cell} {events : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints (modeledSetup Keccak.Controller.rows)))
    (active : row.assignment row.columns.execute = 1)
    (reads : ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded)
    (ports : ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
      cell.readRV before = some (memoryWord (port.readCode row.assignment)) ∧
      cell.readRV after = some (memoryWord (port.writeCode row.assignment)))
    (distinct : (row.memorySteps.map fun edge => edge.1.address).Nodup)
    (history : RVHistory cells events before after) (permutation : events.Perm (row.memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned) (notSpecial : row.family ≠ .keccak) (pc : RV.Word) :
    ∃ next, RV.exec (before.setPC pc) (.delegate (standardKind row.family)) = some next ∧
      RV.Same next (after.setPC (pc + 4)) := by
  obtain ⟨family, w⟩ := row
  cases family
  all_goals simp only [Delegation.Row.constraints, modeledSetup] at holds
  · have core := Verification.holds_of_sublist holds
      (List.sublist_append_left (Bigint.importedConstraints Bigint.setupTable) Bigint.importedConstraintsTimestampLookups)
    have fixedPorts : ∀ port ∈ Bigint.importedConstraintsMemoryPorts, ∃ cell ∈ cells,
        cell.addressCode = port.address.code w ∧
        cell.readRV (before.setPC pc) = some (memoryWord (port.readCode w)) ∧
        cell.readRV (after.setPC pc) = some (memoryWord (port.writeCode w)) := by
      intro port included
      obtain ⟨cell, member, code, read, written⟩ := ports port included
      refine ⟨cell, member, code, ?_, ?_⟩
      · cases cell <;> exact read
      · cases cell <;> exact written
    obtain ⟨next, executed, same⟩ := Bigint.Proofs.rv_bigint_call_local
      (start := before.setPC pc) (finish := after.setPC pc) core fixedPorts distinct aligned
      (rv_history_with_pc history pc) permutation
    exact ⟨next, executed, by simpa only [RV.State.setPC] using same⟩
  · have fixedPorts : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).ports,
        ∃ cell : Cell, cell.addressCode = port.address.code w ∧
          cell.readRV before = some (memoryWord (port.readCode w)) ∧
          cell.readRV after = some (memoryWord (port.writeCode w)) := by
      intro port included
      obtain ⟨cell, _, code, read, written⟩ := ports port included
      exact ⟨cell, code, read, written⟩
    obtain ⟨next, call, same⟩ := Blake2G.Proofs.rv_native_g_call holds active reads fixedPorts history permutation aligned pc
    exact ⟨next, by simpa only [standardKind, RV.calls, RV.exec, Option.bind_some, Option.bind_fun_some] using call, same⟩
  · have fixedPorts : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports,
        ∃ cell : Cell, cell.addressCode = port.address.code w ∧
          cell.readRV before = some (memoryWord (port.readCode w)) ∧
          cell.readRV after = some (memoryWord (port.writeCode w)) := by
      intro port included
      obtain ⟨cell, _, code, read, written⟩ := ports port included
      exact ⟨cell, code, read, written⟩
    obtain ⟨next, call, same⟩ := Blake2Round.Mask.Proofs.rv_native_round_call holds reads fixedPorts distinct
      history permutation aligned pc
    exact ⟨next, by simpa only [standardKind, RV.calls, RV.exec, Option.bind_some, Option.bind_fun_some] using call, same⟩
  · exact False.elim (notSpecial rfl)

end Airbender.Trace.Machine.Proofs
