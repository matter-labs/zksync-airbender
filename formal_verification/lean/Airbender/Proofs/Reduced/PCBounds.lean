import Airbender.Proofs.Reduced.OrdinaryCycles
import Airbender.Proofs.VerifierBoundary

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- Exact public row queries and the typed verifier boundary bound every native PC.
CPU and worker RAM matching stay separate from this state-path argument. -/
theorem native_pc_bounds [Fact p.Prime] (hp : FieldCapacity.NoWrap p limbBase)
    {data : RequestTrace p} {program : List PooledProgramEntry}
    (accepted : MixedMemoryAccepted data program)
    (closure : VerifierBoundary.BootClosure data.machine.initial
      (data.machine.rows.map Row.start) (data.machine.rows.map Row.finish)) :
    ∀ row ∈ data.machine.rows, row.start.word.Bounded ∧ row.finish.word.Bounded := by
  have incoming : ∀ row ∈ data.machine.rows, row.start.word.Bounded := by
    intro row member
    by_cases called : row ∈ data.callers
    · have family := (caller_member called).2
      have decoded := accepted.decoded row called
      change ∃ i : Fin data.program.length,
        Delegation.Caller.nativeQuery row.assignment = Delegation.Caller.query (data.program.get i) at decoded
      obtain ⟨i, query⟩ := decoded
      have word := Delegation.Caller.Proofs.query_pc hp query
      cases row with
      | mk kind w =>
        cases family
        change (Word.mk (w 0).val (w 1).val).Bounded
        change Word.mk (w 0).val (w 1).val = Word.ofBitVec (data.program.get i).pc at word
        exact word.symm ▸ Word.ofBitVec_bound (data.program.get i).pc
    · obtain ⟨entry, _, _, query⟩ := decoder_member (accepted.ordinaryDecoded row member called)
      have word := native_query_pc_word hp query
      change row.start.word = Word.ofBitVec entry.pc at word
      exact word.symm ▸ Word.ofBitVec_bound entry.pc
  have terminal := VerifierBoundary.Proofs.terminal_bound hp accepted.states
    (VerifierBoundary.Proofs.boot_closure closure)
  intro row member
  refine ⟨incoming row member, ?_⟩
  have endpoint : row.finish ∈ data.machine.terminal :: data.machine.rows.map Row.start :=
    accepted.states.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  rcases List.mem_cons.mp endpoint with same | next
  · exact same ▸ terminal
  · obtain ⟨other, included, same⟩ := List.mem_map.mp next
    exact same ▸ incoming other included

end Airbender.AddSub.Modular.External.Caller.Proofs
