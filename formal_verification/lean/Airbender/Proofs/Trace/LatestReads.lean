import Airbender.Proofs.Trace.MemoryPaths
import Airbender.Proofs.Trace.MemoryOrigins

namespace Airbender.Trace.Proofs

/-- An increasing path has no node strictly between two consecutive nodes. -/
theorem consecutive_ranks {S : Type} (rank : S → Nat) {path : List S}
    (ordered : path.Pairwise (fun left right => rank left < rank right))
    {edge : S × S} (member : edge ∈ path.zip path.tail)
    {node : S} (nodeMember : node ∈ path) :
    ¬ (rank edge.1 < rank node ∧ rank node < rank edge.2) := by
  revert edge node
  induction path with
  | nil => simp
  | cons first rest ih =>
    intro edge member node nodeMember
    cases rest with
    | nil => simp at member
    | cons next tail =>
      have firstOrder := List.pairwise_cons.mp ordered
      have restOrder := List.pairwise_cons.mp firstOrder.2
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | later
      · rcases List.mem_cons.mp nodeMember with rfl | inRest
        · simp
        · rcases List.mem_cons.mp inRest with rfl | inTail
          · simp
          · have greater := restOrder.1 node inTail
            change ¬ (rank first < rank node ∧ rank node < rank next)
            omega
      · rcases List.mem_cons.mp nodeMember with rfl | inRest
        · have less := firstOrder.1 edge.1 (List.of_mem_zip later).1
          omega
        · exact ih firstOrder.2 later inRest

theorem latest_reads [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, LatestRead trace row port := by
  intro row rowMember port portMember
  let previous := readToken row.assignment port
  let written := writeToken row.columns row.assignment port
  let rank := fun cell : MemoryToken p => (timeOfPair cell.time).value
  have edgeMember : (previous, written) ∈ trace.memorySteps := by
    refine List.mem_flatMap.mpr ⟨row, rowMember, ?_⟩
    exact List.mem_map.mpr ⟨port, by simpa using portMember, rfl⟩
  obtain ⟨source, sourceMember, sameAddress⟩ := List.mem_map.mp
    (initialized_addresses hp inverse accepted boundary row rowMember port portMember)
  obtain ⟨path, head, _, ordered, permutation⟩ :=
    native_memory_paths hp inverse accepted boundary unique source sourceMember
  have onPath : (previous, written) ∈ path.zip path.tail := by
    apply permutation.mem_iff.mpr
    exact List.mem_filter.mpr ⟨edgeMember, by simpa [previous, readToken] using sameAddress.symm⟩
  have previousMember : previous ∈ trace.initialMemory ++ trace.rows.flatMap Row.writes := by
    apply accepted.memory.mem_iff.mpr
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨row, rowMember, ?_⟩
    exact List.mem_map.mpr ⟨port, by simpa using portMember, rfl⟩
  have clockMember : port.clock ∈ row.columns.ports := by
    rw [← ports_clocks row]
    exact Array.mem_map.mpr ⟨port, portMember, rfl⟩
  have before := (trace_clocks hp inverse accepted boundary row rowMember).accesses port.clock clockMember
  have inputs := clock_inputs hp inverse accepted boundary row rowMember
  have writeTime := (write_time (by omega)
    (base := rawPair row.assignment row.columns.initialTime)
    inputs.initial inputs.aligned (port_offset row port portMember)).2
  refine ⟨previousMember, before.1, ?_⟩
  intro cell cellMember addressEq earlier
  have cellOnPath : cell ∈ path := by
    rcases List.mem_append.mp cellMember with initial | updated
    · have equal := List.inj_on_of_nodup_map unique initial sourceMember
        (addressEq.trans sameAddress.symm)
      rw [equal]
      exact List.mem_of_head? head
    · obtain ⟨writer, writerMember, writtenMember⟩ := List.mem_flatMap.mp updated
      obtain ⟨access, accessMember, rfl⟩ := List.mem_map.mp writtenMember
      have nativeMember : (readToken writer.assignment access,
          writeToken writer.columns writer.assignment access) ∈ trace.memorySteps := by
        refine List.mem_flatMap.mpr ⟨writer, writerMember, ?_⟩
        exact List.mem_map.mpr ⟨access, accessMember, rfl⟩
      have selected : (readToken writer.assignment access,
          writeToken writer.columns writer.assignment access) ∈ path.zip path.tail := by
        apply permutation.mem_iff.mpr
        exact List.mem_filter.mpr ⟨nativeMember, by
          simpa [readToken, writeToken] using (addressEq.trans sameAddress.symm)⟩
      exact List.mem_of_mem_tail (List.of_mem_zip selected).2
  have noGap := consecutive_ranks rank (List.pairwise_map.mp ordered) onPath cellOnPath
  change ¬ (rank previous < rank cell ∧ rank cell < rank written) at noGap
  have writtenTime : rank written = (port.event row.columns row.assignment).1 := writeTime
  have belowWritten : rank cell < rank written := earlier.trans_eq writtenTime.symm
  change rank cell ≤ rank previous
  omega

end Airbender.Trace.Proofs
