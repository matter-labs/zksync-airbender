import Airbender.Proofs.Trace.Slots

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]

private abbrev readToken (row : Row p Kind) (port : MemoryPort) : MemoryToken p :=
  Trace.readToken row.assignment port

private abbrev writeToken (row : Row p Kind) (port : MemoryPort) : MemoryToken p :=
  Trace.writeToken row.columns row.assignment port

private def accessTime (row : Row p Kind) (port : MemoryPort) : Nat :=
  (port.event row.columns row.assignment).1

theorem earlier_write [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (row : Row p Kind) (member : row ∈ trace.rows) (port : MemoryPort) (portMember : port ∈ row.ports) :
    Trace.readToken row.assignment port ∈ trace.initialMemory ∨
      ∃ writer ∈ trace.rows, ∃ source ∈ writer.ports,
        Trace.writeToken writer.columns writer.assignment source = Trace.readToken row.assignment port ∧
          (source.event writer.columns writer.assignment).1 <
            (port.event row.columns row.assignment).1 := by
  have readMember : readToken row port ∈ trace.rows.flatMap Row.reads := by
    refine List.mem_flatMap.mpr ⟨row, member, ?_⟩
    exact List.mem_map.mpr ⟨port, by simpa using portMember, rfl⟩
  have matched := accepted.memory.mem_iff.mpr (List.mem_append_right _ readMember)
  rcases List.mem_append.mp matched with initial | written
  · exact Or.inl initial
  · obtain ⟨writer, writerMember, tokenMember⟩ := List.mem_flatMap.mp written
    obtain ⟨source, sourceMember, tokenEq⟩ := List.mem_map.mp tokenMember
    have sourcePortMember : source ∈ writer.ports := by simpa using sourceMember
    have inputs := clock_inputs hp inverse accepted boundary writer writerMember
    have canonical := (write_time (by omega)
      (base := rawPair writer.assignment writer.columns.initialTime)
      inputs.initial inputs.aligned (port_offset writer source sourcePortMember)).2
    have clockMember : port.clock ∈ row.columns.ports := by
      rw [← ports_clocks row]
      exact Array.mem_map.mpr ⟨port, portMember, rfl⟩
    have order := (trace_clocks hp inverse accepted boundary row member).accesses port.clock clockMember
    refine Or.inr ⟨writer, writerMember, source, sourcePortMember, tokenEq, ?_⟩
    calc
      accessTime writer source = (timeOfPair (writeToken writer source).time).value := canonical.symm
      _ = (timeOfPair (readToken row port).time).value :=
        congrArg (fun token : MemoryToken p => (timeOfPair token.time).value) tokenEq
      _ < accessTime row port := order.1

/-- Native matching and decreasing prior-write times root every access at the
    public initial memory image. No desired address or read value is assumed. -/
theorem initialized_addresses [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      port.address.code row.assignment ∈ trace.initialMemory.map MemoryToken.address := by
  have rooted : ∀ time : Nat, ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      accessTime row port = time →
        ∃ initial ∈ trace.initialMemory, initial.address = port.address.code row.assignment := by
    intro time
    induction time using Nat.strong_induction_on with
    | h time ih =>
      intro row member port portMember clock
      rcases earlier_write hp inverse accepted boundary row member port portMember with initial | prior
      · exact ⟨readToken row port, initial, rfl⟩
      · obtain ⟨writer, writerMember, source, sourceMember, same, order⟩ := prior
        change accessTime writer source < accessTime row port at order
        have earlier : accessTime writer source < time := by simpa only [clock] using order
        obtain ⟨origin, originMember, addressEq⟩ :=
          ih _ earlier writer writerMember source sourceMember rfl
        exact ⟨origin, originMember, addressEq.trans (congrArg MemoryToken.address same)⟩
  intro row member port portMember
  obtain ⟨origin, originMember, addressEq⟩ := rooted _ row member port portMember rfl
  exact List.mem_map.mpr ⟨origin, originMember, addressEq⟩

end Airbender.Trace.Proofs
