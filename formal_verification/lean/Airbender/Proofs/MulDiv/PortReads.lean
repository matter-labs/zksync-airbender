import Airbender.Proofs.MulDiv.Decoder
import Airbender.Review.MulDiv.Trace
import Airbender.Proofs.Trace.PortReads

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

abbrev nativeEvents (epoch : Nat) (w : Nat → ZMod p) :=
  Trace.Proofs.nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w

/-- The imported query identifies all three direct-register port addresses. -/
theorem register_addresses {p : Nat} (hp : limbBase < p)
    {w : Nat → ZMod p} {entry : ProgramEntry} (query : decoderQuery w = entry.query) :
    ∀ i : Fin 3, (importedConstraintsMemoryPorts[i]).address.code w =
      (Cell.register (#v[entry.data.rs1, entry.data.rs2, entry.data.rd])[i]).addressCode := by
  intro i
  obtain ⟨left, right, destination⟩ := Trace.Proofs.native_query_indices hp query
  dsimp only [importedConstraintsDecoderColumns] at left right destination
  fin_cases i <;> simp [importedConstraintsMemoryPorts, MemoryAddress.code,
    Cell.addressCode, left, right, destination]

/-- A complete native row history supplies Sail's actual pre-state reads.
    The first two ports refresh clocks, including when either aliases rd. -/
theorem register_reads {p : Nat} (hp : limbBase < p)
    {w : Nat → ZMod p} {entry : ProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State} (query : decoderQuery w = entry.query)
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after) :
    ∀ i : Fin 3, run (SailRV32.Functions.rX_bits
      (.Regidx (#v[entry.data.rs1, entry.data.rs2, entry.data.rd])[i])) before =
        .ok (Trace.memoryWord ((importedConstraintsMemoryPorts[i]).readCode w)) before := by
  intro i
  have present : importedConstraintsMemoryPorts[i] ∈ importedConstraintsMemoryPorts := by
    fin_cases i <;> simp [importedConstraintsMemoryPorts]
  exact Trace.Proofs.native_history_read epoch rfl rfl rfl history present
    (register_addresses hp query i)

/-- The destination port performs the actual Sail write. No expected result is
    supplied: its value comes from the imported witness's destination columns. -/
theorem register_write {p : Nat} (hp : limbBase < p)
    {w : Nat → ZMod p} {entry : ProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State} (query : decoderQuery w = entry.query)
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (Trace.memoryWord (importedConstraintsMemoryPorts[2].writeCode w))) before =
        .ok () after :=
  Trace.Proofs.native_history_write epoch rfl rfl rfl history (by rfl)
    (register_addresses hp query 2)

/-- Actual decoder membership identifies every native access as a GPR port.
    Hence these traces cannot overwrite any fetched program byte. -/
theorem native_register_addresses {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : NativeTrace p} {program : List ProgramEntry} (decoded : Decoded trace program)
    {event : MemoryAccess} (member : event ∈ trace.nativeEvents) :
    ∃ index : BitVec 5, event.2.1 = (Cell.register index).addressCode := by
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value,
      edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp rowEdge
  obtain ⟨entry, _, _, query⟩ := Trace.Proofs.decoder_member (decoded row rowMember)
  have addresses := register_addresses hp query
  simp [Row.ports, importedConstraintsMemoryPorts] at portMember
  rcases portMember with rfl | rfl | rfl
  · exact ⟨entry.data.rs1, addresses 0⟩
  · exact ⟨entry.data.rs2, addresses 1⟩
  · exact ⟨entry.data.rd, addresses 2⟩

end Airbender.MulDiv.Proofs
