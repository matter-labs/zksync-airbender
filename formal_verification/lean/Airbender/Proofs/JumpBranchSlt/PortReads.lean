import Airbender.Proofs.JumpBranchSlt.Decoder
import Airbender.Proofs.Trace.PortReads

namespace Airbender.JumpBranchSlt.Proofs
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
    (history : Trace.Proofs.SailHistory cells (nativeEvents epoch w).reverse before after) :
    ∀ i : Fin 3, run (SailRV32.Functions.rX_bits
      (.Regidx (#v[entry.data.rs1, entry.data.rs2, entry.data.rd])[i])) before =
        .ok (Trace.Proofs.memoryWord ((importedConstraintsMemoryPorts[i]).readCode w)) before := by
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
    (history : Trace.Proofs.SailHistory cells (nativeEvents epoch w).reverse before after) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (Trace.Proofs.memoryWord (importedConstraintsMemoryPorts[2].writeCode w))) before =
        .ok () after :=
  Trace.Proofs.native_history_write epoch rfl rfl rfl history (by rfl)
    (register_addresses hp query 2)

end Airbender.JumpBranchSlt.Proofs
