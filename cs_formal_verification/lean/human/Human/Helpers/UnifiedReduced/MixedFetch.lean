import Human.Helpers.UnifiedReduced.MixedMemory
import Human.Helpers.Decoder.CycleFetch

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Public readonly-code profile for the physical shared pool. Tracked memory
    stays in RAM, while both program images use aligned four-byte ROM entries.
    These are address-domain conditions; no fetched value or decoder result is
    supplied. Native zero ROM shadows need their separate transport binding. -/
structure CodeProfile [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cells : List Cell) : Prop where
  /-- Native workers/instructions access tracked data above the ROM boundary. -/
  ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat
  /-- Ordinary standard/custom instruction entries are aligned public ROM words. -/
  ordinary : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  /-- Delegation CSR instruction entries use that same public code domain. -/
  callers : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0

/-- Current-state fetch for the actual shared history, including worker effects.
    The ordinary and caller projections are native metadata from original Sail
    decoding. Range/read assumptions and per-row decoded results are absent. -/
structure CurrentFetch [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (initial : Reference.RiscV.Sail.State)
    (cells : List Cell) (events : List MemoryAccess) : Prop where
  /-- Every ordinary standard/custom row reads and decodes its public instruction. -/
  ordinary : ∀ row ∈ data.machine.rows, row ∉ data.callers →
    CycleFetch initial cells events row program Mixed.decoderFields (fun entry => entry.query)
  /-- Every selected caller reads/decodes its actual full-width public CSR form. -/
  callers : ∀ row ∈ data.callers,
    CycleFetch initial cells events row data.program Delegation.Caller.decoderFields Delegation.Caller.query

end Airbender.UnifiedReduced.Caller
