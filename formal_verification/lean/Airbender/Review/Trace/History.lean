import Airbender.Proofs.Trace.MemoryHistory
import Airbender.Proofs.Mersenne31

namespace Airbender.Trace

/-- Initialized v2 ADD/SUB logical memory soundness. The native equations,
    active state matching, memory matching and public initial clock bounds
    construct a complete Clean online history and force newest preceding reads.
    Seed addresses are unique. No expected reads or per-row clocks are premises.
    Public Sail image binding, decoding and cryptographic enforcement are separate. -/
theorem native_memory_soundness {trace : Data mersenne31Modulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    (∃ history, MemoryHistory trace history) ∧
      ∀ row ∈ trace.rows, ∀ port ∈ row.ports, LatestRead trace row port :=
  ⟨Proofs.native_memory_history (by decide) accepted boundary unique,
    Proofs.latest_reads (by decide) accepted boundary unique⟩

end Airbender.Trace
