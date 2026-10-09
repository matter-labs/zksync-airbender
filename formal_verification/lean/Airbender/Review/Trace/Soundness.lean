import Airbender.Proofs.Trace.PooledROMView
import Airbender.Proofs.BabyBear

namespace Airbender.Trace

/-- Primary integrated soundness claim for the six admitted circuit families.
    `before` supplies public Sail state and bytes; `cells` lists tracked
    registers/RAM; `program` is constructed by actual pinned Sail decoding.

    `inputs` binds initialization, configuration, modeled tables and the unresolved
    jump terminal-PC condition. `accepted` checks imported richer constraints
    and logical state/memory matching; `decoded` checks decoder-table membership.
    Cryptographic enforcement and import/table-generation fidelity remain external.

    `Realizes` proves a Sail execution reaching the native terminal PC and
    cell values. `ROMView.token before` interprets zero ROM shadow tokens as
    public bytes. Operand/address bounds and actual reads are derived internally. -/
theorem pooled_native_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : PooledTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs trace before cells program)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program) :
    Realizes (PooledStep program) trace before cells (ROMView.token before) :=
  PooledROMView.trace_execution (by decide) (by decide) inputs accepted decoded

end Airbender.Trace
