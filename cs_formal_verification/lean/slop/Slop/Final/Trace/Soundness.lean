import Slop.Trace.PooledROMView
import Slop.Trace.PooledOracleComposition
import Slop.BabyBear

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
theorem pooled_native_soundness
    {trace : PooledTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs trace before cells program)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program) :
    Realizes (PooledStep program) trace before cells (ROMView.token before) :=
  PooledROMView.trace_execution (by decide) (by decide) inputs accepted decoded

/-- Integrated mixed execution for the same six families plus the pinned
    project's external-read/write-hint CSR forms. Standard ISA behavior is
    unchanged Sail. `stream` is supplied independently of the witness.

    `inputs` uses the same public initialization, configuration, modeled tables
    and terminal-PC boundary with the extended decoder. `accepted` and `decoded`
    check imported constraints, logical matching and decoder membership.
    `ports` binds external responses to their clock-ordered stream positions.

    The conclusion reaches the native final PC/cells and proves the consumed
    count. Per-row bounds, reads, decoding and execution are derived internally;
    cryptographic enforcement and import/table fidelity remain external. -/
theorem NonDeterminism.Pooled.native_soundness
    {trace : PooledTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry} {stream : List (BitVec 32)}
    (inputs : PooledBootInputs trace before cells program NonDeterminism.Pooled.decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program)
    (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    NonDeterminism.Pooled.Realizes stream program trace before cells (ROMView.token before) :=
  NonDeterminism.Pooled.Proofs.native_trace_execution (by decide) (by decide) inputs accepted decoded ports

end Airbender.Trace
