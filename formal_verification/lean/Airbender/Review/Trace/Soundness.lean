import Airbender.Proofs.Trace.PooledROMView
import Airbender.Proofs.BabyBear

namespace Airbender.Trace

/-- Six admitted families execute the pinned Sail instructions through one
    initialized register/RAM history. ROM loads use public bytes while native
    ROM slots stay zero. Operand/address bounds and actual reads are derived.

    Review `PooledBootInputs` for public initialization, configuration, modeled
    setups and terminal-PC normalization; `Accepted`/`PooledDecoded` expose
    logical matching and lookup membership. `Realizes` concludes Sail execution
    and terminal PC/register/RAM values. The target is the richer imported JSON. -/
theorem pooled_native_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : PooledTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs trace before cells program)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program) :
    Realizes (PooledStep program) trace before cells (ROMView.token before) :=
  PooledROMView.trace_execution (by decide) (by decide) inputs accepted decoded

end Airbender.Trace
