module
public import Human.Trace.RVExecution
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.UnifiedReduced.RVExecutionInputs

@[expose] public section

-- The statements proven in slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean (checked by verify.sh).

namespace Airbender.UnifiedReduced

/-- Every admitted unified row (standard instructions, TRIADD and XORROT), in its history-derived order, is one
    `RV.step` of our RV32 spec from the public starting state `initial` (RAM seeded by the trace's inline
    inits/teardowns instances `inits`); the final PC and every tracked cell (registers and RAM, shadow RAM included)
    match the trace's terminal tokens. `RVExecutionInputs` lists only public boot conditions; row reads, bounds and
    results are derived. -/
def RVExecutionSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 4194304 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_byteInverse : 256 * (-7864320 : ZMod p) = 1) {trace : Trace.UnifiedTrace p} {initial : RV.State} {cells : List Trace.Cell} {program : List RVProgramEntry} {inits : List (InitsTeardowns.Witness p InitsTeardowns.unifiedLayout)} (_inputs : RVExecutionInputs trace initial cells program inits) (_accepted : Trace.Accepted trace) (_decoded : RVDecoded trace program),
    Trace.RVRealizes trace initial cells

/-- `Trace.BootRamZeroClaim` for the unified machine: under the boot inputs, every tracked RAM cell of the starting
    state reads 0, ROM shadow below 4 MiB included. It follows from `image` and `seeds` and the inits/teardowns claim
    that the `Init` tokens of checked top bits are the zero boot image of their windows
    (`InitsTeardowns.UnifiedClaim`). Residual items, not derived from a circuit: the register seeds (the chunk's public
    state, zero for the first chunk), RAM coverage (only the cells of initialised windows are tracked, so only they are
    reachable) and cross-chunk clock chaining (no other circuit writes at timestamp 0). -/
def BootRamZeroClaim : Prop :=
  ∀ {trace : Trace.UnifiedTrace babyBearModulus} {initial : RV.State} {cells : List Trace.Cell} {program : List RVProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)} (_inputs : RVBootInputs trace initial cells program inits),
    ∀ address, Trace.Cell.ram address ∈ cells → (Trace.Cell.ram address).readRV initial = some 0

end Airbender.UnifiedReduced
