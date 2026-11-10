module
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Context.RVPooledBoundary
public import Human.Helpers.Decoder.RVExternalInput
public import Human.Helpers.Decoder.PooledExternalInput
public import Human.Trace.RVExecution

@[expose] public section

/-! Six-family trace claims over our RV32 spec: an accepted six-family trace is a run of `RV.run` from the public
    starting state `initial : RV.State`. Proven in
    `slop/Slop/Final/Trace/RVSoundness.lean` (checked in `test/Checks/Claims.lean`). The program table is the RV one
    (`rvProgramImageWith`): PC in ROM and 4-byte aligned is its fetch guard. A load into x0 is a no-op in our spec, as in
    Airbender, so no load restriction is needed. -/

namespace Airbender.Trace

/-- Every accepted six-family trace booted from the public state `initial` (RAM seeded by the inits/teardowns
    instances `inits`) is a run of our spec reaching its terminal PC and tracked cell values. The input stream is not
    touched: the standard table has no CSR 0x7C0 instruction. `accepted` checks the imported constraints and logical
    state/memory matching, `decoded` decoder-table membership; cryptographic enforcement and import/table-generation
    fidelity remain external. -/
def RVPooledNativeSoundnessClaim : Prop :=
  ∀ {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)} (_inputs : RVPooledBootInputs trace initial cells program inits) (_accepted : Accepted trace) (_decoded : RVPooledDecoded trace program),
    RVRealizes trace initial cells

/-- How Airbender's zero starting RAM (`Human/ISA/State.lean`) is justified by the inits/teardowns circuit: under the
    boot inputs, every tracked RAM cell of the starting state reads 0, ROM shadow below 4 MiB included. It follows from `image` and `seeds` and the
    inits/teardowns claim that the `Init` tokens of checked top bits are the zero boot image of their windows
    (`InitsTeardowns.Claims.bootImage`). Residual items, not derived from a circuit: the register seeds (the chunk's
    public state, zero for the first chunk), RAM coverage (only the cells of initialised windows are tracked, so only
    they are reachable) and cross-chunk clock chaining (no other circuit writes at timestamp 0). -/
def BootRamZeroClaim : Prop :=
  ∀ {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)} {projection : RV.Instr → Option (DecoderData PooledFamily)} (_inputs : RVPooledBootInputs trace initial cells program inits projection),
    ∀ address, Cell.ram address ∈ cells → (Cell.ram address).readRV initial = some 0

namespace NonDeterminism.Pooled

/-- A run of our spec as in `RVRealizes` that consumed exactly the trace's `readCount` words of the input stream. -/
def RVRealizes {p : Nat} [Fact p.Prime] (trace : PooledTrace p) (initial : RV.State) (cells : List Cell) : Prop :=
  ∃ n after, RV.run n initial = some after ∧ after.input = initial.input.drop (readCount trace) ∧
    after.pc = trace.terminal.word.toBitVec ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.readRV after = some sink.word.toBitVec

/-- The six families plus the CSR 0x7C0 read/write forms (`rvDecoderFields`). The input stream is `initial.input`:
    a read row writes an unconstrained value to `rd` in the circuit, and `ports` binds the read rows' values to the
    stream in clock order (`StreamPorts`); the run consumes exactly the trace's reads. -/
def RVNativeSoundnessClaim : Prop :=
  ∀ {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)} (_inputs : RVPooledBootInputs trace initial cells program inits rvDecoderFields) (_accepted : Accepted trace) (_decoded : RVPooledDecoded trace program) (_ports : StreamPorts trace initial.input),
    RVRealizes trace initial cells

end NonDeterminism.Pooled

end Airbender.Trace
