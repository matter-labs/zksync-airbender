import Human.ISA.Sail.WholeRun

namespace Airbender.Trace.Machine

/-- The full unsigned production machine executes the whole accepted trace, including standard and split workers.
    Public premises bind ROM bytes, register seeds, all initialization instances, their checked top bits,
    the typed full statement verifier boundary, and the ROM tables. Worker tables are an explicit setup interface.
    Native acceptance supplies imported constraints and logical decoder, state, request and memory matching.
    Response ports bind the independent input stream. Special5 and `mop.r.N` are excluded. Delegation validity is not a premise. -/
def UnrolledFullUnsignedSailClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    BootInputs .unrolledFullUnsigned trace initial cells program InitsTeardowns.importedLayout inits →
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) →
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) →
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows →
    NoSpecial5 program → NoMopR program →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    UnrolledAcceptance trace workers program → SailRealizes trace initial cells

/-- The reduced production machine executes the whole accepted trace with modular operations and round calls.
    Public premises bind ROM bytes, zero register seeds, all initialization instances, checked top bits,
    the typed full statement verifier boundary and ROM tables. Worker setup is explicit.
    The production program projection restricts the CPU and delegation families.
    Native acceptance supplies constraints and logical decoder, state, request and memory matching.
    Response ports bind the independent input stream. Delegation validity is not a premise. -/
def UnrolledReducedSailClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)),
    BootInputs .unrolledReduced trace initial cells program InitsTeardowns.importedLayout inits →
    trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) →
    trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial) →
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows →
    NonDeterminism.Pooled.StreamPorts trace initial.input →
    UnrolledAcceptance trace workers program → SailRealizes trace initial cells

/-- The unified production machine executes the whole accepted trace with modular and delegation operations.
    Public premises bind ROM bytes, register seeds, all trailing initialization instances and their checked top bits,
    the typed full statement verifier boundary and the unified ROM table. Worker setup is explicit.
    Native acceptance supplies constraints and logical decoder, state, request and memory matching.
    Response ports bind the independent input stream. Special5 is excluded. Delegation validity is not a premise. The initialized inline windows lie below `2 ^ 31`. -/
def UnifiedSailClaim : Prop :=
  ∀ (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (initial : RV.State) (cells : List Cell) (program : List RVMachineProgramEntry)
    (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)),
    BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits →
    trace.rom = UnifiedReduced.Setup.tableRV initial →
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows →
    NoSpecial5 program → UnifiedStreamPorts trace initial.input →
    UnifiedAcceptance trace workers program → SailRealizes trace initial cells


end Airbender.Trace.Machine
