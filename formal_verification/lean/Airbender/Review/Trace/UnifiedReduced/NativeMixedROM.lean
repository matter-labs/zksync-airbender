import Airbender.Proofs.UnifiedReduced.MixedNativeROM

namespace Airbender.UnifiedReduced.Caller.NativeROM
open Trace Reference.RiscV.Sail

/-- Native mixed acceptance survives public-ROM interpretation when the explicit
    F04 RAM-port contract binds every worker. Caller requests, multiplicity and
    the imported worker assignments are preserved; no new acceptance is assumed. -/
theorem acceptance_soundness [Fact p.Prime] (hp : 131072 < p) (initial : State)
    {native : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    (accepted : MixedMemoryAccepted native program)
    (ram : ExternalBoundary.WorkerRAM.Binding native.workers.rows) :
    MixedMemoryAccepted (view initial native) program :=
  Proofs.accepted hp initial accepted ram

/-- Public native boot data derives the physical shared initialization and
    program inputs. The original row reads and all worker outputs remain absent
    from this interface; the F04 restriction is separate from boot data. -/
theorem initialization_soundness [Fact p.Prime] (hp : 4 < p)
    {native : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell} (boot : Inputs native program initial cells) :
    ∃ ca oa, MixedMemoryInputs (view initial native) program initial ca oa cells :=
  Proofs.inputs hp boot

/-- One initialized Sail history realizes native ordinary/caller/worker ports,
    operation references and terminal public cells after ROM interpretation.
    This completes conditional mixed-memory transport, while F04 enforcement and
    full custom-CSR retirement remain separate obligations. -/
theorem memory_soundness
    {native : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell}
    (accepted : MixedMemoryAccepted native program) (boot : Inputs native program initial cells)
    (ram : ExternalBoundary.WorkerRAM.Binding native.workers.rows) :
    MixedMemoryEffects (view initial native) initial cells :=
  Proofs.memory_soundness accepted boot ram

/-- The existing physical tracked-RAM scope derives the worker restriction from
    initialized matching. Arbitrary native zero-shadow acceptance still needs
    the separate F04 binding; this does not assume a port's desired read. -/
theorem ram_binding_soundness
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell} {ca oa : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program)
    (physical : MixedMemoryInputs data program initial ca oa cells)
    (domain : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat) :
    ExternalBoundary.WorkerRAM.Binding data.workers.rows :=
  Proofs.ram_binding_of_inputs accepted physical domain

end Airbender.UnifiedReduced.Caller.NativeROM
