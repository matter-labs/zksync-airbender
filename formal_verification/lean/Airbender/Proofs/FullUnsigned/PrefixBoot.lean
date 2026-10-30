import Airbender.Proofs.FullUnsigned.PrefixAcceptance
import Airbender.Proofs.Reduced.PrefixBoundary

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The actual native cut supplies a canonical verifier endpoint for the full
prefix. Public initialization, code and ROM bindings keep their original meaning. -/
theorem unrolled_full_prefix_boot
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus} {cells : List Cell}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (boot : PooledBootInputs trace initial cells
      (NativeDecoder.ProgramRows.programOf .fullUnsigned initial text) AddSub.Modular.External.decoderFields)
    {next : Trace.Row babyBearModulus PooledFamily} (member : next ∈ trace.rows)
    {memory : List (MemoryToken babyBearModulus)}
    (prefixAccepted : UnrolledAcceptance (unrolledFullPrefixTrace trace next.start memory)
      (unrolledFullPrefixWorkers workers next.start) (unrolledFullPrefixSplitWorkers splitWorkers next.start).steps
      ((unrolledFullPrefixSplitWorkers splitWorkers next.start).rows.map
        (Keccak.Split.Native.Row.fulfillment splitWorkers.cached))) :
    PooledBootInputs (unrolledFullPrefixTrace trace next.start memory) initial cells
      (NativeDecoder.ProgramRows.programOf .fullUnsigned initial text) AddSub.Modular.External.decoderFields := by
  have initialPC : trace.initial.word.lo < limbBase := by
    rw [boot.initialBoundary]
    change 0 < limbBase
    decide
  have pc := (unrolled_full_pc_bounds setup lookup accepted excluded initialPC boot.verifierBoundary next member).1
  have clocks := ROMView.native_clocks (by decide) boot.seed boot.initialBoundary
  have clock := (state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states clocks.initial clocks.aligned next member).1
  obtain ⟨terminal, encoded⟩ := AddSub.Modular.External.Caller.Proofs.endpoint_of_bounds pc clock
  refine {boot with verifierBoundary := ?_}
  refine ⟨terminal, VerifierBoundary.Proofs.binding_of_endpoints ?_ encoded.symm prefixAccepted.states⟩
  exact boot.initialBoundary

end Airbender.Compiler.MachineTargets.Proofs
