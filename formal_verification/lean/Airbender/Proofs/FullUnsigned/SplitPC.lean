import Airbender.Proofs.FullUnsigned.SplitSource

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The full caller's public split source and imported PC equations give
canonical PC limbs, a four-byte advance and original Sail retirement. -/
theorem unrolled_full_split_pc_binding
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (families : ∀ worker ∈ workers.rows, FullUnsigned.standardCall worker.family)
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Keccak.Split.Native.Row babyBearModulus)
    (matched : worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment) :
    Keccak.Split.Native.CallerPCBinding row.assignment initial
      (FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text) := by
  let data : Keccak.Split.Native.RequestTrace babyBearModulus :=
    ⟨trace, splitWorkers, FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text⟩
  have checked := unrolled_full_split_request_checks splitWorkers setup lookup accepted excluded initialPC
    families equations active
  have inputs : Keccak.Split.Native.RequestInputs data initial (data.program.map ProgramEntry.pc) :=
    ⟨unrolled_full_split_caller_image setup.image setup.size, initialClock, initialAligned⟩
  have csr := congrArg Delegation.Requests.Request.csr matched
  change worker.kind.csr = (Delegation.Requests.caller row.assignment).csr at csr
  have splitKind : (Keccak.Split.Caller.kindOfCSR (Delegation.Requests.caller row.assignment).csr).isSome = true := by
    rw [← csr, Keccak.Split.Caller.Proofs.kind_of_csr]
    rfl
  have called : row ∈ data.callers := by
    apply List.mem_filter.mpr
    refine ⟨member, ?_⟩
    simp only [family, beq_self_eq_true, selected, decide_true, Bool.true_and, splitKind]
  exact Keccak.Split.Native.Proofs.caller_pc_binding (by decide)
    (by decide +kernel : SerializedInverse.Limb16 babyBearModulus) checked inputs called

end Airbender.Compiler.MachineTargets.Proofs
