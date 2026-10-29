import Airbender.Proofs.Reduced.NativePrefix

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open Delegation.Caller
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- Canonical native PC and clock limbs encode one typed verifier endpoint. -/
theorem endpoint_of_bounds [Fact p.Prime] {point : PCState.State p}
    (pc : point.word.Bounded) (clock : (timeOfPair point.timestamp).Bounded) :
    ∃ endpoint : VerifierBoundary.Endpoint, endpoint.encode = point := by
  have word : Word.ofBitVec point.word.toBitVec = point.word :=
    Word.eq_of_value (Word.ofBitVec_bound _) pc (by
      rw [Word.ofBitVec_value, Word.toBitVec_toNat pc])
  have encodedPC : PCState.encode point.word.toBitVec = point.pc := by
    apply Prod.ext
    · have low := congrArg (fun value : Word => (value.lo : ZMod p)) word
      simpa only [PCState.encode, Word.ofBitVec, PCState.State.word,
        ZMod.natCast_zmod_val] using low
    · have high := congrArg (fun value : Word => (value.hi : ZMod p)) word
      simpa only [PCState.encode, Word.ofBitVec, PCState.State.word,
        ZMod.natCast_zmod_val] using high
  have lowBound : point.timestamp.1.val < 2 ^ 32 := by
    have low := clock.1
    change point.timestamp.1.val < timestampBase at low
    dsimp [timestampBase] at low
    omega
  have highBound : point.timestamp.2.val < 2 ^ 32 := by
    have high := clock.2
    change point.timestamp.2.val < timestampBase at high
    dsimp [timestampBase] at high
    omega
  refine ⟨⟨point.word.toBitVec,
    (BitVec.ofNat 32 point.timestamp.1.val, BitVec.ofNat 32 point.timestamp.2.val)⟩, ?_⟩
  change PCState.State.mk (PCState.encode point.word.toBitVec)
    (((BitVec.ofNat 32 point.timestamp.1.val).toNat : ZMod p),
      ((BitVec.ofNat 32 point.timestamp.2.val).toNat : ZMod p)) = point
  rw [encodedPC, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt lowBound, Nat.mod_eq_of_lt highBound,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- The actual cut endpoint closes the prefix verifier boundary. -/
theorem supported_prefix_boot [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial : State} {cells : List Cell} {ca : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program)
    (inputs : RequestInputs data initial ca)
    (boot : PooledBootInputs data.machine initial cells program Caller.reducedDecoderFields)
    {next : Trace.Row babyBearModulus PooledFamily} (member : next ∈ data.machine.rows)
    {memory : List (MemoryToken babyBearModulus)}
    (prefixAccepted : MixedMemoryAccepted (supportedPrefix data next.start memory) program) :
    PooledBootInputs (supportedPrefix data next.start memory).machine initial cells program
      Caller.reducedDecoderFields := by
  have pc := (native_pc_bounds (by decide) accepted boot.verifierBoundary next member).1
  have clock := (state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned next member).1
  obtain ⟨terminal, encoded⟩ := endpoint_of_bounds pc clock
  refine { boot with verifierBoundary := ?_ }
  refine ⟨terminal, VerifierBoundary.Proofs.binding_of_endpoints ?_ encoded.symm prefixAccepted.states⟩
  exact boot.initialBoundary

end Airbender.AddSub.Modular.External.Caller.Proofs
