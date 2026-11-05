import Human.Circuits.AddSub.RVModel
import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Delegation.Decoder

/-! RV32 claims (B2 pilot). The AddSub claims (first block) are stated against our spec (`RV.step`, `Human/ISA/RV32.lean`),
    not Sail: the row's pre-state is `input.before : RV.State`, which carries the input stream (`RV.State.input`), so there is
    no stream binder. `RV.Same` (`ISA/State.lean`) compares two `RV.State`s. Proven in
    `slop/Slop/Final/Circuits/AddSub/RVTheorems.lean` (checked in `test/Checks/Claims.lean`).
    Resolved: PC in ROM and 4-byte aligned is the decoder table's guard (`rvProgramEntryWith`); the word at the row's PC is
    the table's encoding (`RVTraceMapping.instruction`).
    The Delegation.Caller claims (second block) are still Sail-typed; they are not part of the AddSub pilot. -/

namespace Airbender.AddSub
open Reference.RiscV Trace

/-- Every accepted ADD/ADDI/SUB/LUI/AUIPC row is one step of our spec: from the row's pre-state (`input.before`), the
    step exists and gives the row's post-state: `rd` := the row's result (x0: discarded), PC := the row's final PC,
    nothing else changed. -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) (trace : PooledTrace p) (initial : RV.State) (cells : List Cell) (program : List PooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

def BabyBearRVSoundnessClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List PooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Airbender.AddSub

namespace Airbender.Delegation.Caller

/-- An accepted delegation caller is a public instruction that our spec decodes as that delegation call
(`csrrw x0, <csr>, x0`), whose CSR is the row's request. (Its effect is the delegation circuits' claim.) -/
def RVDecodeClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 65536 < p) {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry} {w : Nat → ZMod p} (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints) (image : programImage before addresses = some program) (member : (decoderTable program).Contains #[] (nativeQuery w)),
    ∃ entry ∈ program, initialPC w = Arithmetic.Word.ofBitVec entry.pc ∧
      ∃ k, RV.decode entry.bits = some (.delegate k) ∧ k.csr.toNat = Requests.csr entry.data.family ∧
        (Requests.caller w).csr = Requests.csr entry.data.family

/-- The caller's PC moves to the next instruction (`RV.State.nextInstr`, as `RV.State.applyEffect` does). -/
def RVPcSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry} {w : Nat → ZMod p} (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints) (image : programImage before addresses = some program) (member : (decoderTable program).Contains #[] (nativeQuery w)),
    (finalPC w).Bounded ∧ (finalPC w).toBitVec = (initialPC w).toBitVec + 4

end Airbender.Delegation.Caller
