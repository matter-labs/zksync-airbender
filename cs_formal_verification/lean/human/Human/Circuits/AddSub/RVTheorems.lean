import Human.Circuits.AddSub.Model
import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Delegation.Decoder
import Human.ISA.Sail.View

/-! DRAFT (B2 pilot): the AddSub claims stated against our RV32 spec (`RV.step`, `Human/ISA/RV32.lean`) instead of
Sail. Not proven yet; not in `test/Checks/Claims.lean`. Open items (see the pilot report):
* `InterfaceAssumptions` → `NativeInputs` still carries `configuration : Configured initial`; it is to leave the
  bundle (Configured lives only in `Human/ISA/Sail/Theorems.lean`).
* Under these premises `RVSoundnessClaim` is not provable: nothing places the row's PC in ROM or 4-byte aligned
  (finding G1), and nothing ties the word at that PC in the row's pre-state to the decoded entry (finding G2). -/

namespace Airbender.AddSub
open Reference.RiscV Reference.RiscV.Sail Trace

/-- Every accepted ADD/ADDI/SUB/LUI/AUIPC row is one step of our spec: from the row's pre-state (for any input), the
step exists and gives the row's post-state: `rd` := the row's result (x0: discarded), PC := the row's final PC,
nothing else changed. -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    ∀ input output w, (circuitModel trace initial cells program).relation input output w →
    ∀ stream : List RV.Word, let s := view input.before stream
      ∃ s', RV.step s = some s' ∧
        Same s' ((s.setReg (regNumber input.rd) output.destination.toBitVec).setPC output.pc.toBitVec)

def BabyBearRVSoundnessClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : State) (cells : List Cell) (program : List PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    ∀ input output w, (circuitModel trace initial cells program).relation input output w →
    ∀ stream : List RV.Word, let s := view input.before stream
      ∃ s', RV.step s = some s' ∧
        Same s' ((s.setReg (regNumber input.rd) output.destination.toBitVec).setPC output.pc.toBitVec)

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
