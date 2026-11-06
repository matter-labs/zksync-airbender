import Human.Helpers.Delegation.Decoder

-- The statements proven in slop/Slop/Final/Circuits/AddSub/CallerTheorems.lean (checked by verify.sh).

namespace Airbender.Delegation.Caller

/-- Public instruction bytes and modeled decoder membership identify the
    request's family. Imported equations then prove its virtual CSR read/write
    tokens, real x0 addresses and state-preserving Sail register effects. Native
    source-value equality and fulfillment matching are separate; this theorem
    does not assume a selected opcode, expected request or expected output. -/
def SoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 65536 < p) {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry} {w : Nat → ZMod p} (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints) (configuration : Reference.RiscV.Sail.Configured before) (image : programImage before addresses = some program) (member : (decoderTable program).Contains #[] (nativeQuery w)),
    Binding w before program

/-- Imported caller PCs match the original Sail preparation/retirement path.
    Public decoding supplies the initial word; imported range queries supply
    the final bounds. The inverse condition names the serialized field constant.
    No per-row PC range or expected next-PC premise is needed. -/
def PcSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry} {w : Nat → ZMod p} (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints) (configuration : Reference.RiscV.Sail.Configured before) (image : programImage before addresses = some program) (member : (decoderTable program).Contains #[] (nativeQuery w)),
    PCBinding w before program

end Airbender.Delegation.Caller
