import Human.Helpers.Delegation.RVDecoder

-- The statements proven in slop/Slop/Final/Circuits/AddSub/RVCallerTheorems.lean (checked by verify.sh). RV siblings
-- of `CallerTheorems.lean`: the public caller table is built from an `RV.State` (`rvProgramImage`, `RV.decode`); no
-- `Configured`.

namespace Airbender.Delegation.Caller

/-- RV sibling of `SoundnessClaim`: public ROM bytes, `RV.decode` and modeled decoder membership identify the request's
    family and its delegation call `.delegate k` (`RV.step` at that PC is `RV.exec s (.delegate k)`). Imported equations
    then prove its virtual CSR read/write tokens, real x0 addresses and state-preserving RV x0 effects. No selected
    opcode, expected request or expected output is assumed. -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 65536 < p) {before : RV.State} {addresses : List (BitVec 32)} {program : List RVProgramEntry} {w : Nat → ZMod p} (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints) (image : rvProgramImage before addresses = some program) (member : (rvDecoderTable program).Contains #[] (nativeQuery w)),
    RVBinding w before program

/-- RV sibling of `PcSoundnessClaim`: imported caller PCs match the RV retirement path. Public decoding supplies the
    initial word; imported range queries supply the final bounds. The inverse condition names the serialized field
    constant. No per-row PC range or expected next-PC premise is needed. -/
def RVPcSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) {before : RV.State} {addresses : List (BitVec 32)} {program : List RVProgramEntry} {w : Nat → ZMod p} (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints) (image : rvProgramImage before addresses = some program) (member : (rvDecoderTable program).Contains #[] (nativeQuery w)),
    RVPCBinding w before program

end Airbender.Delegation.Caller
