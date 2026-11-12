module
public import Human.Helpers.Delegation.RVDecoder
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

-- The statements proven in proven/Proven/Final/Circuits/AddSub/RVCallerTheorems.lean (checked by verify.sh). The public caller table is built from an `RV.State` (`rvProgramImage`, `RV.decode`).

namespace Airbender.Delegation.Caller

/-- Public ROM bytes, `RV.decode` and modeled decoder membership identify the request's
    family and its delegation call `.delegate k` (`RV.step` at that PC is `RV.exec s (.delegate k)`). Imported equations
    then prove its virtual CSR read/write tokens, real x0 addresses and state-preserving RV x0 effects. No selected
    opcode, expected request or expected output is assumed. -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 65536 < p) {before : RV.State} {addresses : List (BitVec 32)} {program : List RVProgramEntry} {w : Nat → ZMod p} (_constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints) (_image : rvProgramImage before addresses = some program) (_member : (rvDecoderTable program).Contains #[] (nativeQuery w)),
    RVBinding w before program

/-- Imported caller PCs match the RV retirement path. Public decoding supplies the
    initial word; imported range queries supply the final bounds. The inverse condition names the serialized field
    constant. No per-row PC range or expected next-PC premise is needed. -/
def RVPcSoundnessClaim : Prop :=
  ∀ {before : RV.State} {addresses : List (BitVec 32)} {program : List RVProgramEntry} {w : Nat → ZMod babyBearModulus} (_constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints) (_image : rvProgramImage before addresses = some program) (_member : (rvDecoderTable program).Contains #[] (nativeQuery w)),
    RVPCBinding w before program

/-- The assumptions of `RVSoundnessClaim` can be met (at BabyBear) by a selected caller row. -/
def RVSoundnessSatisfiableClaim : Prop :=
  ∃ (before : RV.State) (addresses : List (BitVec 32)) (program : List RVProgramEntry)
    (w : Nat → ZMod babyBearModulus),
    65536 < babyBearModulus ∧
      FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints ∧
      rvProgramImage before addresses = some program ∧ (rvDecoderTable program).Contains #[] (nativeQuery w) ∧
      Requests.Selected w

/-- The assumptions of `RVPcSoundnessClaim` can be met by a selected caller row. -/
def RVPcSoundnessSatisfiableClaim : Prop :=
  ∃ (before : RV.State) (addresses : List (BitVec 32)) (program : List RVProgramEntry)
    (w : Nat → ZMod babyBearModulus),
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints ∧
      rvProgramImage before addresses = some program ∧ (rvDecoderTable program).Contains #[] (nativeQuery w) ∧
      Requests.Selected w

end Airbender.Delegation.Caller
