import Airbender.Proofs.Blake2Round.FrameOutputs
import Airbender.Proofs.Blake2Round.ArtifactChecks

namespace Airbender.Blake2Round.Proofs.NativeFinalLayout
set_option warningAsError true
set_option maxRecDepth 16384

/-- Native coordinates for the final XOR phase. Arithmetic consumers use these
    named wires rather than the allocation stride or physical tag position. -/
def flagAssertion : Nat := 2
def muxAssertion (limb : Fin 16) : Nat := 108 + limb.val

def queryIndex (limb : Fin 16) (stage : Fin 4) : Nat :=
  130 + 4 * limb.val + stage.val

def query {p : Nat} [Fact p.Prime] (limb : Fin 16) (stage : Fin 4) : Lookup (ZMod p) :=
  (FlatOperation.lookups (importedConstraints setupTable)).get
    ⟨queryIndex limb stage, by
      rw [lookup_count]; have := limb.isLt; have := stage.isLt; dsimp [queryIndex]; omega⟩

def queryColumn {p : Nat} [Fact p.Prime] (w : Nat → ZMod p)
    (limb : Fin 16) (stage : Fin 4) (column : Fin 6) : ZMod p :=
  ((query limb stage).entry.toArray[column.val]!).eval (Verification.environment w)

def temporary {p : Nat} (w : Nat → ZMod p) (limb : Fin 16) (part : Fin 6) : ZMod p :=
  w (536 + 6 * limb.val + part.val)

def initial {p : Nat} (w : Nat → ZMod p) (limb : Fin 16) : ZMod p :=
  w (154 + 4 * (limb.val / 2) + 2 * (limb.val % 2))
def firstInput {p : Nat} (w : Nat → ZMod p) (limb : Fin 16) : ZMod p :=
  w (39 + 4 * (limb.val / 2) + limb.val % 2)
def secondInput {p : Nat} (w : Nat → ZMod p) (limb : Fin 16) : ZMod p :=
  w (71 + 4 * (limb.val / 2) + limb.val % 2)
def stateRead {p : Nat} (w : Nat → ZMod p) (limb : Fin 16) : ZMod p :=
  w (5 + 4 * (limb.val / 2) + limb.val % 2)
def stateWrite {p : Nat} (w : Nat → ZMod p) (limb : Fin 16) : ZMod p :=
  w (7 + 4 * (limb.val / 2) + limb.val % 2)

def lowC {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  (diagonalFrame (Fin.ofNat 4 (limb.val / 2 + 2)) w).secondCLow[(⟨limb.val % 2, by omega⟩ : Fin 2)]
def lowA {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  (diagonalFrame (Fin.ofNat 4 (limb.val / 2)) w).secondABytes[(⟨limb.val % 2, by omega⟩ : Fin 2)] -
    128 * temporary w (limb.castLE (by decide)) 3

def lowB {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  (diagonalFrame (Fin.ofNat 4 (limb.val / 2 + 3)) w).secondBChunks[
    (⟨1 + 2 * (limb.val % 2), by omega⟩ : Fin 4)]
def lowD {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  (diagonalFrame (Fin.ofNat 4 (limb.val / 2 + 1)) w).secondDBytes[
    (⟨1 + 2 * (limb.val % 2), by omega⟩ : Fin 4)]

end Airbender.Blake2Round.Proofs.NativeFinalLayout
