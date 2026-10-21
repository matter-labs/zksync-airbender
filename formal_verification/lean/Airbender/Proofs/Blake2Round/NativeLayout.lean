import Airbender.Proofs.Blake2G.Frame
import Airbender.Proofs.Blake2Round.ArtifactChecks

namespace Airbender.Blake2Round.Proofs.NativeLayout
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

inductive Phase where
  | column
  | diagonal
  deriving DecidableEq

/-- The native coordinate system is confined to this adapter. Input locations
    refer to semantic lanes supplied by the preceding phase. -/
inductive Location where
  | witness (column : Nat)
  | query (slot : Fin 16) (column : Fin 6)
  | input (limb : Fin 8)

structure Layout where
  inputs : Vector Location 12
  addCarries : Vector Location 4
  cCarries : Vector Location 4
  firstABytes : Vector Location 2
  dBytes : Vector Location 2
  firstDBytes : Vector Location 4
  bLow : Vector Location 2
  bMiddle : Vector Location 2
  cLow : Vector Location 2
  cMiddle : Vector Location 2
  firstBMiddle : Vector Location 2
  packedB : Vector Location 2
  secondABytes : Vector Location 2
  secondDBytes : Vector Location 4
  secondCLow : Vector Location 2
  secondBChunks : Vector Location 4

def queryIndex (phase : Phase) (call : Fin 4) (slot : Fin 16) : Nat :=
  (match phase with | .column => 2 | .diagonal => 66) + 16 * call.val + slot.val

def queryColumn {p : Nat} [Fact p.Prime] (phase : Phase) (call : Fin 4)
    (slot : Fin 16) (column : Fin 6) (w : Nat → ZMod p) : ZMod p :=
  let query := (FlatOperation.lookups (importedConstraints setupTable)).get
    ⟨queryIndex phase call slot, by
      rw [lookup_count]; have := call.isLt; have := slot.isLt
      cases phase <;> dsimp [queryIndex] <;> omega⟩
  (query.entry.toArray[column.val]!).eval (Verification.environment w)

def Location.read {p : Nat} (query : Fin 16 → Fin 6 → ZMod p)
    (incoming : Vector (ZMod p) 8) (w : Nat → ZMod p) : Location → ZMod p
  | .witness column => w column
  | .query slot column => query slot column
  | .input limb => incoming[limb]

def Layout.read {p : Nat} (layout : Layout) (query : Fin 16 → Fin 6 → ZMod p)
    (incoming : Vector (ZMod p) 8) (w : Nat → ZMod p) : Blake2G.Proofs.Frame p where
  inputs := layout.inputs.map (Location.read query incoming w)
  addCarries := layout.addCarries.map (Location.read query incoming w)
  cCarries := layout.cCarries.map (Location.read query incoming w)
  firstABytes := layout.firstABytes.map (Location.read query incoming w)
  dBytes := layout.dBytes.map (Location.read query incoming w)
  firstDBytes := layout.firstDBytes.map (Location.read query incoming w)
  bLow := layout.bLow.map (Location.read query incoming w)
  bMiddle := layout.bMiddle.map (Location.read query incoming w)
  cLow := layout.cLow.map (Location.read query incoming w)
  cMiddle := layout.cMiddle.map (Location.read query incoming w)
  firstBMiddle := layout.firstBMiddle.map (Location.read query incoming w)
  packedB := layout.packedB.map (Location.read query incoming w)
  secondABytes := layout.secondABytes.map (Location.read query incoming w)
  secondDBytes := layout.secondDBytes.map (Location.read query incoming w)
  secondCLow := layout.secondCLow.map (Location.read query incoming w)
  secondBChunks := layout.secondBChunks.map (Location.read query incoming w)

def columnInputs (call : Fin 4) : Vector Nat 8 :=
  #v[155 + 4 * call.val, 157 + 4 * call.val,
     171 + 4 * call.val, 173 + 4 * call.val,
     186 + 2 * call.val, 187 + 2 * call.val,
     #v[198, 194, 200, 196][call], #v[199, 195, 201, 197][call]]

def column (call : Fin 4) : Layout :=
  let b := 256 + 40 * call.val
  {
    inputs := #v[.input 0, .input 1, .input 2, .input 3, .input 4, .input 5, .input 6, .input 7, .witness (224 + 4 * call.val), .witness (225 + 4 * call.val), .witness (226 + 4 * call.val), .witness (227 + 4 * call.val)]
    addCarries := #v[.witness (b + 1), .witness (b + 3), .witness (b + 25), .witness (b + 27)]
    cCarries := #v[.witness (b + 12), .witness (b + 15), .witness (b + 33), .witness (b + 35)]
    firstABytes := #v[.witness b, .witness (b + 2)]
    dBytes := #v[.witness (b + 4), .witness (b + 5)]
    firstDBytes := #v[.witness (b + 6), .witness (b + 7), .witness (b + 8), .witness (b + 9)]
    bLow := #v[.witness (b + 16), .witness (b + 18)]
    bMiddle := #v[.witness (b + 17), .witness (b + 19)]
    cLow := #v[.witness (b + 10), .witness (b + 13)]
    cMiddle := #v[.witness (b + 11), .witness (b + 14)]
    firstBMiddle := #v[.witness (b + 20), .witness (b + 21)]
    packedB := #v[.witness (b + 22), .witness (b + 23)]
    secondABytes := #v[.witness (b + 24), .witness (b + 26)]
    secondDBytes := #v[.witness (b + 30), .witness (b + 28), .witness (b + 31), .witness (b + 29)]
    secondCLow := #v[.witness (b + 32), .witness (b + 34)]
    secondBChunks := #v[.witness (b + 38), .witness (b + 36), .witness (b + 39), .witness (b + 37)]
  }

def diagonal (call : Fin 4) : Layout :=
  let b := 416 + 30 * call.val
  {
    inputs := #v[.input 0, .input 1, .input 2, .input 3, .input 4, .input 5, .input 6, .input 7, .witness (240 + 4 * call.val), .witness (241 + 4 * call.val), .witness (242 + 4 * call.val), .witness (243 + 4 * call.val)]
    addCarries := #v[.witness (b + 1), .witness (b + 3), .query 10 2, .query 11 2]
    cCarries := #v[.witness (b + 10), .witness (b + 13), .query 14 2, .query 15 2]
    firstABytes := #v[.witness b, .witness (b + 2)]
    dBytes := #v[.query 0 0, .query 2 0]
    firstDBytes := #v[.witness (b + 4), .witness (b + 5), .witness (b + 6), .witness (b + 7)]
    bLow := #v[.witness (b + 14), .witness (b + 16)]
    bMiddle := #v[.witness (b + 15), .witness (b + 17)]
    cLow := #v[.witness (b + 8), .witness (b + 11)]
    cMiddle := #v[.witness (b + 9), .witness (b + 12)]
    firstBMiddle := #v[.witness (b + 18), .witness (b + 19)]
    packedB := #v[.witness (b + 20), .witness (b + 21)]
    secondABytes := #v[.witness (b + 22), .witness (b + 23)]
    secondDBytes := #v[.query 10 3, .witness (b + 24), .query 11 3, .witness (b + 25)]
    secondCLow := #v[.witness (b + 26), .witness (b + 27)]
    secondBChunks := #v[.query 14 3, .witness (b + 28), .query 15 3, .witness (b + 29)]
  }

/-- Projection of the fixed eighteen-query G fragment onto the sixteen native
    queries. Packed rows supply two checked projections. -/
def legacyQuerySources : Vector (Fin 16) 18 :=
  #v[0, 1, 2, 3, 7, 4, 6, 6, 5, 7, 10, 8, 11, 9, 14, 12, 15, 13]

def additionCarryQueries : Vector (Fin 16) 4 := #v[0, 2, 10, 11]
def finalCarryQueries : Vector (Fin 16) 2 := #v[14, 15]

def columnCarryColumns (call : Fin 4) : Vector Nat 4 :=
  #v[257 + 40 * call.val, 259 + 40 * call.val, 281 + 40 * call.val, 283 + 40 * call.val]
def columnBooleanColumns (call : Fin 4) : Vector Nat 4 :=
  #v[268 + 40 * call.val, 271 + 40 * call.val, 289 + 40 * call.val, 291 + 40 * call.val]
def columnBooleanAssertion (call : Fin 4) (slot : Fin 4) : Nat :=
  137 + 4 * call.val + slot.val

def diagonalBooleanAssertion (call : Fin 4) (slot : Fin 2) : Nat :=
  153 + 2 * call.val + slot.val

end Airbender.Blake2Round.Proofs.NativeLayout
