import Human.Circuits.InitsTeardowns.Model
import Human.Circuits.InitsTeardowns.Artifact
import Human.Circuits.InitsTeardowns.UnifiedArtifact
import Human.Helpers.Memory.Native
import Human.Helpers.Core.Field

/-! Claims about the inits/teardowns sets: the init tuples are the zero-valued, zero-timestamp boot
    image of the RAM windows named by the public top bits (ROM shadow below 4 MiB included), and each
    teardown tuple carries its row's final timestamp and value at the same address. State-free.
    Proven in slop/Slop/Final/Circuits/InitsTeardowns/Theorems.lean. -/

namespace Airbender.InitsTeardowns
open Trace Arithmetic

/-- Bound the full statement verifier puts on each public top-bits value: `TOP_BITS_UPPER_BOUND = 64`
    for the standalone circuits (`full_statement_verifier/src/unrolled_circuit_params.rs:100-111`) and
    `MAX_TOP_BIT = 1 << 6` for the unified circuit (`unified_circuit_statement.rs:114-115`). -/
def maxTopBit : Nat := 64

/-- The full statement verifier's check of the public top bits of all instances that carry
    inits/teardowns, concatenated in instance order: strictly increasing and below `maxTopBit`
    (`unrolled_proof_statement.rs:158-166`, `unified_circuit_statement.rs:164-175`). The circuits do
    not constrain the top bits. -/
def TopBitsChecked (topBits : List Nat) : Prop :=
  topBits.Pairwise (· < ·) ∧ ∀ top ∈ topBits, top < maxTopBit

/-- Byte address of row `row` in the window of `top`: windows of `2 ^ (traceLog + wordBits)` bytes,
    one `2 ^ wordBits`-byte word per row. -/
def windowAddress (layout : Layout) (top row : Nat) : Nat :=
  top * 2 ^ (layout.traceLog + layout.wordBits) + row * 2 ^ layout.wordBits

/-- The RAM cells of the windows of `topBits`, window by window, row by row. -/
def windowCells (layout : Layout) (topBits : List Nat) : List Cell :=
  topBits.flatMap fun top => (rows layout).map fun row => .ram (BitVec.ofNat 32 (windowAddress layout top row))

/-- The claims for the sets of one artifact, over BabyBear. -/
structure Claims (layout : Layout) : Prop where
  /-- Each init tuple is the zero-timestamp, zero-value token of an aligned RAM cell at its window
      address, which is below `2 ^ 32` (not truncated). -/
  init : ∀ top < maxTopBit, ∀ row < 2 ^ layout.traceLog,
    windowAddress layout top row < 2 ^ 32 ∧
    (Cell.ram (BitVec.ofNat 32 (windowAddress layout top row))).Aligned ∧
    initToken (p := babyBearModulus) layout top row =
      (Cell.ram (BitVec.ofNat 32 (windowAddress layout top row))).initialToken 0 ∧
    (initToken (p := babyBearModulus) layout top row).time = (0, 0) ∧
    (initToken (p := babyBearModulus) layout top row).word = ⟨0, 0⟩
  /-- Under the verifier's check, the init tuples of all instances are the native boot image of
      their window cells, and those cells are distinct. -/
  bootImage : ∀ instances : List (Witness babyBearModulus layout),
    TopBitsChecked (instances.flatMap fun w => w.topBits.toList) →
    (windowCells layout (instances.flatMap fun w => w.topBits.toList)).Nodup ∧
    instances.flatMap Witness.initTokens =
      ROMView.nativeBootImage (windowCells layout (instances.flatMap fun w => w.topBits.toList))
  /-- One teardown tuple per init tuple, at the same address, carrying the row's teardown timestamp
      and value columns. -/
  teardown : ∀ w : Witness babyBearModulus layout,
    w.teardownTokens.map MemoryToken.address = w.initTokens.map MemoryToken.address ∧
    ∀ s (hs : s < layout.sets.size), ∀ row < 2 ^ layout.traceLog,
      teardownToken layout layout.sets[s] w.topBits[s] row (w.assignment row) ∈ w.teardownTokens ∧
      (w.topBits[s] < maxTopBit →
        teardownToken layout layout.sets[s] w.topBits[s] row (w.assignment row) =
          ⟨(Cell.ram (BitVec.ofNat 32 (windowAddress layout w.topBits[s] row))).addressCode,
            rawPair (w.assignment row) layout.sets[s].timestamp,
            pairCode (w.assignment row) layout.sets[s].value⟩)
  /-- The verifier's check can be met: top bits `0, …, 63`. -/
  checkable : TopBitsChecked (List.range maxTopBit)

/-- The standalone circuit (eight sets of `2 ^ 24` rows, windows of `2 ^ 26` bytes): the claims, and
    the windows of top bits `0, …, 63` cover every aligned RAM word. -/
def StandaloneClaim : Prop :=
  Claims importedLayout ∧
    ∀ address : BitVec 32, (Cell.ram address).Aligned →
      Cell.ram address ∈ windowCells importedLayout (List.range maxTopBit)

/-- The unified reduced machine's inline sets (two sets of `2 ^ 23` rows, windows of `2 ^ 25` bytes):
    the claims, and the windows of top bits `0, …, 63` cover every aligned RAM word below `2 ^ 31`
    (the verifier's bound 64 is that of the standalone circuit's `2 ^ 26`-byte windows). -/
def UnifiedClaim : Prop :=
  Claims unifiedLayout ∧
    ∀ address : BitVec 32, (Cell.ram address).Aligned → address.toNat < 2 ^ 31 →
      Cell.ram address ∈ windowCells unifiedLayout (List.range maxTopBit)

end Airbender.InitsTeardowns
