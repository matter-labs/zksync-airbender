module
public import Proven.KeccakSplit.Setup.Common
public import Human.Helpers.Core.Word
public import Human.Helpers.Context.Timestamps
public import Proven.NonVacuous.HonestAttr
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-! The inputs of one honest split-Keccak worker row (any of the three workers), and the call schedule's memory
    keys. A row reads one word at each port (x10, x11, then the low and high word of each lane, in port order) with
    the previous low clock of that word, at invocation clock `invocation`, as call `call` of the schedule. Memory is
    keyed by small naturals: 0 is x10, 1 is x11 and `2 + 2 s + h` the half `h` of state slot `s`; `lastTouch k key`
    is the last call before `k` that accessed `key`. -/

namespace Airbender.NonVacuous.KeccakSplitSpan
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

/-- The inputs of one row: its call index, the word read at each port, the previous low clock of each port's word
    and the invocation clock. -/
structure RowInput where
  call : Nat
  read : Nat → Word
  previous : Nat → Nat
  invocation : Nat

namespace RowInput
variable (x : RowInput)

/-- The control word of the call. -/
def control : Nat := controlAt x.call

/-- Limb `m` (low to high, sixteen bits each) of lane `l`, read at ports `2 + 2 l` and `3 + 2 l`. -/
def limb (l m : Nat) : Nat :=
  match m with
  | 0 => (x.read (2 + 2 * l)).lo
  | 1 => (x.read (2 + 2 * l)).hi
  | 2 => (x.read (3 + 2 * l)).lo
  | _ => (x.read (3 + 2 * l)).hi

end RowInput

/-- A sixteen-bit limb is its four nibbles; its low byte is its two low nibbles. -/
theorem nib_limb {v : Nat} (h : v < 65536) :
    v = nib v 0 + 16 * nib v 1 + 256 * nib v 2 + 4096 * nib v 3 ∧ v % 256 = nib v 0 + 16 * nib v 1 ∧
      nib v 3 = v / 4096 := by
  simp only [nib, Nat.reducePow]
  omega

/-- The key of port `j` of call `k`: x10, x11, then both halves of each lane's slot. -/
def portKey (k j : Nat) : Nat :=
  if j = 0 then 0 else if j = 1 then 1 else 2 + 2 * slotNat k ((j - 2) / 2) + (j - 2) % 2

/-- The number of ports of call `k`'s worker. -/
def portCount (k : Nat) : Nat := 2 + 2 * Call.slotCount (kindAt k)

/-- The ranges every honest row needs: a call of the schedule, an aligned canonical pointer read at x11, canonical
    words at every port, and an invocation clock that is 1 mod 4 with room for the writes. -/
structure RowInput.Valid (x : RowInput) : Prop where
  call : x.call < 361
  pointer : (x.read 1).Bounded ∧ (x.read 1).lo % 256 = 0
  words : ∀ j < portCount x.call, (x.read j).Bounded
  invocation : x.invocation % 4 = 1
  room : x.invocation + 2 < Trace.timestampBase

/-- Every limb of a lane the row accesses is sixteen bits. -/
theorem RowInput.Valid.limb {x : RowInput} (valid : x.Valid) {l : Nat} (lane : l < Call.slotCount (kindAt x.call))
    (m : Nat) : x.limb l m < 65536 := by
  have low := valid.words (2 + 2 * l) (by unfold portCount; omega)
  have high := valid.words (3 + 2 * l) (by unfold portCount; omega)
  simp only [Word.Bounded, limbBase] at low high
  unfold RowInput.limb
  split <;> omega

/-- The keys call `k` accesses, in port order. -/
def portKeys (k : Nat) : List Nat := (List.range (portCount k)).map (portKey k)

/-- The last call before `k` that accessed `key`. -/
def lastTouch : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, key => if key ∈ portKeys k then some k else lastTouch k key

/-- The write clock of a call (invocation `1 + 4 j`, write offset two), zero for the seed. -/
def clockOf : Option Nat → Nat
  | none => 0
  | some j => 3 + 4 * j

end Airbender.NonVacuous.KeccakSplitSpan
