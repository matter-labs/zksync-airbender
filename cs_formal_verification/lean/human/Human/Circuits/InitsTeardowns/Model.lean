import Human.Helpers.Context.Model
import Human.Helpers.Memory.InitsTeardownsColumns

/-! The inits/teardowns circuits: the standalone circuit (`cs/src/gkr_compiler/inits_and_teardowns.rs`)
    and the sets inlined into the unified reduced machine (`inits_and_teardowns_inline.rs`).

    They have no constraints and no lookups. Each set `s` covers one window of RAM: its row `r`
    contributes an `Init` tuple (address, timestamp 0, value 0) to the write side of the RAM
    permutation and a `Teardown` tuple (the same address, the row's teardown timestamp and value
    columns) to its read side. The address is computed from two virtual setup columns and the
    public `top_bits[s]`; nothing in the circuit constrains `top_bits`: the full statement verifier
    checks them (`Human.Circuits.InitsTeardowns.Theorems.TopBitsChecked`). The tuple semantics is
    `gkr_eval_ir/src/lower/memory.rs:311-440` (`lower_inits_or_teardowns`). -/

namespace Airbender.InitsTeardowns
open Trace

/-- Row positions of each set: all `2 ^ traceLog` rows, with no selector or padding. -/
def rows (layout : Layout) : List Nat := List.range (2 ^ layout.traceLog)

/-- Virtual setup `InitsAndTeardownsLow` at row `r`: `(r << WORD_BITS) & 0xFFFF`
    (`prover/src/gkr/virtual_polys/init_and_teardown_base.rs:70-71`). -/
def setupLow (layout : Layout) (row : Nat) : Nat := row * 2 ^ layout.wordBits % 2 ^ 16

/-- Virtual setup `InitsAndTeardownsHigh` at row `r`: `r >> (16 - WORD_BITS)` (same file, 72-73). -/
def setupHigh (layout : Layout) (row : Nat) : Nat := row / 2 ^ (16 - layout.wordBits)

/-- `high_bits_offset = log2(trace_len) + WORD_BITS - 16` (`lower/memory.rs:431-440`). -/
def topShift (layout : Layout) : Nat := layout.traceLog + layout.wordBits - 16

/-- The two address limbs of row `row` of a set whose public top bits are `top`, as field elements:
    low = `InitsAndTeardownsLow`, high = `InitsAndTeardownsHigh + (top << high_bits_offset)`, the
    shift taken in `u32` (`lower/memory.rs:366-389`). -/
def addressLimbs {p : Nat} (layout : Layout) (top row : Nat) : ZMod p × ZMod p :=
  ((setupLow layout row : ZMod p),
    (setupHigh layout row : ZMod p) + (((top <<< topShift layout) % 2 ^ 32 : Nat) : ZMod p))

/-- Address space RAM (`AddressSpaceType::RAM = 1`) and the raw limbs, coded as
    `MemoryAddress.code` codes RAM ports. -/
def addressCode {p : Nat} (layout : Layout) (top row : Nat) : Nat :=
  Nat.pair 1 (Nat.pair (addressLimbs (p := p) layout top row).1.val (addressLimbs (p := p) layout top row).2.val)

/-- The `Init` tuple: no timestamp or value terms, so timestamp `(0, 0)` and value `(0, 0)`
    (`lower/memory.rs:392-420`). -/
def initToken {p : Nat} (layout : Layout) (top row : Nat) : MemoryToken p :=
  ⟨addressCode (p := p) layout top row, (0, 0), Nat.pair 0 0⟩

/-- The `Teardown` tuple of set columns `set` in the row assignment `w`: the row's
    timestamp and value limbs, unconstrained by the circuit. -/
def teardownToken {p : Nat} (layout : Layout) (set : TeardownSet) (top row : Nat) (w : Nat → ZMod p) :
    MemoryToken p :=
  ⟨addressCode (p := p) layout top row, rawPair w set.timestamp, pairCode w set.value⟩

/-- One instance of the circuit: its public top bits and its witness by row position. -/
structure Witness (p : Nat) (layout : Layout) where
  /-- Public `inits_and_teardowns_top_bits`, one per set. -/
  topBits : Vector Nat layout.sets.size
  /-- Row position, then variable ID, to field value. -/
  assignment : Nat → Nat → ZMod p

/-- Init tuples of sets with top bits `topBits`, set by set, row by row. -/
def initTokens {p : Nat} (layout : Layout) (topBits : List Nat) : List (MemoryToken p) :=
  topBits.flatMap fun top => (rows layout).map (initToken layout top)

/-- Write side of the RAM permutation: the instance's init tuples. -/
def Witness.initTokens {p : Nat} {layout : Layout} (w : Witness p layout) : List (MemoryToken p) :=
  InitsTeardowns.initTokens layout w.topBits.toList

/-- Read side of the RAM permutation: the instance's teardown tuples, set by set, row by row. -/
def Witness.teardownTokens {p : Nat} {layout : Layout} (w : Witness p layout) : List (MemoryToken p) :=
  (w.topBits.toList.zip layout.sets.toList).flatMap fun (top, set) =>
    (rows layout).map fun row => teardownToken layout set top row (w.assignment row)

end Airbender.InitsTeardowns
