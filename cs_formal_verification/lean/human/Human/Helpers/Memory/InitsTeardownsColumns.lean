module

@[expose] public section
namespace Airbender.InitsTeardowns

/-- One inits/teardowns set's teardown columns (logical variable IDs, low limb first),
    resolved from `memory_layout.teardown_sets` (Rust: `(timestamps, values)` per set). -/
structure TeardownSet where
  /-- Variable IDs of the teardown value limbs. -/
  value : Vector Nat 2
  /-- Variable IDs of the teardown timestamp limbs. -/
  timestamp : Vector Nat 2
  deriving DecidableEq, Repr

/-- Placement-resolved inits/teardowns metadata of an artifact. Set `s` uses public
    `top_bits[s]` and columns `sets[s]`: the importer checks that each layer-0
    `InitsOrTeardownsInitialPair` gate pairs sets `2k, 2k+1` in this order. -/
structure Layout where
  /-- `log2 trace_len`; every row position `r < 2 ^ traceLog` of each set is used. -/
  traceLog : Nat
  /-- `inits_and_teardowns_word_bits`: each row covers `2 ^ wordBits` bytes. -/
  wordBits : Nat
  /-- The sets, in set-index order. -/
  sets : Array TeardownSet
  deriving DecidableEq, Repr

end Airbender.InitsTeardowns
