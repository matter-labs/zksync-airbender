module
public import Human.Helpers.Context.Timestamps
public import Human.Helpers.Core.Field
public import Slop.KernelRfl
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/- An initialized split pool executes in Sail and every row is a call of the
   schedule, given the per-row circuit contract. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true

theorem babyBear_clock : 2 * timestampBase + 4 < babyBearModulus := by
  norm_num [timestampBase, babyBearModulus]

end Airbender.Keccak.Split.Native.Proofs
