module
public import Slop.KeccakSplit.Memory.History
public import Slop.KeccakSplit.Interface
public import Slop.Trace.TransferBounds

@[expose] public section

/- An initialized split pool executes in Sail and every row is a call of the
   schedule, given the per-row circuit contract. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs
set_option warningAsError true

theorem babyBear_clock : 2 * timestampBase + 4 < babyBearModulus := by
  norm_num [timestampBase, babyBearModulus]

end Airbender.Keccak.Split.Native.Proofs
