module
public import Tests.TraceExecution
public import Slop.Trace.Claims
public import Slop.SubwordMemory.Claims
public import Slop.Trace.RowContext

@[expose] public section

namespace Tests.PooledROM
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private theorem clearing_row (program : Nat → BitVec 32) :
    Verification.subwordRow program ⟨196609, by decide⟩ = #v[65536, 0, 0, 0, 0, 0, 0, 0, 30] := by
  norm_num [Verification.subwordRow, Verification.subwordDataRow, Verification.subwordStoreContribution]

private theorem rom_row (program : Nat → BitVec 32) :
    Verification.subwordRow program ⟨4849666, by decide⟩ =
      Verification.subwordDataRow 16777216
        (Verification.subwordLoadLimbs true ((program 0).toNat % 65536 + 131072)).1
        (Verification.subwordLoadLimbs true ((program 0).toNat % 65536 + 131072)).2 45 := by
  norm_num [Verification.subwordRow]

end Tests.PooledROM
