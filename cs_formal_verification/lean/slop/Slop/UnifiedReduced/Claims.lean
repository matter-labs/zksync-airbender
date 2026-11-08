import Slop.UnifiedReduced.Delegation
import Slop.UnifiedReduced.ComparisonSoundness
import Slop.UnifiedReduced.Trace
import Slop.UnifiedReduced.Values
import Human.Circuits.JumpBranchSlt.Jump
import Human.Circuits.UnifiedReduced.Binary
import Human.Circuits.WordMemory.Output
import Human.Trace.UnifiedReduced.PreparedRoundWindows
import Slop.AddSub
import Slop.Arithmetic.ShiftAssembly
import Slop.Arithmetic.SignExtend
import Slop.Arithmetic.WordBytes
import Slop.Arithmetic.WordRotation
import Slop.Blake2G.CallGroups
import Slop.Blake2G.PhysicalWords
import Slop.Delegation.NativeSegments
import Slop.Delegation.RequestWindows
import Slop.Delegation.SharedOperations
import Slop.Delegation.WorkerProjection
import Slop.JumpBranchSlt.Branch
import Slop.JumpBranchSlt.Jump
import Slop.Keccak.CallPermutation
import Slop.Trace.BytePorts
import Slop.Trace.CompositionCore
import Slop.Trace.ROMView
import Slop.Trace.WindowCounts
import Slop.UnifiedReduced.Binary
import Slop.UnifiedReduced.WordROM
import Human.Circuits.Bigint.PointerABI
import Slop.Bigint.Addresses

namespace Airbender.UnifiedReduced


open Airbender.Reference.RiscV


theorem native_clocks {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (boundary : Trace.ClockBoundary trace) :
    ∀ row ∈ trace.rows, Trace.ClockEffects row.columns row.assignment :=
  Trace.Proofs.trace_clocks hp inverse accepted boundary


end Airbender.UnifiedReduced
