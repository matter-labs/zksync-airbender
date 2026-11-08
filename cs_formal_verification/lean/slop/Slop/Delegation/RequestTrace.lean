module
public import Slop.Trace.Pooled
public import Slop.Trace.Slots
public import Human.Helpers.Delegation.WorkerContext
public import Slop.Delegation.Operations
public import Slop.Delegation.PortEvents
public import Human.Helpers.Delegation.Decoder
public import Slop.AddSub.PC
public import Slop.Delegation.CallerRequests

@[expose] public section

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem caller_clock [Fact p.Prime] (hp : timestampBase < p)
    {w : Nat → ZMod p}
    (bound : (decodeTimestamp w AddSub.importedConstraintsTraceColumns.initialTime).Bounded)
    (aligned : (decodeTimestamp w AddSub.importedConstraintsTraceColumns.initialTime).lo % 4 = 0) :
    (timeOfPair (Requests.caller w).time).Bounded ∧ Requests.Live (Requests.caller w) ∧
    (timeOfPair (Requests.caller w).time).lo + 2 < timestampBase := by
  let base := rawPair w AddSub.importedConstraintsTraceColumns.initialTime
  have bounds : (timeOfPair base).Bounded := bound
  have alignment : base.1.val % 4 = 0 := aligned
  have room : base.1.val + 1 < timestampBase := by
    have low := bounds.1
    norm_num [timeOfPair, timestampBase] at low ⊢
    omega
  have clock := Trace.Proofs.write_time_of_room hp bounds room
  have canonical : (base.1 + (1 : ZMod p)).val = base.1.val + 1 := by
    calc
      _ = ((base.1.val + 1 : Nat) : ZMod p).val := by simp only [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
      _ = base.1.val + 1 := ZMod.val_natCast_of_lt (lt_trans room hp)
  have token : (Requests.caller w).time = (base.1 + 1, base.2) := by
    change (base.1 + ((1 : Nat) : ZMod p), base.2) = (base.1 + 1, base.2)
    simp only [Nat.cast_one]
  refine ⟨by simpa only [token, Nat.cast_one] using clock.1, ?_, ?_⟩
  · intro equal
    have low := congrArg (fun pair : ZMod p × ZMod p => pair.1.val) equal
    rw [token] at low
    simp only [canonical, ZMod.val_zero] at low
    omega
  · rw [token]
    change (base.1 + 1).val + 2 < timestampBase
    rw [canonical]
    have low := bounds.1
    norm_num [timeOfPair, timestampBase] at low ⊢
    omega

theorem csr_injective : Function.Injective Requests.csr := by
  intro first last equal
  cases first <;> cases last <;> first | rfl | contradiction

end Airbender.Delegation.Caller.Proofs
