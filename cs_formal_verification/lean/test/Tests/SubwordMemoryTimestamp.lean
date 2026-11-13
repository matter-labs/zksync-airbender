module
public import Tests.SubwordMemory
public import Proven.SubwordMemory.Trace
public import Human.Helpers.Tables.Subword
public import Proven.SubwordMemory.WitnessCheck
public import Proven.KernelRfl
public import Proven.Defs.Helpers.Context.Columns

@[expose] public section

namespace Tests.SubwordMemoryTimestamp
open Airbender Arithmetic Trace
set_option warningAsError true

-- LBU x2,0(x1), where x1 points to 0x00400001, with independent
-- register/RAM ports. Exercise ordinary clocks and the 19-bit rollover.
def assignment (rollover : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 2 then (if rollover then 524284 else 4)
  else if i = 3 then (if rollover then 7 else 0)
  else if i = 15 then (if rollover then 0 else 8)
  else if i = 16 then (if rollover then 8 else 0)
  else if i = 62 || i = 63 || i = 64 then 1
  else SubwordMemory.row i

theorem constraints (rollover : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment rollover)) (Airbender.SubwordMemory.clockConstraints (Verification.subwordTable (fun _ => 0))) := by
  apply Verification.holds_append (left := Airbender.SubwordMemory.importedConstraints (Verification.subwordTable (fun _ => 0)))
    (right := Airbender.SubwordMemory.importedConstraintsTimestampLookups)
  · cases rollover <;>
      exact Airbender.SubwordMemory.holds_of_check (Airbender.SubwordMemory.subwordChecked _) rfl (by kernel_rfl)
  · cases rollover <;> exact Airbender.SubwordMemory.timestamps_of_check (by kernel_rfl)

theorem native_clocks (rollover : Bool) :
    ClockEffects Airbender.SubwordMemory.importedConstraintsTraceColumns (assignment rollover) := by
  apply Airbender.SubwordMemory.Proofs.clocks (by decide) (by decide) (constraints rollover)
  constructor
  · cases rollover <;> constructor <;> decide
  · cases rollover <;> decide
  · intro port member
    simp [Airbender.SubwordMemory.importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> cases rollover <;> constructor <;> decide

end Tests.SubwordMemoryTimestamp
