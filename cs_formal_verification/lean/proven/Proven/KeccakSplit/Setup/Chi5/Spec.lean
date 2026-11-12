module
public import Proven.KeccakSplit.Setup.Common

@[expose] public section

/- Row formulas of the eleven exported chi5 setup columns
   (cs/src/tables/keccak_precompile_related.rs), one function per column:
   rows [0, 1048576) the chi table (tag 65: five nibbles of n and chi of them),
   [1048576, 1048697) control (66: control, execute, bump, five slots, plane);
   the first control row is the zero key (all zero but the tag); rows from 1048697
   on are padding (all zero). -/

namespace Airbender.Keccak.Split.Chi5.SetupProofs

open Airbender.Keccak.Split.SetupProofs

set_option warningAsError true

/-- Schedule index of control row `j ≥ 1`. -/
abbrev callAt (j : Nat) : Nat := callIndex 10 j

/-- Chi of nibble `k` of each lane of a plane: `a ^ (!b & c)` on four bits. -/
def chiOut (m k : Nat) : Nat := nib m k ^^^ ((15 ^^^ nib m ((k + 1) % 5)) &&& nib m ((k + 2) % 5))

/-- A control-region column: zero on the zero key, else `f` of the call index. -/
abbrev ctl (n : Nat) (f : Nat → Nat) : Nat := if n = 1048576 then 0 else f (callAt (n - 1048576))

def spec0 (n : Nat) : Nat :=
  if n < 1048576 then nib n 0 else if n < 1048697 then ctl n controlAt else 0

def spec1 (n : Nat) : Nat :=
  if n < 1048576 then nib n 1 else if n < 1048697 then ctl n (fun _ => 1) else 0

def spec2 (n : Nat) : Nat :=
  if n < 1048576 then nib n 2 else if n < 1048697 then ctl n (fun i => bump (controlAt i)) else 0

def spec3 (n : Nat) : Nat :=
  if n < 1048576 then nib n 3 else if n < 1048697 then ctl n (fun i => slotNat i 0) else 0

def spec4 (n : Nat) : Nat :=
  if n < 1048576 then nib n 4 else if n < 1048697 then ctl n (fun i => slotNat i 1) else 0

def spec5 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 0 else if n < 1048697 then ctl n (fun i => slotNat i 2) else 0

def spec6 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 1 else if n < 1048697 then ctl n (fun i => slotNat i 3) else 0

def spec7 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 2 else if n < 1048697 then ctl n (fun i => slotNat i 4) else 0

def spec8 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 3 else if n < 1048697 then ctl n (fun i => i % 5) else 0

def spec9 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 4 else 0

def spec10 (n : Nat) : Nat :=
  if n < 1048576 then 65 else if n < 1048697 then 66 else 0

end Airbender.Keccak.Split.Chi5.SetupProofs
