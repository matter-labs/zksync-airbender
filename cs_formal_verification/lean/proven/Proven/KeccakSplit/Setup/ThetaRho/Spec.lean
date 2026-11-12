module
public import Proven.KeccakSplit.Setup.Common

@[expose] public section

/- Row formulas of the nine exported theta/rho setup columns
   (cs/src/tables/binops.rs, keccak_precompile_related.rs), one function per column:
   rows [0, 65536) byte XOR (tag 4: n / 256, n % 256, their XOR),
   [65536, 589824) XOR-and-split (58: a = m % 256, b = m / 256 % 256, s = m / 65536 for
   m = n - 65536, then (a ^ b) * 2^s % 256 and (a ^ b) / 2^(8 - s)),
   [589824, 589945) control (59: control, execute, bump, one-hot iteration),
   [589945, 590066) slots (60: control + 2048, seven slots); the first row of each
   controller region is its zero key (all zero but the tag); rows from 590066 on are
   padding (all zero). -/

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs

open Airbender.Keccak.Split.SetupProofs

set_option warningAsError true

/-- Schedule index of control/slot row `j ≥ 1`. -/
abbrev callAt (j : Nat) : Nat := callIndex 5 j

/-- A control-region column: zero on the zero key, else `f` of the call index. -/
abbrev ctl (n : Nat) (f : Nat → Nat) : Nat := if n = 589824 then 0 else f (callAt (n - 589824))

/-- A slot-region column: zero on the zero key, else `f` of the call index. -/
abbrev slt (n : Nat) (f : Nat → Nat) : Nat := if n = 589945 then 0 else f (callAt (n - 589945))

/-- The XOR-and-split keys of row `n` of its region. -/
abbrev splitA (n : Nat) : Nat := (n - 65536) % 256
abbrev splitB (n : Nat) : Nat := (n - 65536) / 256 % 256
abbrev splitS (n : Nat) : Nat := (n - 65536) / 65536

/-- One-hot flag `f` of call `i`. -/
abbrev flag (f i : Nat) : Nat := if i % 5 = f then 1 else 0

def spec0 (n : Nat) : Nat :=
  if n < 65536 then n / 256
  else if n < 589824 then splitA n
  else if n < 589945 then ctl n controlAt
  else if n < 590066 then slt n (fun i => controlAt i + 2048)
  else 0

def spec1 (n : Nat) : Nat :=
  if n < 65536 then n % 256
  else if n < 589824 then splitB n
  else if n < 589945 then ctl n (fun _ => 1)
  else if n < 590066 then slt n (fun i => slotNat i 0)
  else 0

def spec2 (n : Nat) : Nat :=
  if n < 65536 then n / 256 ^^^ n % 256
  else if n < 589824 then splitS n
  else if n < 589945 then ctl n (fun i => bump (controlAt i))
  else if n < 590066 then slt n (fun i => slotNat i 1)
  else 0

def spec3 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 589824 then (splitA n ^^^ splitB n) * 2 ^ splitS n % 256
  else if n < 589945 then ctl n (flag 0)
  else if n < 590066 then slt n (fun i => slotNat i 2)
  else 0

def spec4 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 589824 then (splitA n ^^^ splitB n) / 2 ^ (8 - splitS n)
  else if n < 589945 then ctl n (flag 1)
  else if n < 590066 then slt n (fun i => slotNat i 3)
  else 0

def spec5 (n : Nat) : Nat :=
  if n < 589824 then 0
  else if n < 589945 then ctl n (flag 2)
  else if n < 590066 then slt n (fun i => slotNat i 4)
  else 0

def spec6 (n : Nat) : Nat :=
  if n < 589824 then 0
  else if n < 589945 then ctl n (flag 3)
  else if n < 590066 then slt n (fun i => slotNat i 5)
  else 0

def spec7 (n : Nat) : Nat :=
  if n < 589824 then 0
  else if n < 589945 then ctl n (flag 4)
  else if n < 590066 then slt n (fun i => slotNat i 6)
  else 0

def spec8 (n : Nat) : Nat :=
  if n < 65536 then 4
  else if n < 589824 then 58
  else if n < 589945 then 59
  else if n < 590066 then 60
  else 0

end Airbender.Keccak.Split.ThetaRho.SetupProofs
