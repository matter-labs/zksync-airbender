import Human.Circuits.KeccakSplit.ColumnParity.SetupArtifact
import Slop.KeccakSplit.Setup.Common

/- Row formulas of the eight exported column-parity setup columns
   (cs/src/tables/keccak_precompile_related.rs), one function per column:
   rows [0, 65536) iota byte XOR (tag 38: a = n % 256, b = n / 256, a ^ rcByte b),
   [65536, 65658) slots (62: control + 2048, six slots), [65658, 65780) control
   (63: control, execute, bump, iota round), [65780, 1114356) XOR5 (64: five nibbles
   of n - 65780 and their XOR); the first row of each controller region is its zero
   key (all zero but the tag); rows from 1114356 on are padding (all zero). -/

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs

open Airbender.Keccak.Split.SetupProofs

set_option warningAsError true

/-- Schedule index of slot/control row `j ≥ 1`. -/
abbrev callAt (j : Nat) : Nat := callIndex 0 j

def spec0 (n : Nat) : Nat :=
  if n < 65536 then n % 256
  else if n < 65658 then (if n = 65536 then 0 else controlAt (callAt (n - 65536)) + 2048)
  else if n < 65780 then (if n = 65658 then 0 else controlAt (callAt (n - 65658)))
  else if n < 1114356 then nib (n - 65780) 0
  else 0

def spec1 (n : Nat) : Nat :=
  if n < 65536 then n / 256
  else if n < 65658 then (if n = 65536 then 0 else slotNat (callAt (n - 65536)) 0)
  else if n < 65780 then (if n = 65658 then 0 else 1)
  else if n < 1114356 then nib (n - 65780) 1
  else 0

def spec2 (n : Nat) : Nat :=
  if n < 65536 then n % 256 ^^^ rcByte (n / 256)
  else if n < 65658 then (if n = 65536 then 0 else slotNat (callAt (n - 65536)) 1)
  else if n < 65780 then (if n = 65658 then 0 else bump (controlAt (callAt (n - 65658))))
  else if n < 1114356 then nib (n - 65780) 2
  else 0

def spec3 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 65658 then (if n = 65536 then 0 else slotNat (callAt (n - 65536)) 2)
  else if n < 65780 then
    (if n = 65658 then 0
     else if callAt (n - 65658) % 5 = 0 then callAt (n - 65658) / 15 else 0)
  else if n < 1114356 then nib (n - 65780) 3
  else 0

def spec4 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 65658 then (if n = 65536 then 0 else slotNat (callAt (n - 65536)) 3)
  else if n < 65780 then 0
  else if n < 1114356 then nib (n - 65780) 4
  else 0

def spec5 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 65658 then (if n = 65536 then 0 else slotNat (callAt (n - 65536)) 4)
  else if n < 65780 then 0
  else if n < 1114356 then
    nib (n - 65780) 0 ^^^ nib (n - 65780) 1 ^^^ nib (n - 65780) 2 ^^^ nib (n - 65780) 3 ^^^
      nib (n - 65780) 4
  else 0

def spec6 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 65658 then (if n = 65536 then 0 else slotNat (callAt (n - 65536)) 5)
  else 0

def spec7 (n : Nat) : Nat :=
  if n < 65536 then 38
  else if n < 65658 then 62
  else if n < 65780 then 63
  else if n < 1114356 then 64
  else 0

end Airbender.Keccak.Split.ColumnParity.SetupProofs
