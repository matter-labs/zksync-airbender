module
public import Human.Circuits.KeccakSplit.Tables.Setup
public import Human.Circuits.KeccakSplit.Call
public import Human.Circuits.Keccak.Tables.Setup

@[expose] public section

/- The row formulas of the three split Keccak setups (cs/src/tables/keccak_precompile_related.rs, binops.rs) and the
   claims that the imported rows are these formulas. The tables (`ColumnParity.setup`, `ThetaRho.setup`,
   `Chi5.setup`) read the imported rows; the circuit proofs use the formulas. The first row of each controller region
   is its zero key: every column is zero, except the tag. The rows after the last region are padding: every column is
   zero, the tag too, so a lookup with a fixed nonzero tag never matches a padding row. -/

namespace Airbender.Keccak.Split

/-- Nibble `k` of `m`. -/
def nib (m k : Nat) : Nat := m / 16 ^ k % 16

/-- The call of row `j ≥ 1` of a controller region (`control_table_row`: row `1 + 5 * round + iteration`). The worker
    offset `offset` is 0 for column parity, 5 for theta/rho and 10 for chi. -/
def callIndex (offset j : Nat) : Nat := 15 * ((j - 1) / 5) + offset + (j - 1) % 5

/-- Slot `position` of call `index` (`Call.slots`), as a number; zero outside the schedule. -/
def callSlot (index position : Nat) : Nat :=
  if valid : index < 361 ∧ position < 7 then ((Call.slots ⟨index, valid.1⟩)[position]'valid.2).val else 0

namespace ColumnParity

/-- The call of row `j ≥ 1` of a column-parity controller region. -/
abbrev callAt (j : Nat) : Nat := callIndex 0 j

/-- Column 0: the iota byte, the slot key (control + 2048), the control word, nibble 0. -/
def spec0 (n : Nat) : Nat :=
  if n < 65536 then n % 256
  else if n < 65658 then (if n = 65536 then 0 else controlAt (callAt (n - 65536)) + 2048)
  else if n < 65780 then (if n = 65658 then 0 else controlAt (callAt (n - 65658)))
  else if n < 1114356 then nib (n - 65780) 0
  else 0

/-- Column 1: the round-constant key, slot 0, the execute flag, nibble 1. -/
def spec1 (n : Nat) : Nat :=
  if n < 65536 then n / 256
  else if n < 65658 then (if n = 65536 then 0 else callSlot (callAt (n - 65536)) 0)
  else if n < 65780 then (if n = 65658 then 0 else 1)
  else if n < 1114356 then nib (n - 65780) 1
  else 0

/-- Column 2: the iota output, slot 1, the next control word, nibble 2. -/
def spec2 (n : Nat) : Nat :=
  if n < 65536 then n % 256 ^^^ iotaByte (n / 256)
  else if n < 65658 then (if n = 65536 then 0 else callSlot (callAt (n - 65536)) 1)
  else if n < 65780 then (if n = 65658 then 0 else bump (controlAt (callAt (n - 65658))))
  else if n < 1114356 then nib (n - 65780) 2
  else 0

/-- Column 3: slot 2, the iota round of the first call of a round, nibble 3. -/
def spec3 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 65658 then (if n = 65536 then 0 else callSlot (callAt (n - 65536)) 2)
  else if n < 65780 then
    (if n = 65658 then 0
     else if callAt (n - 65658) % 5 = 0 then callAt (n - 65658) / 15 else 0)
  else if n < 1114356 then nib (n - 65780) 3
  else 0

/-- Column 4: slot 3, nibble 4. -/
def spec4 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 65658 then (if n = 65536 then 0 else callSlot (callAt (n - 65536)) 3)
  else if n < 65780 then 0
  else if n < 1114356 then nib (n - 65780) 4
  else 0

/-- Column 5: slot 4, the XOR of the five nibbles. -/
def spec5 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 65658 then (if n = 65536 then 0 else callSlot (callAt (n - 65536)) 4)
  else if n < 65780 then 0
  else if n < 1114356 then
    nib (n - 65780) 0 ^^^ nib (n - 65780) 1 ^^^ nib (n - 65780) 2 ^^^ nib (n - 65780) 3 ^^^
      nib (n - 65780) 4
  else 0

/-- Column 6: slot 5 (the column parity slot). -/
def spec6 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 65658 then (if n = 65536 then 0 else callSlot (callAt (n - 65536)) 5)
  else 0

/-- Column 7: the tag. -/
def spec7 (n : Nat) : Nat :=
  if n < 65536 then 38
  else if n < 65658 then 62
  else if n < 65780 then 63
  else if n < 1114356 then 64
  else 0

/-- Row `n` of the column-parity setup, by region: the iota byte XOR `a ^ iotaByte b` with `a = n % 256` and
    `b = n / 256` (tag 38), the slots of each parity call keyed by its control word + 2048 (tag 62), the control rows
    (tag 63: control word, execute, next control word, iota round), the five-input XOR of the nibbles of
    `n - 65780` (tag 64), then zero padding from row 1114356. -/
def formulaRow (n : Nat) : Vector Nat 8 :=
  #v[spec0 n, spec1 n, spec2 n, spec3 n, spec4 n, spec5 n, spec6 n, spec7 n]

/-- The imported column-parity setup holds the formula rows on its complete trace domain. -/
def SetupImportClaim : Prop :=
  columnParitySetup.traceLen = 4194304 ∧
    columnParitySetup.Rows fun n => (formulaRow n).map (fun v : Nat => (v : Int))

end ColumnParity

namespace ThetaRho

/-- The call of row `j ≥ 1` of a theta/rho controller region. -/
abbrev callAt (j : Nat) : Nat := callIndex 5 j

/-- A control-region column: zero on the zero key, else `f` of the call. -/
abbrev controlRegion (n : Nat) (f : Nat → Nat) : Nat := if n = 589824 then 0 else f (callAt (n - 589824))

/-- A slot-region column: zero on the zero key, else `f` of the call. -/
abbrev slotRegion (n : Nat) (f : Nat → Nat) : Nat := if n = 589945 then 0 else f (callAt (n - 589945))

/-- The first key `a` of row `n` of the XOR-and-split region. -/
abbrev splitKeyA (n : Nat) : Nat := (n - 65536) % 256

/-- The second key `b` of row `n` of the XOR-and-split region. -/
abbrev splitKeyB (n : Nat) : Nat := (n - 65536) / 256 % 256

/-- The shift `s` of row `n` of the XOR-and-split region. -/
abbrev splitShift (n : Nat) : Nat := (n - 65536) / 65536

/-- The one-hot iteration flag `f` of call `i`. -/
abbrev iterationFlag (f i : Nat) : Nat := if i % 5 = f then 1 else 0

/-- Column 0: the first byte, key `a`, the control word, the slot key (control + 2048). -/
def spec0 (n : Nat) : Nat :=
  if n < 65536 then n / 256
  else if n < 589824 then splitKeyA n
  else if n < 589945 then controlRegion n controlAt
  else if n < 590066 then slotRegion n (fun i => controlAt i + 2048)
  else 0

/-- Column 1: the second byte, key `b`, the execute flag, slot 0. -/
def spec1 (n : Nat) : Nat :=
  if n < 65536 then n % 256
  else if n < 589824 then splitKeyB n
  else if n < 589945 then controlRegion n (fun _ => 1)
  else if n < 590066 then slotRegion n (fun i => callSlot i 0)
  else 0

/-- Column 2: the byte XOR, the shift `s`, the next control word, slot 1. -/
def spec2 (n : Nat) : Nat :=
  if n < 65536 then n / 256 ^^^ n % 256
  else if n < 589824 then splitShift n
  else if n < 589945 then controlRegion n (fun i => bump (controlAt i))
  else if n < 590066 then slotRegion n (fun i => callSlot i 1)
  else 0

/-- Column 3: the low part `(a ^ b) * 2^s % 256`, iteration flag 0, slot 2. -/
def spec3 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 589824 then (splitKeyA n ^^^ splitKeyB n) * 2 ^ splitShift n % 256
  else if n < 589945 then controlRegion n (iterationFlag 0)
  else if n < 590066 then slotRegion n (fun i => callSlot i 2)
  else 0

/-- Column 4: the high part `(a ^ b) / 2^(8 - s)`, iteration flag 1, slot 3. -/
def spec4 (n : Nat) : Nat :=
  if n < 65536 then 0
  else if n < 589824 then (splitKeyA n ^^^ splitKeyB n) / 2 ^ (8 - splitShift n)
  else if n < 589945 then controlRegion n (iterationFlag 1)
  else if n < 590066 then slotRegion n (fun i => callSlot i 3)
  else 0

/-- Column 5: iteration flag 2, slot 4. -/
def spec5 (n : Nat) : Nat :=
  if n < 589824 then 0
  else if n < 589945 then controlRegion n (iterationFlag 2)
  else if n < 590066 then slotRegion n (fun i => callSlot i 4)
  else 0

/-- Column 6: iteration flag 3, slot 5. -/
def spec6 (n : Nat) : Nat :=
  if n < 589824 then 0
  else if n < 589945 then controlRegion n (iterationFlag 3)
  else if n < 590066 then slotRegion n (fun i => callSlot i 5)
  else 0

/-- Column 7: iteration flag 4, slot 6. -/
def spec7 (n : Nat) : Nat :=
  if n < 589824 then 0
  else if n < 589945 then controlRegion n (iterationFlag 4)
  else if n < 590066 then slotRegion n (fun i => callSlot i 6)
  else 0

/-- Column 8: the tag. -/
def spec8 (n : Nat) : Nat :=
  if n < 65536 then 4
  else if n < 589824 then 58
  else if n < 589945 then 59
  else if n < 590066 then 60
  else 0

/-- Row `n` of the theta/rho setup, by region: the byte XOR of `n / 256` and `n % 256` (tag 4), the XOR-and-split
    rows of `m = n - 65536` with `a = m % 256`, `b = m / 256 % 256`, `s = m / 65536`, `(a ^ b) * 2^s % 256` and
    `(a ^ b) / 2^(8 - s)` (tag 58), the control rows (tag 59: control word, execute, next control word, one-hot
    iteration), the slots of each theta/rho call keyed by its control word + 2048 (tag 60), then zero padding from
    row 590066. -/
def formulaRow (n : Nat) : Vector Nat 9 :=
  #v[spec0 n, spec1 n, spec2 n, spec3 n, spec4 n, spec5 n, spec6 n, spec7 n, spec8 n]

/-- The imported theta/rho setup holds the formula rows on its complete trace domain. -/
def SetupImportClaim : Prop :=
  thetaRhoSetup.traceLen = 4194304 ∧ thetaRhoSetup.Rows fun n => (formulaRow n).map (fun v : Nat => (v : Int))

end ThetaRho

namespace Chi5

/-- The call of row `j ≥ 1` of the chi controller region. -/
abbrev callAt (j : Nat) : Nat := callIndex 10 j

/-- Chi of nibble `k` of each lane of a plane: `a ^ (!b & c)` on four bits. -/
def chiOut (m k : Nat) : Nat := nib m k ^^^ ((15 ^^^ nib m ((k + 1) % 5)) &&& nib m ((k + 2) % 5))

/-- A control-region column: zero on the zero key, else `f` of the call. -/
abbrev controlRegion (n : Nat) (f : Nat → Nat) : Nat := if n = 1048576 then 0 else f (callAt (n - 1048576))

/-- Column 0: nibble 0, the control word. -/
def spec0 (n : Nat) : Nat :=
  if n < 1048576 then nib n 0 else if n < 1048697 then controlRegion n controlAt else 0

/-- Column 1: nibble 1, the execute flag. -/
def spec1 (n : Nat) : Nat :=
  if n < 1048576 then nib n 1 else if n < 1048697 then controlRegion n (fun _ => 1) else 0

/-- Column 2: nibble 2, the next control word. -/
def spec2 (n : Nat) : Nat :=
  if n < 1048576 then nib n 2 else if n < 1048697 then controlRegion n (fun i => bump (controlAt i)) else 0

/-- Column 3: nibble 3, slot 0. -/
def spec3 (n : Nat) : Nat :=
  if n < 1048576 then nib n 3 else if n < 1048697 then controlRegion n (fun i => callSlot i 0) else 0

/-- Column 4: nibble 4, slot 1. -/
def spec4 (n : Nat) : Nat :=
  if n < 1048576 then nib n 4 else if n < 1048697 then controlRegion n (fun i => callSlot i 1) else 0

/-- Column 5: chi of nibble 0, slot 2. -/
def spec5 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 0 else if n < 1048697 then controlRegion n (fun i => callSlot i 2) else 0

/-- Column 6: chi of nibble 1, slot 3. -/
def spec6 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 1 else if n < 1048697 then controlRegion n (fun i => callSlot i 3) else 0

/-- Column 7: chi of nibble 2, slot 4. -/
def spec7 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 2 else if n < 1048697 then controlRegion n (fun i => callSlot i 4) else 0

/-- Column 8: chi of nibble 3, the plane `call % 5`. -/
def spec8 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 3 else if n < 1048697 then controlRegion n (fun i => i % 5) else 0

/-- Column 9: chi of nibble 4. -/
def spec9 (n : Nat) : Nat :=
  if n < 1048576 then chiOut n 4 else 0

/-- Column 10: the tag. Tags 65 and 66 cover the chi and control rows; the padding rows have tag 0. -/
def spec10 (n : Nat) : Nat :=
  if n < 1048576 then 65 else if n < 1048697 then 66 else 0

/-- Row `n` of the chi setup, by region: the five nibbles of `n` and chi of them (tag 65), the control rows (tag 66:
    control word, execute, next control word, five slots, plane), then zero padding from row 1048697. -/
def formulaRow (n : Nat) : Vector Nat 11 :=
  #v[spec0 n, spec1 n, spec2 n, spec3 n, spec4 n, spec5 n, spec6 n, spec7 n, spec8 n, spec9 n, spec10 n]

/-- The imported chi setup holds the formula rows on its complete trace domain. -/
def SetupImportClaim : Prop :=
  chi5Setup.traceLen = 4194304 ∧ chi5Setup.Rows fun n => (formulaRow n).map (fun v : Nat => (v : Int))

end Chi5

end Airbender.Keccak.Split
