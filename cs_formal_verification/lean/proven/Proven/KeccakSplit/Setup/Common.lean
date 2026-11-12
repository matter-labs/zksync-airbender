module
public import Human.Circuits.KeccakSplit.Call
public import Proven.Setup.Blocks

@[expose] public section

/- Shared row-formula helpers of the three split Keccak setups
   (cs/src/tables/keccak_precompile_related.rs). -/

namespace Airbender.Keccak.Split.SetupProofs

set_option warningAsError true

/-- Nibble `k` of `m`. -/
def nib (m k : Nat) : Nat := m / 16 ^ k % 16

/-- Schedule index of row `j ≥ 1` of a controller region (`control_table_row`:
    row `1 + 5 * round + iteration`); `offset` is 0, 5 or 10 for parity, theta/rho, chi. -/
def callIndex (offset j : Nat) : Nat := 15 * ((j - 1) / 5) + offset + (j - 1) % 5

/-- Slot `pos` of call `i` as a number: `Call.slots` unfolded into plain conditionals
    (no `Vector.ofFn`), so the kernel evaluates it directly (`slotNat_eq` in `Facts`). -/
def slotNat (i pos : Nat) : Nat :=
  if hp : pos < 5 then
    if kindAt i = .chi5 then
      (Call.physicalSlot (i / 15 + 1)
        ⟨5 * (i % 5) + (pos + 2 * (i % 5)) % 5, by
          have := Nat.mod_lt i (by decide : 0 < 5)
          have := Nat.mod_lt (pos + 2 * (i % 5)) (by decide : 0 < 5)
          omega⟩).val
    else
      (Call.physicalSlot (i / 15) ⟨i % 5 + 5 * pos, by
          have := Nat.mod_lt i (by decide : 0 < 5)
          omega⟩).val
  else if kindAt i = .columnParity ∧ pos = 5 then 25 + i % 5
  else if kindAt i = .thetaRho then 25 + (if pos = 5 then (i % 5 + 4) % 5 else (i % 5 + 1) % 5)
  else 30

/-- `KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED` (common_constants), padded to 32 entries. -/
def rcAdjusted : List Nat :=
  [0, 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
    0, 0, 0, 0, 0, 0, 0]

/-- Byte `b / 32` of the adjusted round constant `b % 32` (the iota table's second key). -/
def rcByte (b : Nat) : Nat := rcAdjusted.getD (b % 32) 0 / 256 ^ (b / 32) % 256

end Airbender.Keccak.Split.SetupProofs
