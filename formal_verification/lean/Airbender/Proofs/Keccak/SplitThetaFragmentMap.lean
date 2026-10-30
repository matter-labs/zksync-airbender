import Airbender.Proofs.Keccak.SplitThetaXorValues

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- A finite correspondence between actual fragment nodes and the checked byte-XOR nodes. -/
structure XorFragmentMap where
  leaf : Vector Nat 256
  pair : Vector Nat 256
  byte : Vector Nat 16
  root : Nat
  deriving Repr

def XorFragmentMap.at (map : XorFragmentMap) (remaining node : Nat) : Nat :=
  if remaining = 1 then map.leaf[node % 256]'(Nat.mod_lt _ (by decide))
  else if remaining = 2 then map.pair[node % 256]'(Nat.mod_lt _ (by decide))
  else if remaining = 3 then map.byte[node % 16]'(Nat.mod_lt _ (by decide)) else map.root

/-- Reachable byte-XOR nodes at each of its four actual literal levels. -/
def xorFragmentNodeBound (remaining : Nat) : Nat :=
  if remaining = 4 then 1 else if remaining = 3 then 16 else 256

/-- The native low fragment preserves the low byte after the selected shift. -/
def xorFragmentLow (shift value : Nat) : Nat := value * 2 ^ shift % 256

/-- The native high fragment preserves the byte's overflow after the selected shift. -/
def xorFragmentHigh (shift value : Nat) : Nat := value / 2 ^ (8 - shift)

/-- Every actual fragment transition must preserve its complete byte-XOR correspondence. -/
def XorFragmentRefines (target : Column) (output : Nat → Nat) (map : XorFragmentMap) : Prop :=
  ∀ remaining : Fin 4, ∀ node : Fin (xorFragmentNodeBound (remaining.val + 1)), ∀ digit : Fin 16,
    target.entry (map.at (remaining.val + 1) node.val) digit.val =
      if remaining.val = 0 then output (xorByteEntry node.val digit.val)
      else map.at remaining.val (xorByteEntry node.val digit.val)

/-- Checked byte-XOR nodes remain in the next reachable level. -/
theorem xor_fragment_next_bound (remaining node digit : Nat)
    (hr : 2 ≤ remaining ∧ remaining ≤ 4) (hn : node < xorFragmentNodeBound remaining) (hd : digit < 16) :
    xorByteEntry node digit < xorFragmentNodeBound (remaining - 1) := by
  have choices : remaining = 2 ∨ remaining = 3 ∨ remaining = 4 := by omega
  rcases choices with rfl | rfl | rfl
  · exact xor_byte_entry_bound hn hd
  · have bound : node < 16 := hn
    exact xor_byte_entry_bound (by omega) hd
  · have zero : node = 0 := by change node < 1 at hn; omega
    subst node
    simpa [xorFragmentNodeBound, xorByteEntry] using hd

/-- A finite transition certificate proves the transformed output for the complete actual evaluation. -/
theorem xor_fragment_evaluate {target : Column} {output : Nat → Nat} {map : XorFragmentMap}
    (certificate : XorFragmentRefines target output map) (remaining node row : Nat)
    (positive : 1 ≤ remaining) (upper : remaining ≤ 4) (bound : node < xorFragmentNodeBound remaining) :
    target.evaluate remaining (map.at remaining node) row =
      output ((thetaRhoXor.columns[2]).evaluate remaining node row) := by
  induction remaining generalizing node with
  | zero => omega
  | succ previous ih =>
    let digit := row / 16 ^ previous % 16
    have digitBound : digit < 16 := Nat.mod_lt _ (by decide)
    have nodeBound : node < 256 := by
      unfold xorFragmentNodeBound at bound
      split_ifs at bound <;> omega
    have actual : (thetaRhoXor.columns[2]).entry node digit = xorByteEntry node digit :=
      xor_byte_output_entries ⟨node, nodeBound⟩ ⟨digit, digitBound⟩
    have transition := certificate ⟨previous, by omega⟩ ⟨node, bound⟩ ⟨digit, digitBound⟩
    by_cases last : previous = 0
    · subst previous
      have equality := transition.trans (congrArg output actual.symm)
      simpa only [Column.evaluate, ite_true] using equality
    · have next := xor_fragment_next_bound (previous + 1) node digit ⟨by omega, upper⟩ bound digitBound
      have result := ih (xorByteEntry node digit) (by omega) (by omega) (by simpa using next)
      simp only [Column.evaluate, if_neg last]
      rw [transition, if_neg last, actual]
      exact result

/-- The actual five-level fragment column has the transformed complete byte-XOR value. -/
theorem xor_fragment_value {target : Column} {output : Nat → Nat} {map : XorFragmentMap}
    (certificate : XorFragmentRefines target output map) (depth : target.depth = 5)
    (row shift : Nat) (selected : row / 65536 % 16 = shift)
    (root : target.entry target.root shift = map.root) :
    target.value row = output ((thetaRhoXor.columns[2]).value row) := by
  unfold Column.value
  rw [depth, xor_byte_shapes.2.2.1, xor_byte_shapes.2.2.2]
  change target.evaluate 4 (target.entry target.root (row / 65536 % 16)) row = _
  rw [selected, root]
  have result := xor_fragment_evaluate certificate 4 0 row (by decide) (by decide) (by decide)
  change target.evaluate 4 map.root row = _ at result
  exact result

/-- Four small kernel certificates cover the complete native byte-node range. -/
theorem xor_fragment_blocks (property : Nat → Prop)
    (first : ∀ node : Fin 64, property node.val)
    (second : ∀ node : Fin 64, property (64 + node.val))
    (third : ∀ node : Fin 64, property (128 + node.val))
    (fourth : ∀ node : Fin 64, property (192 + node.val)) :
    ∀ node : Fin 256, property node.val := by
  intro node
  by_cases h0 : node.val < 64
  · exact first ⟨node.val, h0⟩
  · by_cases h1 : node.val < 128
    · have value := second ⟨node.val - 64, by omega⟩
      simpa only [Nat.add_sub_of_le (by omega : 64 ≤ node.val)] using value
    · by_cases h2 : node.val < 192
      · have value := third ⟨node.val - 128, by omega⟩
        simpa only [Nat.add_sub_of_le (by omega : 128 ≤ node.val)] using value
      · have value := fourth ⟨node.val - 192, by have := node.isLt; omega⟩
        simpa only [Nat.add_sub_of_le (by omega : 192 ≤ node.val)] using value

/-- One checked complete native node gives every digit transition without repeated node lookups. -/
theorem xor_fragment_entry_of_row {target : Column} {node : Nat} {expected : Fin 16 → Nat}
    (equal : target.nodes[node]? = some (Vector.ofFn expected)) (digit : Fin 16) :
    target.entry node digit.val = expected digit := by
  simp [Column.entry, equal, Nat.mod_eq_of_lt digit.isLt]

/-- Smaller node blocks keep the native pair-node checks within the same memory limit. -/
theorem xor_fragment_small_blocks (property : Nat → Prop)
    (first : ∀ node : Fin 16, property node.val)
    (second : ∀ node : Fin 16, property (16 + node.val))
    (third : ∀ node : Fin 16, property (32 + node.val))
    (fourth : ∀ node : Fin 16, property (48 + node.val)) :
    ∀ node : Fin 64, property node.val := by
  intro node
  by_cases h0 : node.val < 16
  · exact first ⟨node.val, h0⟩
  · by_cases h1 : node.val < 32
    · have value := second ⟨node.val - 16, by omega⟩
      simpa only [Nat.add_sub_of_le (by omega : 16 ≤ node.val)] using value
    · by_cases h2 : node.val < 48
      · have value := third ⟨node.val - 32, by omega⟩
        simpa only [Nat.add_sub_of_le (by omega : 32 ≤ node.val)] using value
      · have value := fourth ⟨node.val - 48, by have := node.isLt; omega⟩
        simpa only [Nat.add_sub_of_le (by omega : 48 ≤ node.val)] using value

/-- Exact finite checks on all four actual levels supply the complete correspondence. -/
theorem xor_fragment_refines_of_levels {target : Column} {output : Nat → Nat} {map : XorFragmentMap}
    (leaf : ∀ (node : Fin 256) (digit : Fin 16),
      target.entry (map.at 1 node.val) digit.val = output (xorByteEntry node.val digit.val))
    (pair : ∀ (node : Fin 256) (digit : Fin 16),
      target.entry (map.at 2 node.val) digit.val = map.at 1 (xorByteEntry node.val digit.val))
    (byte : ∀ (node : Fin 16) (digit : Fin 16),
      target.entry (map.at 3 node.val) digit.val = map.at 2 (xorByteEntry node.val digit.val))
    (root : ∀ digit : Fin 16,
      target.entry map.root digit.val = map.at 3 (xorByteEntry 0 digit.val)) :
    XorFragmentRefines target output map := by
  intro remaining node digit
  fin_cases remaining
  · exact leaf ⟨node.val, node.isLt⟩ digit
  · exact pair ⟨node.val, node.isLt⟩ digit
  · exact byte ⟨node.val, node.isLt⟩ digit
  · have zero : node.val = 0 := by have bound := node.isLt; change node.val < 1 at bound; omega
    simpa [zero, XorFragmentMap.at] using root digit

/-- Whole-node equalities supply all four exact transition levels. -/
theorem xor_fragment_refines_of_rows {target : Column} {output : Nat → Nat} {map : XorFragmentMap}
    (leaf : ∀ node : Fin 256, target.nodes[map.at 1 node.val]? =
      some (Vector.ofFn fun digit : Fin 16 => output (xorByteEntry node.val digit.val)))
    (pair : ∀ node : Fin 256, target.nodes[map.at 2 node.val]? =
      some (Vector.ofFn fun digit : Fin 16 => map.at 1 (xorByteEntry node.val digit.val)))
    (byte : ∀ node : Fin 16, target.nodes[map.at 3 node.val]? =
      some (Vector.ofFn fun digit : Fin 16 => map.at 2 (xorByteEntry node.val digit.val)))
    (root : target.nodes[map.root]? =
      some (Vector.ofFn fun digit : Fin 16 => map.at 3 (xorByteEntry 0 digit.val))) :
    XorFragmentRefines target output map := by
  exact xor_fragment_refines_of_levels
    (fun node digit => xor_fragment_entry_of_row (leaf node) digit)
    (fun node digit => xor_fragment_entry_of_row (pair node) digit)
    (fun node digit => xor_fragment_entry_of_row (byte node) digit)
    (fun digit => xor_fragment_entry_of_row root digit)

end Airbender.Keccak.Split.Native.Fixed.Proofs
