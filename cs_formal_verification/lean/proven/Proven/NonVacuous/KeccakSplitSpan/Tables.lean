module
public import Human.Circuits.KeccakSplit.Tables.Setup
public import Proven.KeccakSplit.Setup.Facts

@[expose] public section

/-! Membership in an exported split-Keccak setup table (the converse of the setup row proofs): a query whose
    entries evaluate to formula row `n` is the table's row `n`, given that every exported row is its formula row
    (`SetupProofs.setupRow_eq`), so no proof decodes the exported blocks. Also the nibbles of five packed nibbles and
    the control-row number of a call. -/

namespace Airbender.NonVacuous.KeccakSplitSpan
open Keccak.Split

/-- A query whose entries evaluate to formula row `n` of an exported setup whose rows are its formula rows. -/
theorem setup_contains {p : Nat} [Fact p.Prime] {data : Import.Setup.SetupData} {width : Nat} {name : String}
    {formula : Nat → Vector Nat width} (length : data.traceLen = 4194304)
    (rows : ∀ n < 4194304, setupRow data width n = (formula n).map Int.ofNat)
    {entry : Vector (Expression (ZMod p)) width} {env : Environment (ZMod p)} (n : Nat) (bound : n < 4194304)
    (values : ∀ j : Fin width, entry[j].eval env = (((formula n)[j] : Nat) : ZMod p)) :
    (Lookup.mk (setupTable (p := p) data width name).toRaw entry).Contains env := by
  have inside : n < data.traceLen := by rw [length]; exact bound
  refine ⟨⟨n, inside⟩, ?_⟩
  change entry.map (Expression.eval env) = (setupRow data width n).map (fun v : Int => (v : ZMod p))
  rw [rows n bound]
  ext j hj
  simp only [Vector.getElem_map, Int.ofNat_eq_natCast, Int.cast_natCast]
  exact values ⟨j, hj⟩

/-- Nibble `i` of five packed nibbles. -/
theorem nib_pack {a0 a1 a2 a3 a4 : Nat} (h0 : a0 < 16) (h1 : a1 < 16) (h2 : a2 < 16) (h3 : a3 < 16) (h4 : a4 < 16) :
    SetupProofs.nib (a0 + 16 * a1 + 256 * a2 + 4096 * a3 + 65536 * a4) 0 = a0 ∧
      SetupProofs.nib (a0 + 16 * a1 + 256 * a2 + 4096 * a3 + 65536 * a4) 1 = a1 ∧
      SetupProofs.nib (a0 + 16 * a1 + 256 * a2 + 4096 * a3 + 65536 * a4) 2 = a2 ∧
      SetupProofs.nib (a0 + 16 * a1 + 256 * a2 + 4096 * a3 + 65536 * a4) 3 = a3 ∧
      SetupProofs.nib (a0 + 16 * a1 + 256 * a2 + 4096 * a3 + 65536 * a4) 4 = a4 := by
  simp only [SetupProofs.nib, Nat.reducePow]
  omega

/-- The controller row of call `k` (`callIndex offset` inverted): one past its round's five calls before it. -/
def ctlRow (offset k : Nat) : Nat := 1 + 5 * (k / 15) + (k % 15 - offset)

theorem callIndex_ctlRow {offset k : Nat} (low : offset ≤ k % 15) (high : k % 15 < offset + 5) :
    SetupProofs.callIndex offset (ctlRow offset k) = k := by
  unfold SetupProofs.callIndex ctlRow
  omega

end Airbender.NonVacuous.KeccakSplitSpan
