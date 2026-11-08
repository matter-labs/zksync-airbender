module
public import Human.Helpers.Memory.Ports

@[expose] public section

namespace Airbender.Trace.Proofs

/-- Bounded byte packing has no base-field wrap. The bounds are proof inputs
    supplied by circuit lookups; the native port metadata supplies only wiring. -/
theorem packed_bytes {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {low high : ZMod p} (lo : low.val < 256) (hi : high.val < 256) :
    (low + 256 * high).val = low.val + 256 * high.val := by
  have bound : low.val + 256 * high.val < p := by omega
  have encoded : low + 256 * high = ((low.val + 256 * high.val : Nat) : ZMod p) := by
    simp [Nat.cast_add, Nat.cast_mul]
  rw [encoded, ZMod.val_natCast, Nat.mod_eq_of_lt bound]

set_option backward.isDefEq.respectTransparency false in
theorem byte_port_code {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {w : Nat → ZMod p} (columns : Vector Nat 4)
    (bounds : ∀ i : Fin 4, (w columns[i]).val < 256) :
    (WordColumns.u8 columns).code w =
      Nat.pair ((w columns[0]).val + 256 * (w columns[1]).val)
        ((w columns[2]).val + 256 * (w columns[3]).val) := by
  dsimp [WordColumns.code, WordColumns.evaluate]
  congr 1
  · exact packed_bytes hp (bounds 0) (bounds 1)
  · exact packed_bytes hp (bounds 2) (bounds 3)

end Airbender.Trace.Proofs
