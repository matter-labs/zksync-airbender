import Airbender.Review.Helpers.Memory.Ports

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

theorem pairCode_eq_iff {p : Nat} {w v : Nat → ZMod p} {left right : Vector Nat 2} :
    pairCode w left = pairCode v right ↔
      (w left[0]).val = (v right[0]).val ∧ (w left[1]).val = (v right[1]).val :=
  Nat.pair_eq_pair

theorem readonly_preserves_value {p : Nat} {port : MemoryPort}
    (readonly : port.writeValue = none) (columns : TraceColumns) (w : Nat → ZMod p) :
    port.event columns w =
      ((decodeTimestamp w columns.initialTime).value + port.clock.offset,
        port.address.code w, port.readCode w, port.readCode w) := by
  simp [MemoryPort.event, MemoryPort.writeCode, MemoryPort.readCode, readonly]

theorem mixed_register {p : Nat} {w : Nat → ZMod p} {selector : Nat}
    {columns : Vector Nat 2} (selected : w selector = 1) :
    (MemoryAddress.mixed selector true columns).code w = Nat.pair 0 (pairCode w columns) := by
  simp [MemoryAddress.code, selected]

theorem mixed_ram {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    {selector : Nat} {columns : Vector Nat 2} (selected : w selector = 1) :
    (MemoryAddress.mixed selector false columns).code w = Nat.pair 1 (pairCode w columns) := by
  simp [MemoryAddress.code, selected, ZMod.val_one]

/-- A RAM address cannot alias a register, even before address limbs are bounded. -/
theorem ram_register_disjoint {p : Nat} [Fact p.Prime]
    {w : Nat → ZMod p} {selector register : Nat} {columns : Vector Nat 2}
    (selected : w selector = 1) :
    (MemoryAddress.mixed selector false columns).code w ≠ (MemoryAddress.register register).code w := by
  rw [mixed_ram selected]
  simp [MemoryAddress.code]

end Airbender.Trace.Proofs
