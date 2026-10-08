import Airbender.Review.Trace.MemoryPorts

namespace Airbender.Trace.Proofs

theorem pairCode_eq_iff {p : Nat} {w v : Nat → ZMod p} {left right : Vector Nat 2} :
    pairCode w left = pairCode v right ↔
      (w left[0]).val = (v right[0]).val ∧ (w left[1]).val = (v right[1]).val :=
  Nat.pair_eq_pair

theorem readonly_preserves_value {p : Nat} {port : MemoryPort}
    (readonly : port.writeColumns = none) (columns : TraceColumns) (w : Nat → ZMod p) :
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
