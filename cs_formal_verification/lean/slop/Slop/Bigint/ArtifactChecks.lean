module
public import Human.Circuits.Bigint.Artifact
import all Init.Data.Array.DecidableEq -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)
import all Init.Data.Vector.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)
import all Init.Data.Repr -- Init.Data.Repr is not exposed (still true in 4.35)

@[expose] public section

namespace Airbender.Bigint

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 41 := by rfl

theorem delegation_columns : importedConstraintsDelegationColumns =
    (⟨0, #v[1, 2], (Vector.ofFn (fun i : Fin 19 =>
      Trace.TimestampPort.mk 2 #v[216 + 3 * i.val, 217 + 3 * i.val]
        (218 + 3 * i.val))).toArray⟩ : Delegation.ClockColumns) := by decide

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsDelegationColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsDelegationColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 135 := by rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 95 := by rfl

end Airbender.Bigint

namespace Airbender.Bigint.Addresses

/-- Actual JSON ports: eight writes through x10, then eight reads through x11.
    Each word is four bytes, within a 32-byte ABI block. -/
theorem port_layout : importedConstraintsIndirectPorts =
    (Vector.ofFn fun i : Fin 8 => Verification.IndirectPort.mk 10 i.val #v[3, 4]
      0 none (4 * i.val) #v[5 + 4 * i.val, 6 + 4 * i.val]
      (some #v[7 + 4 * i.val, 8 + 4 * i.val])).append
    (Vector.ofFn fun i : Fin 8 => Verification.IndirectPort.mk 11 i.val #v[37, 38]
      0 none (4 * i.val) #v[39 + 2 * i.val, 40 + 2 * i.val] none) := by decide

end Airbender.Bigint.Addresses
