import Airbender.Proofs.Trace.ZeroValues
import Airbender.Proofs.Trace.Families.ReducedMachine.ComparisonDecoder
import Airbender.Proofs.Trace.Families.ReducedMachine.History
import Airbender.Proofs.ReducedMachine.NativeComparisonPorts

namespace Airbender.ReducedMachine.NativeComparisonRegisterProofs
open Native Arithmetic Trace Verification
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native mixed-port addressing and the original decoded zero flag prove x0
    preservation. Readonly aliases retain their actual initialized reads. -/
theorem row_zero_preserving (row : Row mersenne31Modulus NativeReducedFamily)
    {fixed : Table (ZMod mersenne31Modulus) (fields 4)} {entry : ComparisonProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints fixed))
    (fields : comparisonDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : RowZeroPreserving row := by
  cases row with
  | mk family w =>
    cases family
    intro port member address reads
    change port ∈ importedConstraintsMemoryPorts at member
    simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact reads importedConstraintsMemoryPorts[0]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _) address
    · exact reads importedConstraintsMemoryPorts[1]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _) address
    · have destination := NativeComparisonPortProofs.register_addresses holds fields query 2
      have same : Cell.register entry.data.rd = Cell.register 0 :=
        cell_address_injective (destination.symm.trans address)
      have zero : entry.data.rd = 0 := Cell.register.inj same
      have decoded := NativeComparisonDecoderProofs.decoded_fields fields query
      have mask := decoded.mask
      have flag : rdZeroFlag w = 1 := by rw [decoded.zero,if_pos zero]
      have write := (NativeComparisonFieldProofs.write holds entry.data.family.useRegister mask).2
      have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) write
      have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) write
      simp [flag,arithmeticCandidate] at low high
      change Nat.pair (rdWrite w)[0].val (rdWrite w)[1].val = 0
      rw [low,high]
      rfl

end Airbender.ReducedMachine.NativeComparisonRegisterProofs
