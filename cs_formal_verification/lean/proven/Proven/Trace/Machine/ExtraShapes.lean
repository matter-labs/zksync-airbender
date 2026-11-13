module
public import Proven.Trace.Machine.Projection

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Extra machine metadata has one of the four shapes in the reviewed public projection. -/
theorem extra_shapes {config : RVMachineConfig} {instruction : RV.Instr} {data : RVMachineDecoderData}
    (fields : rvMachineExtraFields config instruction = some data) :
    data = ⟨config.arithmeticFamily, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ ∨
    (∃ kind : RV.DelegationKind, data = ⟨config.arithmeticFamily, 0, kind.csr.toNat, 0, ⟨0, 0⟩, 128, 0⟩) ∨
    (∃ rd : BitVec 5, rd ≠ 0 ∧ data = ⟨config.arithmeticFamily, 0, 0, rd.toNat, ⟨0, 0⟩, 256, 0⟩) ∨
    (∃ (op : RV.FieldOp) (rd rs1 rs2 : BitVec 5) (mask : Nat), rd ≠ 0 ∧ rvModularMask op = some mask ∧
      data = ⟨config.arithmeticFamily, rs1.toNat, rs2.toNat, rd.toNat, ⟨0, 0⟩, mask, 0⟩) := by
  cases instruction <;> simp only [rvMachineExtraFields] at fields
  all_goals try contradiction
  case delegate kind =>
    split at fields
    · cases fields
      exact Or.inr (Or.inl ⟨kind, rfl⟩)
    · cases fields
  case inputRead rd =>
    split at fields
    · cases fields
    · rename_i nonzero
      cases fields
      exact Or.inr (Or.inr (Or.inl ⟨rd, nonzero, rfl⟩))
  case inputWrite source =>
    cases fields
    exact Or.inl rfl
  case mop op rd rs1 rs2 =>
    split at fields
    · cases fields
      exact Or.inl rfl
    · rename_i nonzero
      cases mask : rvModularMask op with
      | none => simp [mask] at fields
      | some value =>
        simp only [mask, Option.map_some, Option.some.injEq] at fields
        subst fields
        exact Or.inr (Or.inr (Or.inr ⟨op, rd, rs1, rs2, value, nonzero, mask, rfl⟩))

/-- Every extra destination is a genuine RV register number. -/
theorem extra_destination_bound {config : RVMachineConfig} {instruction : RV.Instr} {data : RVMachineDecoderData}
    (fields : rvMachineExtraFields config instruction = some data) : data.rd < 32 := by
  rcases extra_shapes fields with rfl | ⟨kind, rfl⟩ | ⟨rd, _, rfl⟩ | ⟨_, rd, _, _, _, _, _, rfl⟩
  · norm_num
  · norm_num
  · exact rd.isLt
  · exact rd.isLt

/-- The extra selector masks fit the existing arithmetic bit decoder. -/
theorem extra_mask_bound {config : RVMachineConfig} {instruction : RV.Instr} {data : RVMachineDecoderData}
    (fields : rvMachineExtraFields config instruction = some data) : data.mask < 512 := by
  rcases extra_shapes fields with rfl | ⟨kind, rfl⟩ | ⟨rd, _, rfl⟩ | ⟨op, rd, rs1, rs2, mask, _, selected, rfl⟩
  · norm_num
  · norm_num
  · norm_num
  · cases op <;> simp only [rvModularMask] at selected
    all_goals first | contradiction | (cases selected; norm_num)

/-- An extra instruction that writes x0 is a NOP row or a delegation caller. -/
theorem extra_zero_shape {config : RVMachineConfig} {instruction : RV.Instr} {data : RVMachineDecoderData}
    (fields : rvMachineExtraFields config instruction = some data) (zero : data.rd = 0) :
    data = ⟨config.arithmeticFamily, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ ∨ data.mask = 128 := by
  rcases extra_shapes fields with rfl | ⟨kind, rfl⟩ | ⟨rd, nonzero, rfl⟩ | ⟨_, rd, _, _, _, nonzero, _, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (nonzero (BitVec.eq_of_toNat_eq zero))
  · exact False.elim (nonzero (BitVec.eq_of_toNat_eq zero))

end Airbender.Trace.Machine.Proofs
