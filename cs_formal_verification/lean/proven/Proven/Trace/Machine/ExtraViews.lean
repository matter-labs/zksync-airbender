module
public import Proven.Trace.Machine.ModularData
public import Proven.Trace.RVPooled.Oracle

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Every unrolled setup selects the standalone arithmetic family. -/
theorem unrolled_arithmetic_family {config : RVMachineConfig} (unrolled : config ≠ .unified) :
    config.arithmeticFamily = .pooled .addSub := by
  cases config <;> simp_all [RVMachineConfig.arithmeticFamily]

/-- The unrolled arithmetic metadata view preserves every native field. -/
theorem unrolled_arithmetic_view {config : RVMachineConfig} (unrolled : config ≠ .unified)
    (data : DecoderData) (family : data.family = .addSub) :
    RVMachineDecoderData.ofOrdinary (family := fun _ => config.arithmeticFamily) data =
      RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled) (data.mapFamily pooledArithmeticFamily) := by
  rw [unrolled_arithmetic_family unrolled]
  cases data with
  | mk tag rs1 rs2 rd immediate mask funct3 =>
    change tag = .addSub at family
    subst tag
    rfl

/-- The unified arithmetic metadata view preserves every native field. -/
theorem unified_arithmetic_view (data : DecoderData) :
    RVMachineDecoderData.ofOrdinary (family := fun _ => RVMachineConfig.unified.arithmeticFamily) data =
      RVMachineDecoderData.ofOrdinary (family := fun _ => .unified) (data.mapFamily (fun _ => UnifiedFamily.machine)) := by
  rfl

/-- A submitted external read has a nonzero destination and the exact native read metadata. -/
theorem extra_read_data {config : RVMachineConfig} {rd : BitVec 5} {data : RVMachineDecoderData}
    (fields : rvMachineExtraFields config (.inputRead rd) = some data) :
    rd ≠ 0 ∧ data = RVMachineDecoderData.ofOrdinary (family := fun _ => config.arithmeticFamily) (rvReadData rd) := by
  simp only [rvMachineExtraFields] at fields
  split at fields
  · cases fields
  · refine ⟨by assumption, ?_⟩
    rw [← Option.some.inj fields]
    rfl

/-- A submitted external write uses the native NOP metadata. -/
theorem extra_write_data {config : RVMachineConfig} {source : BitVec 5} {data : RVMachineDecoderData}
    (fields : rvMachineExtraFields config (.inputWrite source) = some data) :
    data = RVMachineDecoderData.ofOrdinary (family := fun _ => config.arithmeticFamily) rvNopData := by
  simp only [rvMachineExtraFields, Option.some.injEq] at fields
  rw [← fields]
  rfl

/-- Every discarded modular destination uses the same native NOP metadata. -/
theorem extra_mop_zero_data {config : RVMachineConfig} {opcode : RV.FieldOp} {rs1 rs2 : BitVec 5} {data : RVMachineDecoderData}
    (fields : rvMachineExtraFields config (.mop opcode 0 rs1 rs2) = some data) :
    data = RVMachineDecoderData.ofOrdinary (family := fun _ => config.arithmeticFamily) rvNopData := by
  simp only [rvMachineExtraFields, ↓reduceIte, Option.some.injEq] at fields
  rw [← fields]
  rfl

/-- Each nonzero supported modular destination keeps its exact register and operation metadata. -/
theorem extra_modular_data {config : RVMachineConfig} {opcode : AddSub.Modular.Opcode} {rs1 rs2 rd : BitVec 5}
    {data : RVMachineDecoderData} (nonzero : rd ≠ 0)
    (fields : rvMachineExtraFields config (.mop opcode.rvOp rd rs1 rs2) = some data) :
    data = RVMachineDecoderData.ofOrdinary (family := fun _ => config.arithmeticFamily) (modularData opcode rs1 rs2 rd) := by
  exact (Option.some.inj ((machine_modular_fields config opcode rs1 rs2 rd nonzero).symm.trans fields)).symm

end Airbender.Trace.Machine.Proofs
