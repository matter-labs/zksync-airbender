import Human.Helpers.Core.Configuration
import Human.Helpers.Memory.Platform

/-! Facts about the Airbender configuration (`Configured`) that the memory, jump and decoder proofs use:
the reset values of the registers they read, checked by the kernel (`kernel_rfl`). -/

open Lean Meta Elab Tactic in
/-- `kernel_rfl`: close `a = b` with `Eq.refl a`, checked only by the kernel (the elaborator's definitional
    check is far slower on the generated model); the auxiliary theorem is checked now. Proof search, re-checked
    by the kernel. -/
elab "kernel_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (α, lhs, _) := ty.eq? | throwError "kernel_rfl: goal is not an equality"
  let u ← getLevel α
  g.assign (← withOptions (fun o => Elab.async.set (maxRecDepth.set o 1000000) false)
    (mkAuxTheorem ty (mkApp2 (mkConst ``Eq.refl [u]) α lhs)))
  replaceMainGoal []

namespace Airbender.Reference.RiscV.Sail
open Configuration

theorem reset_cur_privilege : resetState.regs .cur_privilege = .Machine := by kernel_rfl
theorem reset_mstatus : resetState.regs .mstatus = 0 := by kernel_rfl
theorem reset_misa : resetState.regs .misa = Configuration.misa := by kernel_rfl
theorem reset_htif : resetState.regs .htif_tohost_base = none := by kernel_rfl
theorem reset_pmpcfg : resetState.regs .pmpcfg_n = Vector.replicate 64 0 := by kernel_rfl
theorem reset_pma : resetState.regs .pma_regions = memoryMap := by kernel_rfl
theorem reset_mlpe : SailRV32.Functions._get_Seccfg_MLPE (resetState.regs .mseccfg) = 0 := by kernel_rfl
theorem reset_elp :
    resetState.regs .elp = SailRV32.Functions.landing_pad_bits_backwards .NO_LP_EXPECTED := by kernel_rfl

namespace Configured
variable {state : State} (h : Configured state)
include h

theorem privilege : state.regs.get? .cur_privilege = some .Machine := by
  rw [h .cur_privilege rfl, reset_cur_privilege]
theorem status : state.regs.get? .mstatus = some 0 := by rw [h .mstatus rfl, reset_mstatus]
theorem misaValue : state.regs.get? .misa = some Configuration.misa := by rw [h .misa rfl, reset_misa]
theorem isa : ∃ value : BitVec 32, state.regs.get? .misa = some value := ⟨_, misaValue h⟩
theorem htifDisabled : state.regs.get? .htif_tohost_base = some none := by
  rw [h .htif_tohost_base rfl, reset_htif]
theorem pmpOff : state.regs.get? .pmpcfg_n = some (Vector.replicate 64 0) := by
  rw [h .pmpcfg_n rfl, reset_pmpcfg]
theorem pma : state.regs.get? .pma_regions = some memoryMap := by rw [h .pma_regions rfl, reset_pma]
theorem supervisorEnvironment : ∃ value : BitVec 64, state.regs.get? .senvcfg = some value :=
  ⟨_, h .senvcfg rfl⟩
theorem machineEnvironment : ∃ value : BitVec 64, state.regs.get? .menvcfg = some value :=
  ⟨_, h .menvcfg rfl⟩
theorem pmpAddresses : ∃ values : Vector (BitVec 32) 64, state.regs.get? .pmpaddr_n = some values :=
  ⟨_, h .pmpaddr_n rfl⟩
theorem hart : ∃ value : BitVec 32, state.regs.get? .mhartid = some value := ⟨_, h .mhartid rfl⟩
theorem landingPad : ∃ security, state.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0 := ⟨_, h .mseccfg rfl, reset_mlpe⟩

end Configured
end Airbender.Reference.RiscV.Sail
