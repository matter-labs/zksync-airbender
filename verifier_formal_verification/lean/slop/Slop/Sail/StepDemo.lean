import Slop.Sail.KernelRfl
import Slop.Sail.Writes

open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human

namespace Slop

/-- `reg_name_forwards` (a pure name lookup for a 5-bit index) succeeds without touching the state. -/
theorem reg_name_pure (x : BitVec 5) (s : SailState) :
    ∃ n, runSail (reg_name_forwards (.Regidx x)) s = .ok n s := by
  refine ⟨reg_arch_name_raw_forwards (encdec_reg_forwards (regidx.Regidx x)), ?_⟩
  unfold reg_name_forwards
  simp [encdec_reg_forwards_matches, get_config_use_abi_names, SailRV32.not, runF_pure]

/-- The register-name callback: a no-op on the state. -/
theorem xreg_callback_ok (x : BitVec 5) (v : BitVec 32) (s : SailState) :
    runSail (xreg_write_callback (.Regidx x) v) s = .ok () s := by
  obtain ⟨n, hn⟩ := reg_name_pure x s
  unfold xreg_write_callback
  rw [runF_bind, hn]
  simp only [runF_pure]

/-- `addi a0, a0, 1` as executed by Sail's `execute_ITYPE`: a single register update of `x10`. -/
theorem runF_addi_x10 (s : SailState) :
    runSail (execute_ITYPE 1#12 (.Regidx 10#5) (.Regidx 10#5) .ADDI) s
      = .ok RETIRE_SUCCESS (s.set .x10 (s.regs .x10 + 1)) := by
  have hext : (sign_extend (m := 32) (1#12 : BitVec 12)) = (1#32 : BitVec 32) := by decide
  have h10 : (BitVec.toNatInt (10#5 : BitVec 5)).toNat = 10 := by decide
  have hr := runF_readReg Register.x10 s
  have hne : ((10 : Nat) != 0) = true := by decide
  unfold execute_ITYPE wX_bits rX_bits
  simp only [hext, h10, runF_bind, runF_writeReg, runF_pure, RETIRE_SUCCESS,
    rX, wX, regval_from_reg, regval_into_reg, xreg_callback_ok, hr, hne, ↓reduceIte]
  rfl

end Slop

namespace Slop
open Human Wr

/-- Known facts after reset plus `PC = 0xd8`; `minstret` and the GPRs are left symbolic. -/
noncomputable def K0base (mem : Nat → BitVec 8) : Known :=
  { regs := fun r => if writtenByProgram r then none else some (resetState.regs r),
    code := fun i => if 0xd8 ≤ i ∧ i < 0xdc then some ((0x00150513#32).extractLsb' (8*(i-0xd8)) 8) else none,
    data := mem }

noncomputable def K0 (mem : Nat → BitVec 8) : Known := (K0base mem).set .PC (0xd8#32)

theorem probe_fetch : (runOracleW (K0 fun _ => 0) (fetch ())).isSome = true := by decide +kernel
theorem probe_mip : (runOracleW (K0 fun _ => 0) (update_mip ())).isSome = true := by decide +kernel
theorem probe_minc : (runOracleW (K0 fun _ => 0) (should_inc_minstret .Machine)).isSome = true := by decide +kernel
theorem probe_disp : (runOracleW (K0 fun _ => 0) (dispatchInterrupt .Machine)).isSome = true := by decide +kernel

end Slop

namespace Slop
open Human Wr
theorem probe_decode : (runOracleW (K0 fun _ => 0) (ext_decode 0x00150513#32)).isSome = true := by decide +kernel
theorem probe_trig : (runOracleW (K0 fun _ => 0) (find_highest_priority_pending_trigger .Machine)).isSome = true := by decide +kernel
end Slop

namespace Slop
open Human Wr

/-- K0 plus symbolic a0 and minstret. -/
noncomputable def Ks (s : SailState) : Known :=
  (((K0 s.mem).set .x10 (s.regs .x10)).set .minstret (s.regs .minstret))

set_option maxRecDepth 1000000 in
/-- The whole official `try_step` on `addi a0, a0, 1` with SYMBOLIC a0 and minstret, evaluated by the kernel. -/
theorem try_step_addi_vals (s : SailState) : (Wr.oracleGo 100000 (Ks s) (try_step 0 false)).map
    (fun p => (p.1, p.2.regs .x10, p.2.regs .PC, p.2.regs .minstret)) =
    some (false, some (s.regs .x10 + 1), some 0xdc, some (s.regs .minstret + 1)) := by
  kernel_rfl

end Slop
