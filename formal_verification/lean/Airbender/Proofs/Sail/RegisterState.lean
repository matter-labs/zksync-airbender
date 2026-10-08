import Airbender.Proofs.Sail.WordMemoryState

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
set_option maxHeartbeats 2000000

private theorem primitive_write (reg : SailRV32.Register) (value : SailRV32.RegisterType reg)
    (before : State) :
    run (do SailRV32.writeReg reg value; pure ()) before =
      .ok () { before with regs := before.regs.insert reg value } := rfl

private theorem pure_run (before : State) :
    run (pure () : SailRV32.SailM Unit) before = .ok () before := rfl

/-- Readback through Sail's original GPR accessors, including its hardwired x0.
    A native cell representing x0 must contain zero. -/
theorem gpr_write_readback (index : BitVec 5) (value : BitVec 32) (before : State)
    (zero : index = 0 → value = 0) :
    ∃ after, run (SailRV32.Functions.wX_bits (.Regidx index) value) before = .ok () after ∧
      after.mem = before.mem ∧
      run (SailRV32.Functions.rX_bits (.Regidx index)) after = .ok value after := by
  by_cases iz : index = 0
  · have vz := zero iz
    subst index
    subst value
    exact ⟨before, rfl, rfl, rfl⟩
  have positive : 0 < index.toNat := by
    have nonzero : index.toNat ≠ 0 := fun h => iz (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  have bound := index.isLt
  change ∃ after, run (SailRV32.Functions.wX (.Regno (index.toNat : Int)) value) before = _ ∧
    _ ∧ run (SailRV32.Functions.rX (.Regno (index.toNat : Int))) after = _
  interval_cases index.toNat
  all_goals simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, primitive_write]
  all_goals apply read_register
  all_goals simp

/-- Writing one GPR preserves every different GPR's actual successful read. -/
theorem gpr_write_other {before after : State} {index other : BitVec 5}
    {written value : BitVec 32}
    (write : run (SailRV32.Functions.wX_bits (.Regidx index) written) before = .ok () after)
    (different : other ≠ index)
    (read : run (SailRV32.Functions.rX_bits (.Regidx other)) before = .ok value before) :
    run (SailRV32.Functions.rX_bits (.Regidx other)) after = .ok value after := by
  have ib := index.isLt
  have ob := other.isLt
  have unequal : other.toNat ≠ index.toNat := by
    intro equal
    exact different (BitVec.eq_of_toNat_eq equal)
  change run (SailRV32.Functions.wX (.Regno (index.toNat : Int)) written) before = _ at write
  change run (SailRV32.Functions.rX (.Regno (other.toNat : Int))) before = _ at read
  change run (SailRV32.Functions.rX (.Regno (other.toNat : Int))) after = _
  interval_cases index.toNat
  all_goals simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, primitive_write, pure_run,
    EStateM.Result.ok.injEq] at write
  all_goals subst after
  all_goals interval_cases other.toNat
  all_goals first
    | contradiction
    | exact read
    | (apply read_register
       simpa [Std.ExtDHashMap.get?_insert] using read_register_iff.mp read)
    | (change EStateM.Result.ok (0 : BitVec 32) before = .ok value before at read
       rw [← (EStateM.Result.ok.inj read).1]
       rfl)

private theorem insert_state_same {reg : SailRV32.Register}
    {value : SailRV32.RegisterType reg} {before : State}
    (present : before.regs.get? reg = some value) :
    { before with regs := before.regs.insert reg value } = before := by
  have registers : before.regs.insert reg value = before.regs := by
    apply Std.ExtDHashMap.ext_get?
    intro other
    by_cases same : reg = other
    · subst other
      simp [present]
    · simp [Std.ExtDHashMap.get?_insert, same]
  cases before
  simp_all

/-- Clock-refresh writes of an unchanged GPR value are actual Sail stutters. -/
theorem gpr_write_same {before : State} {index : BitVec 5} {value : BitVec 32}
    (read : run (SailRV32.Functions.rX_bits (.Regidx index)) before = .ok value before) :
    run (SailRV32.Functions.wX_bits (.Regidx index) value) before = .ok () before := by
  have bound := index.isLt
  change run (SailRV32.Functions.rX (.Regno (index.toNat : Int))) before = _ at read
  change run (SailRV32.Functions.wX (.Regno (index.toNat : Int)) value) before = _
  interval_cases index.toNat
  all_goals simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, primitive_write, pure_run]
  all_goals exact insert_state_same (read_register_iff.mp read)

end Airbender.Reference.RiscV.Sail
