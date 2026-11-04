import Slop.Sail.ForwardSim

/-! # `Simple` closure: the generated register clauses are covered computations

`Simple` (ForwardSim) holds for a computation whose every instruction effect is covered. Here: closure under
bind, the register primitives, and the generated `execute_RTYPE` / `execute_ITYPE` / `execute_UTYPE` clauses
(what `registerClause` selects for the AddSub family). -/

namespace Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem Configuration Airbender.Reference.Sail SailRV32 SailRV32.Functions

/-- `pure` is covered. -/
theorem simple_pure {ue α : Type} (a : α) : Simple (FreeM.pure a : PreSailM ue α) := Simple.pure a

/-- Sequencing covered computations gives a covered computation. -/
theorem simple_bind {ue α β : Type} {m : PreSailM ue α} {k : α → PreSailM ue β} (hm : Simple m)
    (hk : ∀ x, Simple (k x)) : Simple (FreeM.bind m k) := by
  induction hm with
  | pure a => exact hk a
  | impure e k' hc hkk ih =>
    exact Simple.impure e _ hc (fun x => ih x)

/-- A register read is covered. -/
theorem simple_readReg {ue : Type} (r : Register) : Simple (PreSail.readReg (ue := ue) r) :=
  Simple.impure _ _ trivial (fun x => Simple.pure x)

/-- A register write is covered. -/
theorem simple_writeReg {ue : Type} (r : Register) (v : Arch.register_type r) :
    Simple (PreSail.writeReg (ue := ue) r v) :=
  Simple.impure (.inl (.ok (InstructionEffect.regWrite r Option.none v))) _ (by simp [Covered, InstrCovered])
    (fun x => Simple.pure x)

/-- Tactic core: unfold-and-split closes a generated clause whose effects are register reads and writes. -/
macro "simple_clause" : tactic => `(tactic| repeat' (first
  | exact simple_pure _
  | exact simple_readReg _
  | exact simple_writeReg _ _
  | apply simple_bind
  | intro _
  | split))

theorem simple_rX (r : regno) : Simple (rX r) := by
  unfold rX; simple_clause

theorem simple_wX (r : regno) (v : BitVec 32) : Simple (wX r v) := by
  unfold wX; simple_clause

theorem simple_rX_bits (r : regidx) : Simple (rX_bits r) := by
  unfold rX_bits; dsimp only; exact simple_rX _

theorem simple_wX_bits (r : regidx) (v : BitVec 32) : Simple (wX_bits r v) := by
  unfold wX_bits; dsimp only; exact simple_wX _ _

theorem simple_get_arch_pc : Simple (get_arch_pc ()) := by
  unfold get_arch_pc; exact simple_readReg _

/-- Clauses: the register primitives above, plus the PC read. -/
macro "simple_exec" : tactic => `(tactic| repeat' (first
  | exact simple_pure _
  | exact simple_readReg _
  | exact simple_writeReg _ _
  | exact simple_rX_bits _
  | exact simple_wX_bits _ _
  | exact simple_get_arch_pc
  | apply simple_bind
  | intro _
  | split))

theorem simple_execute_RTYPE (rs2 rs1 rd : regidx) (op : rop) : Simple (execute_RTYPE rs2 rs1 rd op) := by
  unfold execute_RTYPE; dsimp only; cases op <;> simple_exec

theorem simple_execute_ITYPE (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    Simple (execute_ITYPE imm rs1 rd op) := by
  unfold execute_ITYPE; dsimp only; cases op <;> simple_exec

theorem simple_execute_UTYPE (imm : BitVec 20) (rd : regidx) (op : uop) :
    Simple (execute_UTYPE imm rd op) := by
  unfold execute_UTYPE; dsimp only; cases op <;> simple_exec

theorem simple_tick_pc : Simple (SailRV32.Functions.tick_pc ()) := by
  unfold SailRV32.Functions.tick_pc
  dsimp only
  refine simple_bind (simple_readReg _) (fun _ => ?_)
  exact simple_bind (simple_writeReg _ _) (fun _ => Simple.pure _)

theorem simple_normalBaseNextPC : Simple normalBaseNextPC := by
  unfold normalBaseNextPC
  dsimp only
  refine simple_bind (simple_readReg _) (fun _ => ?_)
  exact simple_writeReg _ _

/-- The normal four-byte path around a covered clause. -/
theorem simple_normalStep {m : SailRV32.SailM SailRV32.ExecutionResult} (hm : Simple m) :
    Simple (normalStep m) := by
  unfold normalStep
  dsimp only
  refine simple_bind simple_normalBaseNextPC (fun _ => ?_)
  refine simple_bind hm (fun r => ?_)
  exact simple_bind simple_tick_pc (fun _ => Simple.pure _)

end Airbender.Reference.RiscV.Sail
