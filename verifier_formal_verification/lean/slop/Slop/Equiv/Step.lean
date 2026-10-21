import Slop.Equiv.Fetch

/-! One step of the Airbender machine, given what `execute` does: fetch from ROM, decode with our table,
`nextPC := PC + 4`, execute, check alignment, `PC := nextPC`. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
variable {next : BitVec 32}
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000

/-- Every opcode in our table ends in `11`. -/
theorem decode_opc {w : BitVec 32} {i : RV.Instr} (h : RV.decode w = some i) : (w.extractLsb' 0 7).toNat % 4 = 3 := by
  unfold RV.decode at h
  simp only at h
  split at h <;> first | (simp at h; done) | omega

/-- So Sail's fetch never sees a compressed instruction. -/
theorem decode_not_rvc {w : BitVec 32} {i : RV.Instr} (h : RV.decode w = some i) :
    isRVC (Sail.BitVec.extractLsb w 15 0) = false := by
  have h3 := decode_opc h
  simp only [isRVC, Sail.BitVec.extractLsb, SailRV32.not, Bool.not_eq_false', beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.extractLsb_toNat] at h3 ⊢
  omega

/-- One step of the Airbender machine on Sail's state, `next` being the next input word: the new state, and whether
the instruction read it. -/
noncomputable def stepSail (next : BitVec 32) (σ : SailState) : Option (SailState × Bool) :=
  match runSail (Airbender.sailStep next) σ with
  | .ok (some r) σ' => some (σ', r)
  | _ => none

theorem step_eq (m : Airbender.Machine) (σ' : SailState) (r : Bool) (hd : Airbender.delegation m.sail = none)
    (h : stepSail (m.input.headD 0) m.sail = some (σ', r)) :
    Airbender.step m = if r then (match m.input with | _ :: rest => some ⟨σ', rest⟩ | [] => none)
      else some ⟨σ', m.input⟩ := by
  unfold stepSail at h
  unfold Airbender.step
  rw [hd]; dsimp only
  rcases e : runSail (Airbender.sailStep (m.input.headD 0)) m.sail with ⟨_ | r', σ''⟩ | ⟨_, _⟩ <;> rw [e] at h <;>
    simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  cases r' <;> rcases m.input with _ | ⟨w, rest⟩ <;> rfl

theorem step_of_exec (σ : SailState) (hs : Airbender.Configured σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (i : RV.Instr)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some i) (σ2 : SailState)
    (hexec : runSail (Airbender.execute next (Airbender.toSail i)) (σ.set .nextPC (σ.regs .PC + 4)) = .ok RETIRE_SUCCESS σ2)
    (hal : (σ2.regs .nextPC).toNat % 4 = 0) :
    stepSail next σ = some (σ2.set .PC (σ2.regs .nextPC), RV.Instr.readsInput i) := by
  have hf := fetch_rom σ hs ha h2 (decode_not_rvc hdec)
  unfold stepSail Airbender.sailStep
  simp only [Slop.runF_bind, hf, hdec, Slop.runF_writeReg]
  rw [Slop.runF_readReg]
  simp only [hexec, RETIRE_SUCCESS]
  rw [Slop.runF_bind, Slop.runF_readReg]
  simp only [hal, ne_eq, not_true_eq_false, ite_false, tick_pc, Slop.runF_bind, Slop.runF_writeReg, Slop.runF_pure]
  rw [Slop.runF_readReg]
  simp only []
  rw [Slop.runF_readReg]

end Slop.Equiv
