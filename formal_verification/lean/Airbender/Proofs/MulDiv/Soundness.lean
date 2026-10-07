import Airbender.Review.MulDiv.ZeroDivision
import Airbender.Proofs.MulDiv
import Airbender.Proofs.Sail.PC

namespace Airbender.MulDiv.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

theorem zero_division_soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    ZeroDivision.circuitModel.SoundnessUnder (ZeroDivision.InterfaceAssumptions (p := p))
      ZeroDivision.spec := by
  intro input output w ⟨interface, h, mapping⟩
  have result := division_by_zero (by omega) input.remainder h interface.selected
    interface.otherSelectors mapping.divisorZero
  have destination : output.destination.toBitVec =
      (if input.remainder then input.left.toBitVec else 0xffffffff) := by
    simpa [Word.toBitVec, Word.value, mapping.outputLo, mapping.outputHi,
      mapping.leftLo, mapping.leftHi] using result
  have pc := pc_successor hp inverse h
    ⟨mapping.pcLo, mapping.pcHi, mapping.finalPCLo, mapping.finalPCHi⟩ interface.initialPCBound
  apply Sail.retire_of_destination interface.pcRead pc.2.2
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have leftRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs1 interface.leftRead
  have rightRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs2 interface.rightRead
  have same : run (ZeroDivision.execution input) prepared =
      run (Sail.writeResult input.rd output.destination) prepared := by
    unfold ZeroDivision.execution Sail.writeResult
    cases operation : input.remainder
    · simp only [Bool.false_eq_true, ↓reduceIte, SailRV32.Functions.execute_DIV]
      rw [run_bind_of_ok _ _ _ _ _ leftRead,
        run_bind_of_ok _ _ _ _ _ rightRead]
      simp [SailRV32.Functions.to_bits_truncate, SailRV32.Functions.not,
        _root_.Sail.BitVec.toNatInt, _root_.Sail.get_slice_int, operation] at destination ⊢
      rw [destination]
    · simp only [↓reduceIte, SailRV32.Functions.execute_REM]
      rw [run_bind_of_ok _ _ _ _ _ leftRead,
        run_bind_of_ok _ _ _ _ _ rightRead]
      simp [SailRV32.Functions.to_bits_truncate, _root_.Sail.BitVec.toNatInt,
        _root_.Sail.get_slice_int, operation] at destination ⊢
      rw [destination, BitVec.extractLsb'_setWidth_of_le (by decide)]
      simp
      rfl
  obtain ⟨after, write⟩ := Sail.write_success input.rd output.destination.toBitVec prepared
  have projected : run (Sail.writeResult input.rd output.destination) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    unfold Sail.writeResult
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  exact ⟨after, same.trans projected, projected⟩

end Airbender.MulDiv.Proofs
