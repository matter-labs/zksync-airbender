import Airbender.Review.Circuits.Keccak.Call
import Airbender.Proofs.Keccak.NativeEffects
import Airbender.Proofs.Keccak.MicroOperations
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Keccak.Call.Proofs
open Arithmetic Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

theorem column_selected (lanes : Vector Nat 6) (column : Fin 5) (i : Fin 5) :
    (columnState lanes column)[5 * column.val + i.val] = lanes[i.val] := by
  have division : (5 * column.val + i.val) / 5 = column.val := by omega
  have remainder : (5 * column.val + i.val) % 5 = i.val := by omega
  simp [columnState, division, remainder]

theorem embedded_reads (w : Nat → ZMod p) (column : Fin 5) :
    Native.ColumnReads (columnState (Vector.ofFn (Native.readLane w)) column) column w := by
  intro i
  rw [column_selected]
  simp

theorem native_operation {w : Nat → ZMod p} {control : ControlState}
    (effects : Native.RowEffects w) (read : (w 3).val = control.packed)
    (supported : Supported control) :
    Operation control (Vector.ofFn (Native.readLane w)) (Native.writtenLanes w) := by
  rcases control with ⟨mode, iteration, round⟩
  fin_cases mode
  · let selected : Fin 25 := ⟨round.val, by have bound : round.val ≤ 24 := supported.1; omega⟩
    have actual := effects.iota (columnState (Vector.ofFn (Native.readLane w)) iteration)
      iteration selected read (embedded_reads w iteration)
    refine ⟨selected, rfl, ?_⟩
    apply Vector.ext
    intro i bound
    simp only [Native.writtenLanes, iotaColumn, Vector.getElem_ofFn]
    split_ifs with first
    · exact (Native.Proofs.lane_ports w ⟨i, bound⟩).2.trans (actual.1 ⟨i, first⟩)
    · have same : i = 5 := by omega
      subst i
      exact (Native.Proofs.lane_ports w ⟨5, bound⟩).2.trans actual.2
  · simpa [Operation, Fin.getElem_fin] using effects.mix ⟨1, iteration, round⟩ false read rfl
  · simpa [Operation, Fin.getElem_fin] using effects.mix ⟨2, iteration, round⟩ true read rfl
  · have actual := effects.theta ⟨3, iteration, round⟩ read rfl
    apply Vector.ext
    intro i bound
    simp only [Native.writtenLanes, Vector.getElem_ofFn, Fin.getElem_fin]
    split_ifs with first
    · exact actual.1 ⟨i, first⟩
    · have same : i = 5 := by omega
      subst i
      exact actual.2
  · have actual := effects.rho ⟨4, iteration, round⟩ read rfl
    apply Vector.ext
    intro i bound
    simp only [Native.writtenLanes, Vector.getElem_ofFn, Fin.getElem_fin]
    split_ifs with first
    · exact actual.1 ⟨i, first⟩
    · have same : i = 5 := by omega
      subst i
      exact actual.2
  · simpa [Operation, Fin.getElem_fin] using effects.chiFirst ⟨5, iteration, round⟩ read rfl
  · simpa [Operation, Fin.getElem_fin] using effects.chiSecond ⟨6, iteration, round⟩ read rfl

theorem low_half (low high : Word) :
    half (low.value + 2 ^ 32 * high.value) false = low.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp [half, Word.toBitVec, Nat.add_mod]

theorem high_half {low high : Word} (bound : low.Bounded) :
    half (low.value + 2 ^ 32 * high.value) true = high.toBitVec := by
  have quotient : (low.value + 2 ^ 32 * high.value) / 2 ^ 32 = high.value := by
    have small := Word.value_lt bound
    norm_num [wordModulus] at small
    norm_num only [Nat.reducePow]
    omega
  simpa [half, Word.toBitVec] using congrArg (BitVec.ofNat 32) quotient

theorem lane_bound {low high : Word} (lowBound : low.Bounded) (highBound : high.Bounded) :
    low.value + 2 ^ 32 * high.value < 2 ^ 64 := by
  have small := Word.value_lt lowBound
  have large := Word.value_lt highBound
  norm_num [wordModulus] at small large ⊢
  omega

theorem full_controller {before after : State} (execution : Executes before after) :
    ∃ control : BitVec 32, (Cell.register 10).read before = .ok control before ∧
      control.toNat < 2048 := by
  obtain ⟨input, _, _, _, reads, _, _⟩ := execution
  have bound : input.control.packed < 2048 := by
    unfold ControlState.packed
    have := input.control.mode.isLt
    have := input.control.iteration.isLt
    have := input.control.round.isLt
    omega
  refine ⟨BitVec.ofNat 32 input.control.packed, ?_, ?_⟩
  · simpa [cells, Call.reads, values, Fin.getElem_fin] using reads 0
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : input.control.packed < 2 ^ 32)]
      using bound

end Airbender.Keccak.Call.Proofs
