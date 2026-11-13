module
public import Proven.KeccakSplit.Trace.RVAtomicWrites
public import Human.Trace.Workers.KeccakSplit.RVCall
public import Human.Circuits.KeccakSplit.Native
public import Proven.KeccakSplit.Setup.Facts

@[expose] public section

/-! RV twins of the row-level steps of `RowExecution.lean`, shared by the three split workers' RV `executes` proofs:
    a row's RV history of exactly its accesses, from a state where its ports read their native values, is one
    documented call (`Call.RVExecutesAt`). RAM cells include the shadow RAM below `ROM_END`. -/

namespace Airbender.Keccak.Split.RowProofs
open Airbender.Trace Airbender.Trace.Proofs Airbender.Arithmetic
set_option warningAsError true

/-- A control word read through x10 identifies the call whose arguments hold. -/
theorem rv_control_index {actual index : Fin 361} {before : RV.State}
    (arguments : Call.RVArgumentsAt index.val before)
    (read : (Cell.register 10).readRV before = some (Word.mk (controlAt actual.val) 0).toBitVec) :
    actual = index := by
  obtain ⟨control, _, controlRead, _, controlWord, _⟩ := arguments
  rw [controlWord] at controlRead
  have bits := Option.some.inj (read.symm.trans controlRead)
  have numeric := congrArg BitVec.toNat bits
  have a := SetupProofs.controlAt_lt actual.isLt
  have b := SetupProofs.controlAt_lt index.isLt
  simp only [Word.toBitVec, Word.value, limbBase, mul_zero, add_zero, BitVec.toNat_ofNat] at numeric
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at numeric
  exact Fin.ext (SetupProofs.controlAt_inj actual.isLt index.isLt numeric)

/-- A cell observed at a port's address is the cell with that address code. -/
theorem rv_observed_read {port : MemoryPort} {w : Nat → ZMod babyBearModulus} {before : RV.State}
    {target : Cell} (address : port.address.code w = target.addressCode)
    (observed : ∃ cell : Cell, cell.addressCode = port.address.code w ∧
      cell.readRV before = some (readToken w port).word.toBitVec) :
    target.readRV before = some (readToken w port).word.toBitVec := by
  obtain ⟨cell, code, read⟩ := observed
  rwa [cell_address_injective (code.trans address)] at read

/-- The RV step of a row whose port values project onto the call's writes. -/
theorem rv_executes_of_projection (row : Native.Row babyBearModulus) (index : Fin 361)
    {before after : RV.State} {cells : List Cell} {events : List MemoryAccess}
    (arguments : Call.RVArgumentsAt index.val before) (pointer : BitVec 32)
    (pointerRead : (Cell.register 11).readRV before = some pointer) (input : Vector Nat 7)
    (lanes : ∀ lane : Fin 7, lane.val < Call.slotCount (kindAt index.val) →
      input[lane] < 2 ^ 64 ∧
      (Call.laneCell pointer (Call.slots index)[lane] false).readRV before = some (Call.half input[lane] false) ∧
      (Call.laneCell pointer (Call.slots index)[lane] true).readRV before = some (Call.half input[lane] true))
    (history : RVHistory cells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (projection : (row.memorySteps.map transferEvent).map
        (fun event => (event.2.1, memoryWord event.2.2.2)) =
      (Call.writes index pointer (Call.result index input)).map
        (fun entry => (entry.1.addressCode, entry.2))) :
    Call.RVExecutesAt index before after := by
  refine ⟨pointer, input, arguments, pointerRead, lanes, ?_⟩
  apply rv_atomic_writes_of_history history
  exact (permutation.map _).trans (List.Perm.of_eq projection)

end Airbender.Keccak.Split.RowProofs
