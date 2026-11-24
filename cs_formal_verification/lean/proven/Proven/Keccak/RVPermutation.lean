module
public import Proven.Keccak.RVCallSteps
public import Proven.Keccak.CallPermutation
public import Human.Trace.Workers.Keccak.RVCall
public import Proven.Defs.Trace.Workers.Keccak.Call

@[expose] public section

/-! RV twin of `PermutationBinding.permutation_binding_at_boundary`, with the delegate link: the complete special5
    span on `RV.State`s writes Clean's Keccak permutation into actual RV RAM, and its final state is the spec's run of
    the 649 special5 delegations (`RV.calls rvCalls`) from the initial state, up to the spec's PC advance. RAM cells
    include the shadow RAM below `ROM_END`. -/

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

private theorem rv_lanes_at {state : RV.State} {pointer : BitVec 32} {cells : List Cell}
    (tracked : ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Permutation.RVLanesAt state pointer (logicalLanes 0 (rvPhysicalLanes state pointer)) := by
  intro lane
  let physical : Fin 31 := ⟨Controller.physicalLane 0 lane,
    Nat.lt_trans (Controller.Proofs.physical_bound 0 lane) (by decide)⟩
  have lowAligned := aligned _ (tracked physical 0)
  have highAligned := aligned _ (tracked physical 1)
  have four : BitVec.ofNat 32 4 = (4 : BitVec 32) := by decide +kernel
  simp only [physical, Controller.physicalLane, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one, BitVec.ofNat_add, ← BitVec.add_assoc, four] at lowAligned highAligned
  have offset : 8 * (lane.val / 5 + 5 * (lane.val % 5)) = Permutation.laneOffset lane := by rfl
  rw [offset] at lowAligned highAligned
  refine ⟨_, _, rv_encoded_read lowAligned, rv_encoded_read highAligned, ?_, ?_⟩
  · simp only [logicalLanes, Fin.getElem_fin, Vector.getElem_ofFn, rvPhysicalLanes, rvRamLane,
      Controller.physicalLane, offset, rvRamEncoding, Word.ofBitVec_value, Word.ofBitVec_roundtrip]
  · simp only [logicalLanes, Fin.getElem_fin, Vector.getElem_ofFn, rvPhysicalLanes, rvRamLane, rvRamEncoding,
      Word.ofBitVec_value]
    have := (RV.read state.mem (pointer + BitVec.ofNat 32 (8 * (Controller.physicalLane 0 lane))) 4).isLt
    have := (RV.read state.mem (pointer + BitVec.ofNat 32 (8 * (Controller.physicalLane 0 lane)) + 4) 4).isLt
    omega

theorem rv_permutation_binding_at_boundary [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.RVWordMapping initial after pointer input output ∧
        Delegation.RVTraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
        ∃ s', RV.calls rvCalls initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * rvCalls.length))) := by
  obtain ⟨pointer, after, states, count, pointerRead, pointerAligned, tracked, head, last, trace, steps⟩ :=
    rv_call_steps hp inverse accepted inputs tables aligned
  have endpoints : states[0]'(by omega) = after ∧ states[649]'(by omega) = initial := by
    constructor
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at head
      exact Option.some.inj head
    · have finish := List.getLast_of_getLast?_eq_some last
      simpa only [List.getLast_eq_getElem, count] using finish
  let lanes : Fin 650 → LaneState := fun i => rvPhysicalLanes (states[i.val]'(by omega)) pointer
  have result := permutation_of_chain lanes (fun i => (steps i).1)
  have first : lanes 0 = rvPhysicalLanes after pointer := congrArg (rvPhysicalLanes · pointer) endpoints.1
  have final : lanes 649 = rvPhysicalLanes initial pointer := congrArg (rvPhysicalLanes · pointer) endpoints.2
  rw [first, final] at result
  refine ⟨after, pointer, logicalLanes 0 (rvPhysicalLanes initial pointer),
    logicalLanes 0 (rvPhysicalLanes after pointer),
    ⟨pointerRead, rv_lanes_at tracked aligned, rv_lanes_at tracked aligned⟩, trace, result, ?_⟩
  let chron : Nat → RV.State := fun m => states[649 - m]'(by omega)
  have link := calls_replicate_link (k := .keccak) (n := 649) chron (by
    intro m bound x
    obtain ⟨physical, x10, x10', x11, regs, words, rom, input⟩ := steps ⟨648 - m, by omega⟩
    have previous : chron m = states[648 - m + 1]'(by omega) := by
      simp only [chron, show 649 - m = 648 - m + 1 by omega]
    have next : chron (m + 1) = states[648 - m]'(by omega) := by
      simp only [chron, show 649 - (m + 1) = 648 - m by omega]
    have call : 648 - (648 - m) = m := by omega
    rw [previous, next]
    simp only [call] at physical x10 x10'
    exact keccak_call_link ⟨m, bound⟩ pointerAligned physical x10 x10' x11 regs words rom input x)
  have start : chron 0 = initial := by simpa only [chron, Nat.sub_zero] using endpoints.2
  have finish : chron 649 = after := by simpa only [chron, Nat.sub_self] using endpoints.1
  rw [start, finish] at link
  simpa only [rvCalls, List.length_replicate] using link

end Airbender.Keccak.Proofs
