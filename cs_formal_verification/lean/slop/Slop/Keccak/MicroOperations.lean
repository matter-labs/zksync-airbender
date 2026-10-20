import Slop.Keccak.NativeExecution

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def columnState (reads : Vector Nat 6) (column : Fin 5) : Vector Nat 25 :=
  Vector.ofFn fun i => if i.val / 5 = column.val then reads[Fin.ofNat 6 (i.val % 5)] else 0

def microWrites (control : ControlState) (reads : Vector Nat 6) : Vector Nat 6 :=
  if control.mode = 0 then
    let state := iotaState (columnState reads control.iteration) (Fin.ofNat 25 control.round.val)
    Vector.ofFn fun lane : Fin 6 => if h : lane.val < 5 then
      state[5 * control.iteration.val + lane.val]'(by have := control.iteration.isLt; omega)
      else (Specs.Keccak256.thetaC state)[control.iteration]
  else if control.mode = 1 then
    #v[reads[0] ^^^ rotLeft64 reads[2] 1, reads[1], reads[2] ^^^ rotLeft64 reads[4] 1,
      reads[3], reads[4], rotLeft64 reads[0] 1]
  else if control.mode = 2 then
    #v[reads[0], reads[1] ^^^ rotLeft64 reads[3] 1, reads[2], reads[3] ^^^ reads[5],
      reads[4] ^^^ rotLeft64 reads[1] 1, reads[5]]
  else if control.mode = 3 then
    Vector.ofFn fun lane : Fin 6 => if lane.val < 5 then reads[lane] ^^^ reads[5] else reads[5]
  else if control.mode = 4 then
    Vector.ofFn fun lane : Fin 6 => if h : lane.val < 5 then
      rotLeft64 reads[lane] rhoRotations[control.iteration][lane.val] else reads[5]
  else if control.mode = 5 then
    #v[reads[0] ^^^ ((not64 reads[1]) &&& reads[2]),
      reads[1] ^^^ ((not64 reads[2]) &&& reads[3]),
      reads[2], reads[3], (not64 reads[0]) &&& reads[1], reads[0]]
  else
    #v[reads[0] ^^^ reads[3], reads[1] ^^^ ((not64 reads[2]) &&& reads[0]),
      reads[2] ^^^ ((not64 reads[0]) &&& reads[4]), reads[3], reads[4], reads[5]]

private theorem column_reads (reads : Vector Nat 6) (column : Fin 5) (lane : Fin 5) :
    (columnState reads column)[5 * column.val + lane.val] = reads[lane.val]'(by omega) := by
  fin_cases column <;> fin_cases lane <;> simp [columnState]

theorem row_micro_writes {p : Nat} {w : Nat → ZMod p} (effects : Native.RowEffects w)
    (control : ControlState) (roundBound : control.round.val < 25)
    (packed : (w 3).val = control.packed) :
    Native.writtenLanes w = microWrites control (Vector.ofFn (Native.readLane w)) := by
  let reads := Vector.ofFn (Native.readLane w)
  have out : Native.writtenLanes w = Vector.ofFn (Native.writtenLane w) := rfl
  generalize mode : control.mode = selected
  fin_cases selected
  · have decoded : ControlState.mk 0 control.iteration ⟨(Fin.ofNat 25 control.round.val).val, by omega⟩ = control := by
      cases control with
      | mk selected iteration round =>
        simp only [ControlState.mk.injEq]
        exact ⟨mode.symm, True.intro, Fin.ext (Nat.mod_eq_of_lt roundBound)⟩
    have iota := effects.iota (columnState reads control.iteration) control.iteration
      (Fin.ofNat 25 control.round.val) (by simpa only [decoded] using packed) (by
        intro lane
        simpa only [reads, Vector.getElem_ofFn] using (column_reads reads control.iteration lane).symm)
    rw [out]
    apply Vector.ext
    intro i bound
    by_cases small : i < 5
    · simpa [microWrites, mode, reads, Fin.getElem_fin, Native.Proofs.lane_ports, small]
        using iota.1 ⟨i, small⟩
    · have iFive : i = 5 := by omega
      subst i
      simpa [microWrites, mode, reads, Native.Proofs.lane_ports] using iota.2
  · simpa [microWrites, mode, reads] using effects.mix control false packed mode
  · simpa [microWrites, mode, reads] using effects.mix control true packed mode
  · obtain ⟨theta, scratch⟩ := effects.theta control packed mode
    rw [out]
    apply Vector.ext
    intro i bound
    by_cases small : i < 5
    · simpa [microWrites, mode, reads, small] using theta ⟨i, small⟩
    · have iFive : i = 5 := by omega
      subst i
      simpa [microWrites, mode, reads] using scratch
  · obtain ⟨rho, scratch⟩ := effects.rho control packed mode
    rw [out]
    apply Vector.ext
    intro i bound
    by_cases small : i < 5
    · simpa [microWrites, mode, reads, small] using rho ⟨i, small⟩
    · have iFive : i = 5 := by omega
      subst i
      simpa [microWrites, mode, reads] using scratch
  · simpa [microWrites, mode, reads] using effects.chiFirst control packed mode
  · simpa [microWrites, mode, reads] using effects.chiSecond control packed mode

end Airbender.Keccak.Proofs
