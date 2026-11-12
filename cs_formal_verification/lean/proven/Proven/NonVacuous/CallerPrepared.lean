module
public import Proven.NonVacuous.CallerPool
public import Proven.NonVacuous.UnifiedPrepared

@[expose] public section

/-! A six-family caller trace with an ordinary row: `LUI x10, 0x400` at PC 0 (clock 4) writes the bigint worker's
    pointer, then the ADD/SUB caller at PC 4 (clock 8) issues the bigint call, fulfilled by the worker of
    `UnifiedPrepared` (invocation clock nine, x10 read as the LUI wrote it). The state and cells are
    `UnifiedPrepared`'s. The witness that the assumptions of `Delegation.Caller.RVMixedMemorySoundnessClaim` can be
    met with an ordinary program. -/

namespace Airbender.NonVacuous.CallerPrepared
open Trace Arithmetic Verification Delegation Caller
open scoped List

/-- `LUI x10, 0x400` at PC 0 and clock 4: rd = x10 (column 7), immediate high limb 0x40 (9) and result 0x400000
    (34), the ADD selector (10); the second port reads x0 as the first port left it (clock 4, column 27). -/
def prepAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 19 ∨ column = 27 then 4
  else if column = 21 then 8
  else if column = 4 ∨ column = 10 ∨ column = 42 ∨ column = 43 ∨ column = 44 then 1
  else if column = 7 then 10
  else if column = 9 ∨ column = 34 then 64
  else 0

/-- The caller at PC 4 and clock 8: its source port reads x0 as the LUI left it (clock 5, column 23), its x0 write
    follows its x0 read (clock 8, column 35). -/
def callerAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 0 then 4
  else if column = 2 ∨ column = 19 ∨ column = 35 then 8
  else if column = 21 then 12
  else if column = 23 then 5
  else if column = 4 ∨ column = 17 ∨ column = 42 ∨ column = 43 ∨ column = 44 then 1
  else if column = 6 then 0x7CA
  else 0

def prep : Row babyBearModulus PooledFamily := ⟨.addSub, prepAssignment⟩
def caller : Row babyBearModulus PooledFamily := ⟨.addSub, callerAssignment⟩

theorem prep_satisfies : FlatOperation.ConstraintsHoldFlat (environment prepAssignment) AddSub.clockConstraints :=
  holds_append (holds_of_checkOps NonVacuous.Caller.lookup_tables (by kernel_rfl))
    (holds_of_checkOps NonVacuous.Caller.timestamp_tables (by kernel_rfl))

theorem caller_satisfies : FlatOperation.ConstraintsHoldFlat (environment callerAssignment) AddSub.clockConstraints :=
  holds_append (holds_of_checkOps NonVacuous.Caller.lookup_tables (by kernel_rfl))
    (holds_of_checkOps NonVacuous.Caller.timestamp_tables (by kernel_rfl))

abbrev before : RV.State := UnifiedPrepared.before
abbrev cells : List Cell := UnifiedPrepared.cells
noncomputable abbrev workers : MemoryData babyBearModulus := UnifiedPrepared.workers

/-- The ordinary program: the LUI at PC 0. -/
def program : List RVPooledProgramEntry :=
  [⟨0, 0x00400537#32, (arithmeticFields 0 0 10 0x400000#32 1).mapFamily pooledArithmeticFamily⟩]

/-- The caller program: the bigint call at PC 4. -/
def callerProgram : List Caller.RVProgramEntry := [⟨4, 0x7CA01073#32, ⟨.bigint, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩⟩]

theorem program_image : rvProgramImageWith rvPooledDecoderFields before [0] = some program := by kernel_rfl

theorem caller_image : rvProgramImage before [4] = some callerProgram := by kernel_rfl

/-- x0 as the last machine row leaves it. -/
def x0Final : MemoryToken babyBearModulus := destinationToken callerAssignment

noncomputable def machine : PooledTrace babyBearModulus where
  rows := [prep, caller]
  rom := ⟨ROM.table cells (romImageRV before cells), Verification.subwordTable (ROM.wordsRV before)⟩
  initial := prep.start
  terminal := caller.finish
  initialMemory := (Cell.register 0).initialToken 0 :: (Cell.register 10).initialToken 0 ::
    (UnifiedPrepared.worker.memorySteps.map Prod.fst).tail
  terminalMemory := x0Final :: UnifiedPrepared.worker.memorySteps.map Prod.snd

noncomputable def data : RVRequestTrace babyBearModulus := ⟨machine, workers, callerProgram⟩

theorem callers : data.callers = [caller] := by kernel_rfl

theorem callers_ne : data.callers ≠ [] := by
  rw [callers]
  exact List.cons_ne_nil _ _

theorem checks : RVRequestChecks data where
  constraints current member := by
    simp only [data, machine, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact prep_satisfies
    · exact caller_satisfies
  active current member := by
    simp only [data, machine, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  states := by
    change [prep.start, prep.finish, caller.finish].Perm [caller.finish, prep.start, caller.start]
    have link : prep.finish = caller.start := by kernel_rfl
    rw [link]
    exact List.perm_append_comm (l₁ := [_, _]) (l₂ := [_])
  decoded current member := by
    rw [callers, List.mem_singleton] at member
    subst current
    exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩
  workerConstraints current member := by
    simp only [data, workers, UnifiedPrepared.workers, List.mem_singleton] at member
    subst current
    exact holds_append UnifiedPrepared.worker_core UnifiedPrepared.worker_clocks
  workerActive current member := by
    simp only [data, workers, UnifiedPrepared.workers, List.mem_singleton] at member
    subst current
    rfl
  requests := by
    rw [Requests.Matching, RVRequestTrace.calls, RVRequestTrace.fulfillments, callers]
    decide +kernel

theorem mixed_accepted : RVMixedMemoryAccepted data program where
  toRVRequestChecks := checks
  ordinaryDecoded current member notCaller := by
    rw [callers] at notCaller
    simp only [data, machine, List.mem_cons, List.not_mem_nil, or_false] at member notCaller
    rcases member with rfl | rfl
    · exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩
    · exact absurd rfl notCaller
  memory := by
    rw [RVRequestTrace.mixedSteps]
    decide +kernel

theorem mixed_inputs : RVMixedMemoryInputs data program before [4] [0] cells where
  publicProgram := ⟨caller_image, by decide +kernel, by decide +kernel⟩
  initialization := by kernel_rfl
  distinct := by decide +kernel
  aligned := by decide +kernel
  ordinaryProgram := program_image
  wordTable := rfl
  subwordTable := rfl
  tables := rfl
  rounds current member family := by
    simp only [data, workers, UnifiedPrepared.workers, List.mem_singleton] at member
    subst current
    cases family

end Airbender.NonVacuous.CallerPrepared
