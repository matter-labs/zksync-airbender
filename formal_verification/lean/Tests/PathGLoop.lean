/- Accepted native G calls compose with the branch/jump loop in three full
Sail executions. Scratch and protected-message stores retain their actual
memory effects; only the baseline and scratch variants group the full protocol. -/
import Tests.PathGLoopNative
import Tests.PathGLoopInputs
import Airbender.Review.Trace.UnifiedReduced.PathSpanExecution
import Airbender.Proofs.Trace.MemoryFrame

namespace Tests.PathGLoop
open Airbender Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
open Airbender.UnifiedReduced.Caller Airbender.UnifiedReduced.Caller.Proofs
open Tests.PathGLoopProgram Tests.PathGLoopNative
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

-- The complete G protocol has56 calls; this proof supplies only the
-- positivity required by Fin's existing numeral instance.
local instance : NeZero ((Delegation.Caller.HashSpan.blakeG true).callCount) :=
  ⟨by decide⟩

private theorem closed_false {proposition : Prop} [Decidable proposition]
    (fact : proposition) (checked : decide proposition = false) : False :=
  (of_decide_eq_false checked) fact

private def cpu (variant : Variant) (i : Fin 228) : Row babyBearModulus UnifiedFamily :=
  ⟨.machine, machineAssignment variant i⟩

private theorem cpu_clock (variant : Variant) (i : Fin 228) :
    Delegation.Caller.startClock (cpu variant i) = 4 + 4 * i.val := by
  fin_cases i <;> cases variant <;> rfl

private theorem cpu_pc (variant : Variant) (i : Fin 228) :
    (cpu variant i).start.word.toBitVec = (codeEntry variant (rowCodeIndex i)).pc := by
  fin_cases i <;> cases variant <;> rfl

private theorem ordinary_registry (variant : Variant) (i : Fin 228)
    (ordinary : isCaller i = false) :
    ∃ entry ∈ ordinaryProgram variant,
      entry.pc = (cpu variant i).start.word.toBitVec ∧
      entry.instruction = (codeEntry variant (rowCodeIndex i)).instruction := by
  let code := rowCodeIndex i
  have bound : code.val < 12 := code.isLt
  have excluded : ¬ (code.val = 6 ∨ code.val = 11) := of_decide_eq_false ordinary
  have notSix : code.val ≠ 6 := fun equal => excluded (Or.inl equal)
  have notEleven : code.val ≠ 11 := fun equal => excluded (Or.inr equal)
  let index : Fin 10 := ⟨if code.val < 6 then code.val else code.val - 1, by
    split_ifs <;> omega⟩
  have equal : ordinaryCodeIndex index = code := by
    apply Fin.ext
    dsimp only [ordinaryCodeIndex, index]
    split_ifs <;> omega
  refine ⟨ordinaryEntry variant index, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  · change (codeEntry variant (ordinaryCodeIndex index)).pc =
      (cpu variant i).start.word.toBitVec
    rw [equal, cpu_pc]
  · change (codeEntry variant (ordinaryCodeIndex index)).instruction =
      (codeEntry variant (rowCodeIndex i)).instruction
    rw [equal]

private theorem instruction_at (variant : Variant) (i : Fin 228)
    (ordinary : isCaller i = false) :
    PathInstructionPreparation (data variant) (ordinaryProgram variant) (8 + 4 * i.val)
      (codeEntry variant (rowCodeIndex i)).instruction := by
  refine ⟨?_, by have := i.isLt; change 8 ≤ 8 + 4 * i.val; omega,
    by have := i.isLt; change 8 + 4 * i.val ≤ 916; omega⟩
  intro row member last
  change row ∈ machineRows variant at member
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
  change Delegation.Caller.startClock (cpu variant j) + 4 = _ at last
  rw [cpu_clock] at last
  have equal : j = i := Fin.ext (by omega)
  subst j
  exact ordinary_registry variant i ordinary

private theorem caller_at_row (variant : Variant) (i : Fin 228)
    (called : isCaller i = true) :
    PathCallerPreparation (data variant) (8 + 4 * i.val) .blakeG := by
  refine ⟨?_, by have := i.isLt; change 8 ≤ 8 + 4 * i.val; omega,
    by have := i.isLt; change 8 + 4 * i.val ≤ 916; omega⟩
  intro row member last
  change row ∈ machineRows variant at member
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
  change Delegation.Caller.startClock (cpu variant j) + 4 = _ at last
  rw [cpu_clock] at last
  have equal : j = i := Fin.ext (by omega)
  subst j
  change ∃ entry ∈ callerProgram,
    entry.pc = (cpu variant i).start.word.toBitVec ∧ entry.data.family = .blakeG
  rw [cpu_pc]
  have choices : (rowCodeIndex i).val = 6 ∨ (rowCodeIndex i).val = 11 :=
    of_decide_eq_true called
  rcases choices with first | last
  · have code : rowCodeIndex i = (6 : Fin 12) := Fin.ext first
    rw [code]
    exact ⟨callerEntry 0, by simp [callerProgram], rfl, rfl⟩
  · have code : rowCodeIndex i = (11 : Fin 12) := Fin.ext last
    rw [code]
    exact ⟨callerEntry 1, by simp [callerProgram], rfl, rfl⟩

private theorem caller_at (variant : Variant) (i : Fin 56) :
    PathCallerPreparation (data variant) (callStart i + 4) .blakeG := by
  have called : isCaller (callRow i) = true := by fin_cases i <;> decide +kernel
  have scope := caller_at_row variant (callRow i) called
  convert scope using 1
  simp only [callStart]
  omega

private theorem late_code_index (i : Fin 228) (late : 6 ≤ i.val) :
    6 ≤ (rowCodeIndex i).val := by
  have bound := i.isLt
  have remainder := Nat.mod_lt (i.val - 6) (by decide : 0 < 4)
  dsimp only [rowCodeIndex]
  split_ifs <;> omega

private theorem code_pointer_frame (variant : Variant) (code : Fin 12)
    (late : 6 ≤ code.val) (notSix : code.val ≠ 6) (notEleven : code.val ≠ 11)
    {register : BitVec 5} (pointer : register = 10 ∨ register = 11) :
    PathRegisterFrame register (codeEntry variant code).instruction := by
  have notOne : (1 : BitVec 5) ≠ register := by
    rcases pointer with rfl | rfl <;> decide
  have notFive : (5 : BitVec 5) ≠ register := by
    rcases pointer with rfl | rfl <;> decide
  have notTwo : (2 : BitVec 5) ≠ register := by
    rcases pointer with rfl | rfl <;> decide
  fin_cases code
  · norm_num at late
  · norm_num at late
  · norm_num at late
  · norm_num at late
  · norm_num at late
  · norm_num at late
  · exact (notSix rfl).elim
  · exact .jal 12 1 notOne
  · exact .write (.arithmetic (.addi 0xfff 5 5)) (by decide) notFive
  · exact .branch 0x1fec 0 5 .BNE
  · cases variant with
    | baseline => exact .write (.arithmetic (.addi 0 2 2)) (by decide) notTwo
    | scratch => exact .store 256 2 10
    | protectedMessage => exact .store 0 2 11
  · exact (notEleven rfl).elim

private theorem frame_at (variant : Variant) (i : Fin 228) (late : 6 ≤ i.val)
    {register : BitVec 5} (pointer : register = 10 ∨ register = 11) :
    PathRegisterCodeFrame (data variant) (ordinaryProgram variant) (8 + 4 * i.val) register := by
  cases called : isCaller i with
  | false =>
    have excluded : ¬ ((rowCodeIndex i).val = 6 ∨ (rowCodeIndex i).val = 11) :=
      of_decide_eq_false called
    exact .ordinary (instruction_at variant i called)
      (code_pointer_frame variant (rowCodeIndex i) (late_code_index i late)
        (fun equal => excluded (Or.inl equal))
        (fun equal => excluded (Or.inr equal)) pointer)
  | true =>
    refine .caller (caller_at_row variant i called) ?_
    rcases pointer with rfl | rfl
    · change (10 : BitVec 5) ≠ 12
      decide
    · change (11 : BitVec 5) ≠ 12
      decide

private theorem store_code_occurrence (i : Fin 228) :
    (rowCodeIndex i).val = 10 ↔ i.val = 226 := by
  have bound := i.isLt
  have remainder := Nat.mod_lt (i.val - 6) (by decide : 0 < 4)
  dsimp only [rowCodeIndex]
  split_ifs <;> omega

private theorem code_ram_readonly (variant : Variant) (code : Fin 12)
    (notSix : code.val ≠ 6) (notEleven : code.val ≠ 11)
    (baseline : code.val = 10 → variant = .baseline) :
    PathRamReadOnlyInstruction (codeEntry variant code).instruction := by
  fin_cases code
  · exact .write (.arithmetic (.lui 0x02000 10))
  · exact .write (.arithmetic (.addi 64 10 11))
  · exact .write (.arithmetic (.addi 128 0 12))
  · exact .write (.arithmetic (.addi 55 0 5))
  · exact .write (.arithmetic (.addi 7 0 2))
  · exact .jal 108 0
  · exact (notSix rfl).elim
  · exact .jal 12 1
  · exact .write (.arithmetic (.addi 0xfff 5 5))
  · exact .branch 0x1fec 0 5 .BNE
  · have equal : variant = .baseline := baseline rfl
    subst variant
    exact .write (.arithmetic (.addi 0 2 2))
  · exact (notEleven rfl).elim

private theorem ram_readonly_at (variant : Variant) (i : Fin 228)
    (ordinary : isCaller i = false) (notStore : isStore variant i = false) :
    PathRamReadOnlyInstruction (codeEntry variant (rowCodeIndex i)).instruction := by
  have excluded : ¬ ((rowCodeIndex i).val = 6 ∨ (rowCodeIndex i).val = 11) :=
    of_decide_eq_false ordinary
  have unstored : ¬ (i.val = 226 ∧ variant ≠ .baseline) :=
    of_decide_eq_false notStore
  apply code_ram_readonly variant (rowCodeIndex i)
    (fun equal => excluded (Or.inl equal))
    (fun equal => excluded (Or.inr equal))
  intro code
  have occurrence : i.val = 226 := (store_code_occurrence i).mp code
  by_contra different
  exact unstored ⟨occurrence, different⟩

private theorem control0 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 28 12 128 := by
  have literal : PathRegisterDataflow (data variant) (ordinaryProgram variant) 16 12 128 := by
    apply PathRegisterDataflow.literal (literal := .addi 128)
    have scope := instruction_at variant 2 (by decide)
    exact ⟨scope.code, scope.afterInitial, scope.beforeTerminal⟩
  have one : PathControllerDataflow (data variant) (ordinaryProgram variant) 20 12 128 :=
    .frame (.ordinary literal) (instruction_at variant 3 (by decide))
      (.write (.arithmetic (.addi 55 0 5)) (by decide) (by decide))
  have two : PathControllerDataflow (data variant) (ordinaryProgram variant) 24 12 128 :=
    .frame one (instruction_at variant 4 (by decide))
      (.write (.arithmetic (.addi 7 0 2)) (by decide) (by decide))
  exact .frame two (instruction_at variant 5 (by decide)) (.jal 108 0 (by decide))

private theorem control1 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 44 12 129 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 32 12 129 :=
    .hashAdvance ⟨.blakeG true, 0⟩ (control0 variant) (caller_at variant 0)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 36 12 129 :=
    .frame call (instruction_at variant 7 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 40 12 129 :=
    .frame jump (instruction_at variant 8 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 9 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control2 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 60 12 130 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 48 12 130 :=
    .hashAdvance ⟨.blakeG true, 1⟩ (control1 variant) (caller_at variant 1)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 52 12 130 :=
    .frame call (instruction_at variant 11 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 56 12 130 :=
    .frame jump (instruction_at variant 12 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 13 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control3 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 76 12 131 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 64 12 131 :=
    .hashAdvance ⟨.blakeG true, 2⟩ (control2 variant) (caller_at variant 2)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 68 12 131 :=
    .frame call (instruction_at variant 15 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 72 12 131 :=
    .frame jump (instruction_at variant 16 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 17 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control4 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 92 12 132 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 80 12 132 :=
    .hashAdvance ⟨.blakeG true, 3⟩ (control3 variant) (caller_at variant 3)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 84 12 132 :=
    .frame call (instruction_at variant 19 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 88 12 132 :=
    .frame jump (instruction_at variant 20 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 21 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control5 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 108 12 133 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 96 12 133 :=
    .hashAdvance ⟨.blakeG true, 4⟩ (control4 variant) (caller_at variant 4)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 100 12 133 :=
    .frame call (instruction_at variant 23 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 104 12 133 :=
    .frame jump (instruction_at variant 24 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 25 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control6 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 124 12 134 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 112 12 134 :=
    .hashAdvance ⟨.blakeG true, 5⟩ (control5 variant) (caller_at variant 5)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 116 12 134 :=
    .frame call (instruction_at variant 27 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 120 12 134 :=
    .frame jump (instruction_at variant 28 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 29 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control7 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 140 12 135 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 128 12 135 :=
    .hashAdvance ⟨.blakeG true, 6⟩ (control6 variant) (caller_at variant 6)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 132 12 135 :=
    .frame call (instruction_at variant 31 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 136 12 135 :=
    .frame jump (instruction_at variant 32 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 33 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control8 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 156 12 136 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 144 12 136 :=
    .hashAdvance ⟨.blakeG true, 7⟩ (control7 variant) (caller_at variant 7)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 148 12 136 :=
    .frame call (instruction_at variant 35 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 152 12 136 :=
    .frame jump (instruction_at variant 36 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 37 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control9 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 172 12 137 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 160 12 137 :=
    .hashAdvance ⟨.blakeG true, 8⟩ (control8 variant) (caller_at variant 8)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 164 12 137 :=
    .frame call (instruction_at variant 39 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 168 12 137 :=
    .frame jump (instruction_at variant 40 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 41 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control10 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 188 12 138 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 176 12 138 :=
    .hashAdvance ⟨.blakeG true, 9⟩ (control9 variant) (caller_at variant 9)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 180 12 138 :=
    .frame call (instruction_at variant 43 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 184 12 138 :=
    .frame jump (instruction_at variant 44 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 45 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control11 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 204 12 139 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 192 12 139 :=
    .hashAdvance ⟨.blakeG true, 10⟩ (control10 variant) (caller_at variant 10)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 196 12 139 :=
    .frame call (instruction_at variant 47 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 200 12 139 :=
    .frame jump (instruction_at variant 48 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 49 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control12 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 220 12 140 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 208 12 140 :=
    .hashAdvance ⟨.blakeG true, 11⟩ (control11 variant) (caller_at variant 11)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 212 12 140 :=
    .frame call (instruction_at variant 51 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 216 12 140 :=
    .frame jump (instruction_at variant 52 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 53 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control13 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 236 12 141 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 224 12 141 :=
    .hashAdvance ⟨.blakeG true, 12⟩ (control12 variant) (caller_at variant 12)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 228 12 141 :=
    .frame call (instruction_at variant 55 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 232 12 141 :=
    .frame jump (instruction_at variant 56 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 57 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control14 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 252 12 142 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 240 12 142 :=
    .hashAdvance ⟨.blakeG true, 13⟩ (control13 variant) (caller_at variant 13)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 244 12 142 :=
    .frame call (instruction_at variant 59 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 248 12 142 :=
    .frame jump (instruction_at variant 60 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 61 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control15 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 268 12 143 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 256 12 143 :=
    .hashAdvance ⟨.blakeG true, 14⟩ (control14 variant) (caller_at variant 14)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 260 12 143 :=
    .frame call (instruction_at variant 63 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 264 12 143 :=
    .frame jump (instruction_at variant 64 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 65 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control16 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 284 12 144 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 272 12 144 :=
    .hashAdvance ⟨.blakeG true, 15⟩ (control15 variant) (caller_at variant 15)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 276 12 144 :=
    .frame call (instruction_at variant 67 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 280 12 144 :=
    .frame jump (instruction_at variant 68 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 69 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control17 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 300 12 145 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 288 12 145 :=
    .hashAdvance ⟨.blakeG true, 16⟩ (control16 variant) (caller_at variant 16)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 292 12 145 :=
    .frame call (instruction_at variant 71 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 296 12 145 :=
    .frame jump (instruction_at variant 72 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 73 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control18 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 316 12 146 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 304 12 146 :=
    .hashAdvance ⟨.blakeG true, 17⟩ (control17 variant) (caller_at variant 17)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 308 12 146 :=
    .frame call (instruction_at variant 75 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 312 12 146 :=
    .frame jump (instruction_at variant 76 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 77 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control19 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 332 12 147 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 320 12 147 :=
    .hashAdvance ⟨.blakeG true, 18⟩ (control18 variant) (caller_at variant 18)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 324 12 147 :=
    .frame call (instruction_at variant 79 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 328 12 147 :=
    .frame jump (instruction_at variant 80 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 81 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control20 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 348 12 148 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 336 12 148 :=
    .hashAdvance ⟨.blakeG true, 19⟩ (control19 variant) (caller_at variant 19)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 340 12 148 :=
    .frame call (instruction_at variant 83 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 344 12 148 :=
    .frame jump (instruction_at variant 84 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 85 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control21 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 364 12 149 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 352 12 149 :=
    .hashAdvance ⟨.blakeG true, 20⟩ (control20 variant) (caller_at variant 20)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 356 12 149 :=
    .frame call (instruction_at variant 87 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 360 12 149 :=
    .frame jump (instruction_at variant 88 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 89 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control22 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 380 12 150 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 368 12 150 :=
    .hashAdvance ⟨.blakeG true, 21⟩ (control21 variant) (caller_at variant 21)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 372 12 150 :=
    .frame call (instruction_at variant 91 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 376 12 150 :=
    .frame jump (instruction_at variant 92 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 93 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control23 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 396 12 151 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 384 12 151 :=
    .hashAdvance ⟨.blakeG true, 22⟩ (control22 variant) (caller_at variant 22)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 388 12 151 :=
    .frame call (instruction_at variant 95 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 392 12 151 :=
    .frame jump (instruction_at variant 96 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 97 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control24 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 412 12 152 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 400 12 152 :=
    .hashAdvance ⟨.blakeG true, 23⟩ (control23 variant) (caller_at variant 23)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 404 12 152 :=
    .frame call (instruction_at variant 99 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 408 12 152 :=
    .frame jump (instruction_at variant 100 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 101 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control25 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 428 12 153 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 416 12 153 :=
    .hashAdvance ⟨.blakeG true, 24⟩ (control24 variant) (caller_at variant 24)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 420 12 153 :=
    .frame call (instruction_at variant 103 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 424 12 153 :=
    .frame jump (instruction_at variant 104 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 105 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control26 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 444 12 154 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 432 12 154 :=
    .hashAdvance ⟨.blakeG true, 25⟩ (control25 variant) (caller_at variant 25)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 436 12 154 :=
    .frame call (instruction_at variant 107 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 440 12 154 :=
    .frame jump (instruction_at variant 108 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 109 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control27 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 460 12 155 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 448 12 155 :=
    .hashAdvance ⟨.blakeG true, 26⟩ (control26 variant) (caller_at variant 26)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 452 12 155 :=
    .frame call (instruction_at variant 111 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 456 12 155 :=
    .frame jump (instruction_at variant 112 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 113 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control28 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 476 12 156 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 464 12 156 :=
    .hashAdvance ⟨.blakeG true, 27⟩ (control27 variant) (caller_at variant 27)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 468 12 156 :=
    .frame call (instruction_at variant 115 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 472 12 156 :=
    .frame jump (instruction_at variant 116 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 117 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control29 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 492 12 157 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 480 12 157 :=
    .hashAdvance ⟨.blakeG true, 28⟩ (control28 variant) (caller_at variant 28)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 484 12 157 :=
    .frame call (instruction_at variant 119 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 488 12 157 :=
    .frame jump (instruction_at variant 120 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 121 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control30 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 508 12 158 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 496 12 158 :=
    .hashAdvance ⟨.blakeG true, 29⟩ (control29 variant) (caller_at variant 29)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 500 12 158 :=
    .frame call (instruction_at variant 123 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 504 12 158 :=
    .frame jump (instruction_at variant 124 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 125 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control31 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 524 12 159 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 512 12 159 :=
    .hashAdvance ⟨.blakeG true, 30⟩ (control30 variant) (caller_at variant 30)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 516 12 159 :=
    .frame call (instruction_at variant 127 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 520 12 159 :=
    .frame jump (instruction_at variant 128 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 129 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control32 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 540 12 160 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 528 12 160 :=
    .hashAdvance ⟨.blakeG true, 31⟩ (control31 variant) (caller_at variant 31)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 532 12 160 :=
    .frame call (instruction_at variant 131 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 536 12 160 :=
    .frame jump (instruction_at variant 132 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 133 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control33 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 556 12 161 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 544 12 161 :=
    .hashAdvance ⟨.blakeG true, 32⟩ (control32 variant) (caller_at variant 32)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 548 12 161 :=
    .frame call (instruction_at variant 135 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 552 12 161 :=
    .frame jump (instruction_at variant 136 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 137 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control34 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 572 12 162 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 560 12 162 :=
    .hashAdvance ⟨.blakeG true, 33⟩ (control33 variant) (caller_at variant 33)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 564 12 162 :=
    .frame call (instruction_at variant 139 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 568 12 162 :=
    .frame jump (instruction_at variant 140 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 141 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control35 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 588 12 163 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 576 12 163 :=
    .hashAdvance ⟨.blakeG true, 34⟩ (control34 variant) (caller_at variant 34)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 580 12 163 :=
    .frame call (instruction_at variant 143 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 584 12 163 :=
    .frame jump (instruction_at variant 144 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 145 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control36 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 604 12 164 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 592 12 164 :=
    .hashAdvance ⟨.blakeG true, 35⟩ (control35 variant) (caller_at variant 35)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 596 12 164 :=
    .frame call (instruction_at variant 147 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 600 12 164 :=
    .frame jump (instruction_at variant 148 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 149 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control37 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 620 12 165 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 608 12 165 :=
    .hashAdvance ⟨.blakeG true, 36⟩ (control36 variant) (caller_at variant 36)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 612 12 165 :=
    .frame call (instruction_at variant 151 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 616 12 165 :=
    .frame jump (instruction_at variant 152 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 153 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control38 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 636 12 166 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 624 12 166 :=
    .hashAdvance ⟨.blakeG true, 37⟩ (control37 variant) (caller_at variant 37)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 628 12 166 :=
    .frame call (instruction_at variant 155 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 632 12 166 :=
    .frame jump (instruction_at variant 156 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 157 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control39 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 652 12 167 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 640 12 167 :=
    .hashAdvance ⟨.blakeG true, 38⟩ (control38 variant) (caller_at variant 38)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 644 12 167 :=
    .frame call (instruction_at variant 159 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 648 12 167 :=
    .frame jump (instruction_at variant 160 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 161 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control40 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 668 12 168 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 656 12 168 :=
    .hashAdvance ⟨.blakeG true, 39⟩ (control39 variant) (caller_at variant 39)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 660 12 168 :=
    .frame call (instruction_at variant 163 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 664 12 168 :=
    .frame jump (instruction_at variant 164 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 165 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control41 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 684 12 169 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 672 12 169 :=
    .hashAdvance ⟨.blakeG true, 40⟩ (control40 variant) (caller_at variant 40)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 676 12 169 :=
    .frame call (instruction_at variant 167 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 680 12 169 :=
    .frame jump (instruction_at variant 168 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 169 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control42 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 700 12 170 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 688 12 170 :=
    .hashAdvance ⟨.blakeG true, 41⟩ (control41 variant) (caller_at variant 41)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 692 12 170 :=
    .frame call (instruction_at variant 171 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 696 12 170 :=
    .frame jump (instruction_at variant 172 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 173 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control43 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 716 12 171 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 704 12 171 :=
    .hashAdvance ⟨.blakeG true, 42⟩ (control42 variant) (caller_at variant 42)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 708 12 171 :=
    .frame call (instruction_at variant 175 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 712 12 171 :=
    .frame jump (instruction_at variant 176 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 177 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control44 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 732 12 172 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 720 12 172 :=
    .hashAdvance ⟨.blakeG true, 43⟩ (control43 variant) (caller_at variant 43)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 724 12 172 :=
    .frame call (instruction_at variant 179 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 728 12 172 :=
    .frame jump (instruction_at variant 180 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 181 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control45 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 748 12 173 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 736 12 173 :=
    .hashAdvance ⟨.blakeG true, 44⟩ (control44 variant) (caller_at variant 44)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 740 12 173 :=
    .frame call (instruction_at variant 183 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 744 12 173 :=
    .frame jump (instruction_at variant 184 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 185 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control46 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 764 12 174 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 752 12 174 :=
    .hashAdvance ⟨.blakeG true, 45⟩ (control45 variant) (caller_at variant 45)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 756 12 174 :=
    .frame call (instruction_at variant 187 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 760 12 174 :=
    .frame jump (instruction_at variant 188 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 189 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control47 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 780 12 175 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 768 12 175 :=
    .hashAdvance ⟨.blakeG true, 46⟩ (control46 variant) (caller_at variant 46)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 772 12 175 :=
    .frame call (instruction_at variant 191 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 776 12 175 :=
    .frame jump (instruction_at variant 192 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 193 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control48 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 796 12 176 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 784 12 176 :=
    .hashAdvance ⟨.blakeG true, 47⟩ (control47 variant) (caller_at variant 47)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 788 12 176 :=
    .frame call (instruction_at variant 195 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 792 12 176 :=
    .frame jump (instruction_at variant 196 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 197 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control49 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 812 12 177 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 800 12 177 :=
    .hashAdvance ⟨.blakeG true, 48⟩ (control48 variant) (caller_at variant 48)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 804 12 177 :=
    .frame call (instruction_at variant 199 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 808 12 177 :=
    .frame jump (instruction_at variant 200 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 201 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control50 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 828 12 178 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 816 12 178 :=
    .hashAdvance ⟨.blakeG true, 49⟩ (control49 variant) (caller_at variant 49)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 820 12 178 :=
    .frame call (instruction_at variant 203 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 824 12 178 :=
    .frame jump (instruction_at variant 204 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 205 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control51 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 844 12 179 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 832 12 179 :=
    .hashAdvance ⟨.blakeG true, 50⟩ (control50 variant) (caller_at variant 50)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 836 12 179 :=
    .frame call (instruction_at variant 207 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 840 12 179 :=
    .frame jump (instruction_at variant 208 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 209 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control52 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 860 12 180 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 848 12 180 :=
    .hashAdvance ⟨.blakeG true, 51⟩ (control51 variant) (caller_at variant 51)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 852 12 180 :=
    .frame call (instruction_at variant 211 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 856 12 180 :=
    .frame jump (instruction_at variant 212 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 213 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control53 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 876 12 181 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 864 12 181 :=
    .hashAdvance ⟨.blakeG true, 52⟩ (control52 variant) (caller_at variant 52)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 868 12 181 :=
    .frame call (instruction_at variant 215 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 872 12 181 :=
    .frame jump (instruction_at variant 216 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 217 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control54 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 892 12 182 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 880 12 182 :=
    .hashAdvance ⟨.blakeG true, 53⟩ (control53 variant) (caller_at variant 53)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 884 12 182 :=
    .frame call (instruction_at variant 219 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 888 12 182 :=
    .frame jump (instruction_at variant 220 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  exact .frame decrement (instruction_at variant 221 (by decide)) (.branch 0x1fec 0 5 .BNE)

private theorem control55 (variant : Variant) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 912 12 183 := by
  have call : PathControllerDataflow (data variant) (ordinaryProgram variant) 896 12 183 :=
    .hashAdvance ⟨.blakeG true, 54⟩ (control54 variant) (caller_at variant 54)
  have jump : PathControllerDataflow (data variant) (ordinaryProgram variant) 900 12 183 :=
    .frame call (instruction_at variant 223 (by decide)) (.jal 12 1 (by decide))
  have decrement : PathControllerDataflow (data variant) (ordinaryProgram variant) 904 12 183 :=
    .frame jump (instruction_at variant 224 (by decide))
      (.write (.arithmetic (.addi 0xfff 5 5)) (by decide) (by decide))
  have branch : PathControllerDataflow (data variant) (ordinaryProgram variant) 908 12 183 :=
    .frame decrement (instruction_at variant 225 (by decide)) (.branch 0x1fec 0 5 .BNE)
  refine .frame branch (instruction_at variant 226 (by decide)) ?_
  cases variant
  · exact .write (.arithmetic (.addi 0 2 2)) (by decide) (by decide)
  · exact .store 256 2 10
  · exact .store 0 2 11

private theorem control_at (variant : Variant) (i : Fin 56) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) (callStart i) 12
      (HashCallPosition.word ⟨.blakeG true, i⟩).toBitVec := by
  fin_cases i
  · exact control0 variant
  · exact control1 variant
  · exact control2 variant
  · exact control3 variant
  · exact control4 variant
  · exact control5 variant
  · exact control6 variant
  · exact control7 variant
  · exact control8 variant
  · exact control9 variant
  · exact control10 variant
  · exact control11 variant
  · exact control12 variant
  · exact control13 variant
  · exact control14 variant
  · exact control15 variant
  · exact control16 variant
  · exact control17 variant
  · exact control18 variant
  · exact control19 variant
  · exact control20 variant
  · exact control21 variant
  · exact control22 variant
  · exact control23 variant
  · exact control24 variant
  · exact control25 variant
  · exact control26 variant
  · exact control27 variant
  · exact control28 variant
  · exact control29 variant
  · exact control30 variant
  · exact control31 variant
  · exact control32 variant
  · exact control33 variant
  · exact control34 variant
  · exact control35 variant
  · exact control36 variant
  · exact control37 variant
  · exact control38 variant
  · exact control39 variant
  · exact control40 variant
  · exact control41 variant
  · exact control42 variant
  · exact control43 variant
  · exact control44 variant
  · exact control45 variant
  · exact control46 variant
  · exact control47 variant
  · exact control48 variant
  · exact control49 variant
  · exact control50 variant
  · exact control51 variant
  · exact control52 variant
  · exact control53 variant
  · exact control54 variant
  · exact control55 variant

private def pointerValue (register : BitVec 5) : BitVec 32 :=
  if register = 10 then stateAddress else messageAddress

private theorem pointer_boot (variant : Variant) {register : BitVec 5}
    (pointer : register = 10 ∨ register = 11) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) 28 register (pointerValue register) := by
  have state : PathRegisterDataflow (data variant) (ordinaryProgram variant) 8 10 stateAddress := by
    apply PathRegisterDataflow.literal (literal := .lui 0x02000)
    have scope := instruction_at variant 0 (by decide)
    exact ⟨scope.code, scope.afterInitial, scope.beforeTerminal⟩
  have message : PathControllerDataflow (data variant) (ordinaryProgram variant) 12 11 messageAddress := by
    have sum : registerImmediateValue stateAddress (64 : BitVec 12) = messageAddress := by
      decide +kernel
    have addition : PathControllerDataflow (data variant) (ordinaryProgram variant) 12 11
        (registerImmediateValue stateAddress (64 : BitVec 12)) :=
      PathControllerDataflow.addi (cut := 12) (source := (10 : BitVec 5))
        (register := (11 : BitVec 5)) (value := stateAddress) (immediate := (64 : BitVec 12))
        (.ordinary state) (instruction_at variant 1 (by decide)) (by decide)
    simpa only [sum] using addition
  have state12 : PathControllerDataflow (data variant) (ordinaryProgram variant) 12 10 stateAddress :=
    .frame (.ordinary state) (instruction_at variant 1 (by decide))
      (.write (.arithmetic (.addi 64 10 11)) (by decide) (by decide))
  have at12 : PathControllerDataflow (data variant) (ordinaryProgram variant) 12 register (pointerValue register) := by
    rcases pointer with rfl | rfl
    · exact state12
    · exact message
  have at16 : PathControllerDataflow (data variant) (ordinaryProgram variant) 16 register (pointerValue register) :=
    .frame at12 (instruction_at variant 2 (by decide))
      (.write (.arithmetic (.addi 128 0 12)) (by decide)
        (by rcases pointer with rfl | rfl <;> decide))
  have at20 : PathControllerDataflow (data variant) (ordinaryProgram variant) 20 register (pointerValue register) :=
    .frame at16 (instruction_at variant 3 (by decide))
      (.write (.arithmetic (.addi 55 0 5)) (by decide)
        (by rcases pointer with rfl | rfl <;> decide))
  have at24 : PathControllerDataflow (data variant) (ordinaryProgram variant) 24 register (pointerValue register) :=
    .frame at20 (instruction_at variant 4 (by decide))
      (.write (.arithmetic (.addi 7 0 2)) (by decide)
        (by rcases pointer with rfl | rfl <;> decide))
  exact .frame at24 (instruction_at variant 5 (by decide))
    (.jal 108 0 (by rcases pointer with rfl | rfl <;> decide))

private theorem pointer_flow (variant : Variant) {register : BitVec 5}
    (pointer : register = 10 ∨ register = 11) (n : Nat) (lower : 6 ≤ n) (upper : n ≤ 227) :
    PathControllerDataflow (data variant) (ordinaryProgram variant) (4 + 4 * n)
      register (pointerValue register) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n + 1 = 6
    · have same : n = 5 := by omega
      subst n
      exact pointer_boot variant pointer
    have late : 6 ≤ n := by omega
    have prior := ih late (by omega)
    have cut : 4 + 4 * (n + 1) = 8 + 4 * n := by omega
    rw [cut]
    have before : (8 + 4 * n) - 4 = 4 + 4 * n := by omega
    have frame := frame_at variant ⟨n, by omega⟩ late pointer
    cases frame with
    | ordinary scope form => exact .frame (by simpa only [before] using prior) scope form
    | caller scope different => exact .callerFrame (by simpa only [before] using prior) scope different

private theorem g_pointer_frames (variant : Variant) (i : Fin 56) (positive : 0 < i.val)
    {register : BitVec 5} (pointer : register = 10 ∨ register = 11) :
    PathRegisterGapFrames (data variant) (ordinaryProgram variant) 32 (callStart i) register := by
  have aligned : callStart i % 4 = 0 := by fin_cases i <;> decide
  have ordered : 32 ≤ callStart i := by
    dsimp only [callStart, callRow]
    split_ifs <;> omega
  have upper : callStart i ≤ 912 := by fin_cases i <;> decide
  refine ⟨by decide, aligned, ordered, by change 8 ≤ 32; decide,
    by change callStart i ≤ 916; omega, ?_⟩
  intro cut afterLower beforeUpper alignment
  let index : Fin 228 := ⟨(cut - 8) / 4, by omega⟩
  have equal : 8 + 4 * index.val = cut := by dsimp [index]; omega
  have late : 6 ≤ index.val := by dsimp [index]; omega
  simpa only [equal] using frame_at variant index late pointer

private def completeSpan (variant : Variant) : PathCompleteSpan (data variant) (ordinaryProgram variant) where
  span := .blakeG true
  start := callStart
  increasing := by
    intro i j less
    have first := i.isLt
    have last := j.isLt
    change i.val < 56 at first
    change j.val < 56 at last
    change i.val < j.val at less
    dsimp only [callStart, callRow]
    split_ifs <;> omega
  aligned := by intro i; fin_cases i <;> decide
  code := caller_at variant
  control := control_at variant
  gFrames := by
    intro _ i positive
    exact ⟨g_pointer_frames variant i positive (Or.inl rfl),
      g_pointer_frames variant i positive (Or.inr rfl)⟩

/-- Classification inspects only the twelve public code forms. No native
assignment, chronological history or row enumeration enters this proof. -/
private theorem span_code_caller (variant : Variant) (code : Fin 12)
    (positions : (codeEntry variant code).pc = 128 ∨ (codeEntry variant code).pc = 156) :
    code.val = 6 ∨ code.val = 11 := by
  fin_cases code <;> cases variant
  all_goals solve
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact False.elim (closed_false positions (by decide +kernel))

private theorem span_inputs (variant : Variant) :
    PathSpansInputs (data variant) (before variant) [128, 156]
      [0, 4, 8, 12, 16, 20, 132, 144, 148, 152] cells (ordinaryProgram variant)
      [] [completeSpan variant] := by
  have physical := Tests.PathGLoopNative.inputs variant
  refine {
    toProtocolContextInputs := ⟨physical.publicProgram, physical.ordinaryProgram,
      physical.initialization, physical.distinct, physical.aligned, physical.setup, physical.tables⟩
    distinctOccurrences := by change (List.ofFn callStart).Nodup; decide +kernel
    coverage := ?_ }
  have included (i : Fin 56) : (completeSpan variant).occurrence i ∈
      pathProtocolOccurrences ([] : List (PathBigintOccurrence (data variant))) [completeSpan variant] := by
    simp only [pathProtocolOccurrences, List.map_nil, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  intro row member entry entryMember pc
  have choices : entry = callerEntry 0 ∨ entry = callerEntry 1 := by
    change entry ∈ callerProgram at entryMember
    simpa only [callerProgram, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using entryMember
  have family : entry.data.family = .blakeG := by
    rcases choices with rfl | rfl <;> rfl
  have positions : entry.pc = 128 ∨ entry.pc = 156 := by
    rcases choices with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  change row ∈ machineRows variant at member
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
  change entry.pc = (cpu variant j).start.word.toBitVec at pc
  rw [cpu_pc] at pc
  have codePositions : (codeEntry variant (rowCodeIndex j)).pc = 128 ∨
      (codeEntry variant (rowCodeIndex j)).pc = 156 := by
    rw [← pc]
    exact positions
  have called : isCaller j = true :=
    decide_eq_true (span_code_caller variant (rowCodeIndex j) codePositions)
  have selected : UnifiedReduced.Caller.Selected (machineAssignment variant j) :=
    (native_selected_iff variant j).mpr called
  have present : cpu variant j ∈ (data variant).callers := by
    apply List.mem_filter.mpr
    constructor
    · change cpu variant j ∈ machineRows variant
      exact List.mem_map.mpr ⟨j, List.mem_finRange _, rfl⟩
    · exact decide_eq_true selected
  rw [Tests.PathGLoopNative.callers_exact variant] at present
  obtain ⟨i, _, rowEqual⟩ := List.mem_map.mp present
  refine ⟨(completeSpan variant).occurrence i, included i, ?_, ?_⟩
  · change callStart i = Delegation.Caller.startClock (cpu variant j)
    have projected := congrArg Delegation.Caller.startClock rowEqual
    change Delegation.Caller.startClock (cpu variant (callRow i)) =
      Delegation.Caller.startClock (cpu variant j) at projected
    rw [cpu_clock variant (callRow i)] at projected
    exact projected
  · change Delegation.Family.blakeG = entry.data.family
    exact family.symm

private theorem ordinary_pointer_frame (variant : Variant) (i : Fin 228)
    (late : 6 ≤ i.val) (ordinary : isCaller i = false)
    {register : BitVec 5} (pointer : register = 10 ∨ register = 11) :
    PathRegisterFrame register (codeEntry variant (rowCodeIndex i)).instruction := by
  have excluded : ¬ ((rowCodeIndex i).val = 6 ∨ (rowCodeIndex i).val = 11) :=
    of_decide_eq_false ordinary
  exact code_pointer_frame variant (rowCodeIndex i) (late_code_index i late)
    (fun equal => excluded (Or.inl equal)) (fun equal => excluded (Or.inr equal)) pointer

private theorem gap_index (cut : Nat) (lower : 36 ≤ cut)
    (upper : cut ≤ 912) (alignment : cut % 4 = 0)
    (unowned : ¬ ∃ i : Fin 56, cut = callStart i + 4) :
    ∃ i : Fin 228, 6 ≤ i.val ∧ 8 + 4 * i.val = cut ∧ isCaller i = false := by
  let index : Fin 228 := ⟨(cut - 8) / 4, by omega⟩
  have equal : 8 + 4 * index.val = cut := by dsimp [index]; omega
  have late : 6 ≤ index.val := by dsimp [index]; omega
  have beforeLastCaller : index.val ≤ 226 := by omega
  refine ⟨index, late, equal, ?_⟩
  cases called : isCaller index with
  | false => rfl
  | true =>
    have selected : (rowCodeIndex index).val = 6 ∨ (rowCodeIndex index).val = 11 :=
      of_decide_eq_true called
    have remainder := Nat.mod_lt (index.val - 6) (by decide : 0 < 4)
    have geometry : index.val < 226 ∧ (index.val - 6) % 4 = 0 := by
      dsimp only [rowCodeIndex] at selected
      split_ifs at selected <;> omega
    have quotient : (index.val - 6) / 4 < 55 := by omega
    let call : Fin 56 := ⟨(index.val - 6) / 4, Nat.lt_trans quotient (by decide)⟩
    have small : call.val < 55 := quotient
    have row : callRow call = index := by
      apply Fin.ext
      change (if call.val < 55 then 6 + 4 * call.val else 227) = index.val
      rw [if_pos small]
      dsimp only [call]
      omega
    exfalso
    apply unowned
    refine ⟨call, ?_⟩
    dsimp only [callStart]
    rw [row]
    omega

private theorem readonly_gaps : PathSpanReadOnlyGaps (completeSpan .baseline) := by
  constructor
  intro cut lower upper alignment unowned
  change 36 ≤ cut at lower
  change cut ≤ 912 at upper
  obtain ⟨i, late, equal, ordinary⟩ := gap_index cut lower upper alignment unowned
  refine ⟨(codeEntry .baseline (rowCodeIndex i)).instruction,
    by simpa only [equal] using instruction_at .baseline i ordinary,
    ram_readonly_at .baseline i ordinary (by simp [isStore]), ?_⟩
  intro register pointer
  have selected : register = 10 ∨ register = 11 := by
    simpa [completeSpan, path_span_pointer_registers] using pointer
  exact ordinary_pointer_frame .baseline i late ordinary selected

private def scratch_gaps : PathSpanComputedStoreGaps (completeSpan .scratch) where
  pointerValues := pointerValue
  pointerPreparation := by
    intro register pointer
    apply pointer_boot .scratch
    simpa [completeSpan, path_span_pointer_registers] using pointer
  code := by
    intro cut lower upper alignment unowned
    change 36 ≤ cut at lower
    change cut ≤ 912 at upper
    obtain ⟨i, late, equal, ordinary⟩ := gap_index cut lower upper alignment unowned
    refine ⟨(codeEntry .scratch (rowCodeIndex i)).instruction,
      by simpa only [equal] using instruction_at .scratch i ordinary, ?_, ?_⟩
    · intro register pointer
      apply ordinary_pointer_frame .scratch i late ordinary
      simpa [completeSpan, path_span_pointer_registers] using pointer
    · by_cases store : i = 226
      · subst i
        have cutIs : cut = 912 := by omega
        subst cut
        exact .store 256 2 10 stateAddress (by decide)
          (pointer_flow .scratch (Or.inl rfl) 226 (by decide) (by decide)) (by decide +kernel)
      · apply PathRamProtectedInstruction.readOnly
        apply ram_readonly_at .scratch i ordinary
        fin_cases i
        all_goals first | rfl | exact False.elim (store rfl)

private theorem install_registers (entries : List CodeEntry) (state : State) :
    (install entries state).regs = state.regs := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih => exact ih (wordWriteState state entry.pc.toNat entry.bits)

private theorem install_configuration (entries : List CodeEntry) {state : State}
    (configured : FlatMemoryConfiguration state) : FlatMemoryConfiguration (install entries state) := by
  induction entries generalizing state with
  | nil => exact configured
  | cons entry rest ih => exact ih (configuration_word_write configured entry.pc.toNat entry.bits)

private theorem initial_pc (variant : Variant) :
    run (SailRV32.Functions.get_arch_pc ()) (before variant) = .ok 0 (before variant) := by
  apply read_register
  rw [show (before variant).regs = AirbenderInitialization.before.regs from install_registers _ _]
  exact read_register_iff.mp AirbenderInitialization.standalone_profile.profile.pc

private theorem ram_scope (address : BitVec 32) (member : Cell.ram address ∈ cells) :
    ROM.limit ≤ address.toNat ∧ address.toNat + 4 ≤ 2 ^ 30 := by
  have all : cells.all (fun cell => match cell with
      | .register _ => true
      | .ram address => decide (ROM.limit ≤ address.toNat ∧ address.toNat + 4 ≤ 2 ^ 30)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all _ member)

private theorem profile (variant : Variant) :
    RetirementProfile (data variant) (ordinaryProgram variant) (before variant) cells := by
  refine {
    code := ⟨fun address member => (ram_scope address member).1, ?_, ?_⟩
    registers := ?_
    configuration := install_configuration (code variant) AirbenderInitialization.configuration
    ordinary := fun address _ => ordinaryWordAddress_airbender address
    landingPadDisabled := ?_
    loads := ?_ }
  · intro entry member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    fin_cases i <;> cases variant <;> decide +kernel
  · intro entry member
    have choices : entry = callerEntry 0 ∨ entry = callerEntry 1 := by
      simpa [data, callerProgram] using member
    rcases choices with rfl | rfl <;> decide +kernel
  · intro register
    change Cell.register register ∈
      (List.finRange 32).map (fun i => Cell.register (BitVec.ofNat 5 i.val)) ++ _
    apply List.mem_append.mpr
    left
    refine List.mem_map.mpr ⟨⟨register.toNat, register.isLt⟩, List.mem_finRange _, ?_⟩
    simp
  · rintro ⟨entry, member, immediate, source, destination, encoding⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    fin_cases i <;> cases variant <;> cases encoding
  · intro entry member immediate source encoding
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    fin_cases i <;> cases variant <;> cases encoding

private theorem no_bigint_commands (variant : Variant) : BigintCommands (data variant) := by
  intro worker member family
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  cases family

/-- All three programs execute original instructions and complete G calls;
the scratch/protected SW7 effects remain in these actual FullStep executions. -/
theorem full_execution (variant : Variant) :
    Realizes (FullStep (ordinaryProgram variant) (data variant).program)
      (data variant).machine (before variant) cells :=
  path_span_realizes_soundness (Tests.PathGLoopNative.accepted variant) (span_inputs variant)
    (profile variant) (initial_pc variant) (no_bigint_commands variant)

/-- The baseline groups all56 actual positions through real JAL/BNE loops. -/
theorem baseline_grouped :
    PathSpansResult (data .baseline) (ordinaryProgram .baseline) (before .baseline) cells [] [completeSpan .baseline] := by
  apply path_span_execution_soundness (Tests.PathGLoopNative.accepted .baseline) (span_inputs .baseline)
    (profile .baseline) (initial_pc .baseline) (no_bigint_commands .baseline)
  intro span member
  have same : span = completeSpan .baseline := List.mem_singleton.mp member
  subst span
  exact readonly_gaps

/-- SW7 to computed stateBase+256 survives in the whole execution and groups
through the exact32-word protected G state/message domain. -/
theorem scratch_grouped :
    PathSpansResult (data .scratch) (ordinaryProgram .scratch) (before .scratch) cells [] [completeSpan .scratch] := by
  apply path_span_execution_computed_store_soundness (Tests.PathGLoopNative.accepted .scratch) (span_inputs .scratch)
    (profile .scratch) (initial_pc .scratch) (no_bigint_commands .scratch)
  intro span member
  have same : span = completeSpan .scratch := List.mem_singleton.mp member
  subst span
  exact scratch_gaps

private theorem final_address (variant : Variant) (cell : Cell) :
    (final variant cell).address = cell.addressCode := by
  have invariant : ∀ writes : List Write, ∀ token : MemoryToken babyBearModulus,
      token.address = cell.addressCode →
      (writes.foldl (fun token write => if write.cell = cell then
        ⟨cell.addressCode, (write.stamp, 0), Nat.pair write.value.lo write.value.hi⟩ else token) token).address =
        cell.addressCode := by
    intro writes
    induction writes with
    | nil => intro token address; exact address
    | cons write rest ih =>
      intro token address
      apply ih
      dsimp only []
      split_ifs <;> first | rfl | exact address
  exact invariant (prefixWrites variant 228) (old cell) rfl

private theorem read_terminal (variant : Variant) {after : State}
    (terminal : ∀ sink ∈ (data variant).machine.terminalMemory, ∃ actual ∈ cells,
      actual.addressCode = sink.address ∧ actual.read after = .ok sink.word.toBitVec after)
    (cell : Cell) (member : cell ∈ cells) :
    cell.read after = .ok (final variant cell).word.toBitVec after := by
  have sink : final variant cell ∈ (data variant).machine.terminalMemory :=
    List.mem_map.mpr ⟨cell, member, rfl⟩
  obtain ⟨actual, _, address, read⟩ := terminal _ sink
  have same : actual = cell := cell_address_injective (address.trans (final_address variant cell))
  simpa only [same] using read

private theorem initial_zero (variant : Variant) (cell : Cell) (member : cell ∈ cells) :
    cell.read (before variant) = .ok 0 (before variant) := by
  obtain ⟨token, present, value, read, equal⟩ :=
    image_cell_source (Tests.PathGLoopNative.inputs variant).initialization cell member
  change token ∈ cells.map old at present
  obtain ⟨actual, _, rfl⟩ := List.mem_map.mp present
  have address := congrArg MemoryToken.address equal
  change actual.addressCode = cell.addressCode at address
  have same : actual = cell := cell_address_injective address
  subst actual
  have values := congrArg (fun token : MemoryToken babyBearModulus => token.word.toBitVec) equal
  have zero : (0 : BitVec 32) = value := by
    simpa only [old, initial_token_word, Word.ofBitVec_roundtrip] using values
  rw [← zero] at read
  exact read

/-- Native terminal cells are all observed in the public whole execution,
including each real SW7 and the nonzero reduced-mode controller128. -/
def TerminalCells (variant : Variant) : Prop := ∃ after : State,
    Relation.ReflTransGen (FullStep (ordinaryProgram variant) (data variant).program) (before variant) after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok 160 after ∧
    (∀ cell ∈ cells, cell.read after = .ok (final variant cell).word.toBitVec after) ∧
    (Cell.register 1).read after = .ok 136 after ∧
    (Cell.register 5).read after = .ok 0 after ∧
    (Cell.register 12).read after = .ok 128 after ∧
    (Cell.ram scratchAddress).read after = .ok (if variant = .scratch then 7 else 0) after ∧
    (Cell.ram messageAddress).read after = .ok (if variant = .protectedMessage then 7 else 0) after

theorem terminal_cells (variant : Variant) : TerminalCells variant := by
  obtain ⟨after, steps, pc, terminal⟩ := full_execution variant
  have all := read_terminal variant terminal
  have link := all (.register 1) (by decide +kernel)
  have counter := all (.register 5) (by decide +kernel)
  have control := all (.register 12) (by decide +kernel)
  have scratch := all (.ram scratchAddress) (by decide +kernel)
  have message := all (.ram messageAddress) (by decide +kernel)
  have linkValue : (final variant (.register 1)).word.toBitVec = 136 := by cases variant <;> decide +kernel
  have counterValue : (final variant (.register 5)).word.toBitVec = 0 := by cases variant <;> decide +kernel
  have controlValue : (final variant (.register 12)).word.toBitVec = 128 := by cases variant <;> decide +kernel
  have scratchValue : (final variant (.ram scratchAddress)).word.toBitVec =
      (if variant = .scratch then 7 else 0) := by cases variant <;> decide +kernel
  have messageValue : (final variant (.ram messageAddress)).word.toBitVec =
      (if variant = .protectedMessage then 7 else 0) := by cases variant <;> decide +kernel
  rw [linkValue] at link
  rw [counterValue] at counter
  rw [controlValue] at control
  rw [scratchValue] at scratch
  rw [messageValue] at message
  exact ⟨after, steps, pc, all, link, counter, control, scratch, message⟩

/-- The last actual worker has index55/control183, rather than being reset to
index0 to invoke a homogeneous theorem. -/
theorem actual_nonzero_position (variant : Variant) :
    HashCallPosition.NativeBinding ⟨.blakeG true, 55⟩
      (⟨.blakeG, workerAssignment variant 55⟩ : Delegation.Row babyBearModulus) := by
  apply path_span_worker_binding (by decide) (by decide)
    (Tests.PathGLoopNative.accepted variant) (span_inputs variant).toProtocolContextInputs
    (completeSpan variant) (⟨55, by change 55 < 56; decide⟩)
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨55, List.mem_finRange _, rfl⟩, ?_⟩
  cases variant <;> decide +kernel

/-- A real cell with at least one write, all of whose writes have one value,
ends with that value. Earlier reads, writes elsewhere and timestamps stay. -/
private theorem history_uniform_write {domain : List Cell} {events : List MemoryAccess}
    {initial after : State} (history : SailHistory domain events initial after)
    (aligned : ∀ cell ∈ domain, cell.Aligned) (other : Cell) (otherAligned : other.Aligned)
    (nonzero : other ≠ .register 0) (value : BitVec 32)
    (touch : ∃ event ∈ events, event.2.1 = other.addressCode)
    (values : ∀ event ∈ events, event.2.1 = other.addressCode → memoryWord event.2.2.2 = value) :
    other.read after = .ok value after := by
  revert touch values
  induction history with
  | nil => intro touch; obtain ⟨_, absent, _⟩ := touch; cases absent
  | @cons event rest initial middle after past cell member address old written ih =>
    intro touch values
    by_cases same : event.2.1 = other.addressCode
    · have equal : cell = other := cell_address_injective (address.trans same)
      subst cell
      rw [values event List.mem_cons_self same] at written
      obtain ⟨actual, write, read⟩ := cell_write_readback other value middle
        (fun zero => False.elim (nonzero zero))
      have stateEqual := (EStateM.Result.ok.inj (write.symm.trans written)).2
      exact stateEqual ▸ read
    · have touched : ∃ event ∈ rest, event.2.1 = other.addressCode := by
        obtain ⟨found, included, key⟩ := touch
        rcases List.mem_cons.mp included with equal | included
        · subst found
          exact False.elim (same key)
        · exact ⟨found, included, key⟩
      have previous := ih touched (fun e m key => values e (List.mem_cons_of_mem _ m) key)
      have different : other ≠ cell := by
        intro equal
        exact same (address.symm.trans (congrArg Cell.addressCode equal).symm)
      exact cell_write_frame written different (aligned cell member) otherAligned previous

private theorem native_prefix_x11_touched :
    ((data .protectedMessage).mixedSteps.map transferEvent).any (fun event =>
      decide (event.1 ≤ 28 ∧ event.2.1 = (Cell.register 11).addressCode)) = true := by
  decide +kernel

private theorem native_prefix_x11_values :
    ((data .protectedMessage).mixedSteps.map transferEvent).all (fun event =>
      decide (event.1 ≤ 28 → event.2.1 = (Cell.register 11).addressCode →
        memoryWord event.2.2.2 = messageAddress)) = true := by
  decide +kernel

private theorem native_prefix_message_untouched :
    ((data .protectedMessage).mixedSteps.map transferEvent).all (fun event =>
      decide (event.1 ≤ 28 → event.2.1 ≠ (Cell.ram messageAddress).addressCode)) = true := by
  decide +kernel

private theorem prefix_observations {events : List MemoryAccess} {first : State}
    (permutation : events.Perm ((data .protectedMessage).mixedSteps.map transferEvent))
    (past : SailHistory cells (events.filter fun event => decide (event.1 ≤ 28))
      (before .protectedMessage) first) :
    (Cell.register 11).read first = .ok messageAddress first ∧
      (Cell.ram messageAddress).read first = .ok 0 first := by
  have physical := Tests.PathGLoopNative.inputs .protectedMessage
  constructor
  · apply history_uniform_write past physical.aligned (.register 11) trivial (by decide) messageAddress
    · obtain ⟨event, included, chosen⟩ := List.any_eq_true.mp native_prefix_x11_touched
      have facts := of_decide_eq_true chosen
      exact ⟨event, List.mem_filter.mpr ⟨permutation.mem_iff.mpr included, decide_eq_true facts.1⟩, facts.2⟩
    · intro event included key
      obtain ⟨member, chosen⟩ := List.mem_filter.mp included
      have facts := of_decide_eq_true (List.all_eq_true.mp native_prefix_x11_values event
        (permutation.mem_iff.mp member))
      exact facts (of_decide_eq_true chosen) key
  · apply history_cell_frame past physical.aligned (.ram messageAddress)
      (physical.aligned _ (by decide +kernel)) ?_
      (initial_zero .protectedMessage (.ram messageAddress) (by decide +kernel))
    intro event included
    obtain ⟨member, chosen⟩ := List.mem_filter.mp included
    have facts := of_decide_eq_true (List.all_eq_true.mp native_prefix_message_untouched event
      (permutation.mem_iff.mp member))
    exact facts (of_decide_eq_true chosen)

private theorem mapping_impossible {first last : State}
    (pointer : (Cell.register 11).read first = .ok messageAddress first)
    (initialWord : (Cell.ram messageAddress).read first = .ok 0 first)
    (finalWord : (Cell.ram messageAddress).read last = .ok 7 last) :
    ¬ ∃ statePointer messagePointer : BitVec 32, ∃ input message output : Vector Word 16,
      Blake2G.WorkVector.WordMapping first last statePointer messagePointer input message output := by
  rintro ⟨statePointer, messagePointer, input, message, output, mapping⟩
  have fixedPointer : messagePointer = messageAddress :=
    (EStateM.Result.ok.inj (mapping.pointers.2.symm.trans pointer)).1
  have readBefore : (Cell.ram messageAddress).read first = .ok message[0].toBitVec first := by
    simpa [fixedPointer] using (mapping.messageWords (0 : Fin 16)).2
  have readAfter : (Cell.ram messageAddress).read last = .ok message[0].toBitVec last := by
    simpa [fixedPointer] using (mapping.messageUnchanged (0 : Fin 16)).2
  have zero : message[0].toBitVec = 0 := (EStateM.Result.ok.inj (readBefore.symm.trans initialWord)).1
  have seven : message[0].toBitVec = 7 := (EStateM.Result.ok.inj (readAfter.symm.trans finalWord)).1
  exact (by decide : (0 : BitVec 32) ≠ 7) (zero.symm.trans seven)

/-- Actual protected-message SW7 is a counterexample to endpoint WordMapping
and to PathSpanAlgorithmAt. The pointer is anchored by the real pre-span x11,
the old message0 is0 and the final message0 is7. This proves more than rejecting
one proposed syntactic gap certificate; the whole FullStep execution still holds. -/
def ProtectedNegative : Prop := ∃ events : List MemoryAccess, ∃ finalState first last : State,
    events.Perm ((data .protectedMessage).mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧ SailHistory cells events (before .protectedMessage) finalState ∧
    SailHistory cells (events.filter fun event => decide (event.1 ≤ 28)) (before .protectedMessage) first ∧
    SailHistory cells (events.filter fun event => decide (28 < event.1 ∧ event.1 ≤ 916)) first last ∧
    (Cell.register 11).read first = .ok messageAddress first ∧
    (Cell.ram messageAddress).read first = .ok 0 first ∧
    (Cell.ram messageAddress).read last = .ok 7 last ∧
    (¬ ∃ statePointer messagePointer : BitVec 32, ∃ input message output : Vector Word 16,
      Blake2G.WorkVector.WordMapping first last statePointer messagePointer input message output) ∧
    ¬ PathSpanAlgorithmAt (completeSpan .protectedMessage) cells events (before .protectedMessage)

theorem protected_negative : ProtectedNegative := by
  have accepted := Tests.PathGLoopNative.accepted .protectedMessage
  have physical := Tests.PathGLoopNative.inputs .protectedMessage
  have effects := mixed_memory_effects accepted physical
  have ledger := ExternalBoundary.Requests.Proofs.native_binding accepted.toRequestChecks effects.requests
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  have sink := read_terminal .protectedMessage terminal (.ram messageAddress) (by decide +kernel)
  have nativeValue : (final .protectedMessage (.ram messageAddress)).word.toBitVec = 7 := by decide +kernel
  rw [nativeValue] at sink
  have allEvents : (events.filter fun event => decide (event.1 ≤ 916)) = events := by
    apply List.filter_eq_self.mpr
    intro event included
    have bound := (mixed_event_interval accepted physical.publicProgram effects.requests ledger
      (permutation.mem_iff.mp included)).2
    exact decide_eq_true bound
  have observations {first last : State}
      (past : SailHistory cells (events.filter fun event => decide (event.1 ≤ 28))
        (before .protectedMessage) first)
      (current : SailHistory cells (events.filter fun event => decide (28 < event.1 ∧ event.1 ≤ 916)) first last) :
      (Cell.register 11).read first = .ok messageAddress first ∧
      (Cell.ram messageAddress).read first = .ok 0 first ∧
      (Cell.ram messageAddress).read last = .ok 7 last := by
    have beginning := prefix_observations permutation past
    have full := history_prefix_of_window order (by decide : 28 ≤ 916) past current
    rw [allEvents] at full
    have equal : last = finalState := sail_history_deterministic full history
    exact ⟨beginning.1, beginning.2, equal.symm ▸ sink⟩
  obtain ⟨first, last, _, past, current, _⟩ := history_window order history (by decide : 28 ≤ 916)
  have actual := observations past current
  have impossible := mapping_impossible actual.1 actual.2.1 actual.2.2
  refine ⟨events, finalState, first, last, permutation, order, history, past, current,
    actual.1, actual.2.1, actual.2.2, impossible, ?_⟩
  rintro ⟨one, two, prefixHistory, currentHistory, result⟩
  change SailHistory cells (events.filter fun event => decide (event.1 ≤ 28))
    (before .protectedMessage) one at prefixHistory
  change SailHistory cells (events.filter fun event => decide (28 < event.1 ∧ event.1 ≤ 916))
    one two at currentHistory
  have values := observations prefixHistory currentHistory
  have noMapping := mapping_impossible values.1 values.2.1 values.2.2
  obtain ⟨statePointer, messagePointer, input, message, output, mapping, _⟩ := result
  exact noMapping ⟨statePointer, messagePointer, input, message, output, mapping⟩

/-- Whole execution/terminal cells for every variant, both positive grouped
protocols, the actual protected-message endpoint counterexample, and last
position55 binding are all conclusions of these concrete native inputs. -/
theorem complete_regression :
    (∀ variant, TerminalCells variant) ∧
    (∀ variant, Realizes (FullStep (ordinaryProgram variant) (data variant).program)
      (data variant).machine (before variant) cells) ∧
    PathSpansResult (data .baseline) (ordinaryProgram .baseline) (before .baseline) cells [] [completeSpan .baseline] ∧
    PathSpansResult (data .scratch) (ordinaryProgram .scratch) (before .scratch) cells [] [completeSpan .scratch] ∧
    ProtectedNegative ∧
    (∀ variant, HashCallPosition.NativeBinding ⟨.blakeG true, 55⟩
      (⟨.blakeG, workerAssignment variant 55⟩ : Delegation.Row babyBearModulus)) :=
  ⟨terminal_cells, full_execution, baseline_grouped, scratch_grouped, protected_negative, actual_nonzero_position⟩

end Tests.PathGLoop
