import Slop.Sail.ResetState
import Slop.UnifiedReduced.CustomComposition
import Slop.UnifiedReduced.CustomHistory
import Slop.UnifiedReduced.Completeness.Binary
import Slop.BabyBear
import Slop.Sail.WordMemoryState

namespace Tests.UnifiedXorRotate
open Airbender Arithmetic UnifiedReduced Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def rotation (kind : Fin 4) : Nat := #[16, 12, 8, 7][kind.val]!
private def left : BitVec 32 := 0xabcd1234
private def old : BitVec 32 := 0xef015678
private def result (kind : Fin 4) : BitVec 32 := (left ^^^ old).rotateRight (rotation kind)
private def leftByte (i : Nat) : Nat := (left.extractLsb' (8 * i) 8).toNat
private def oldByte (i : Nat) : Nat := (old.extractLsb' (8 * i) 8).toNat
private def witness (kind : Fin 4) : Completeness.Binary :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 5, 0⟩, 0, true, kind.val, false, 1, 2, 2,
    leftByte 0, leftByte 1, leftByte 2, leftByte 3, oldByte 0, oldByte 1, oldByte 2, oldByte 3,
    0x5678, 0xef01⟩
private def assignment (kind : Fin 4) : Nat → ZMod babyBearModulus := (witness kind).honest
private def bits (kind : Fin 4) : BitVec 32 :=
  #[0xc1c0c173, 0x8dc0c173, 0x89c0c173, 0x85f0c173][kind.val]!
private noncomputable def before (kind : Fin 4) : State :=
  wordWriteState { resetMachine with
    regs := resetMachine.regs.insert .x1 left |>.insert .x2 old |>.insert .PC (0 : BitVec 32) }
    0 (bits kind)

theorem airbender_before (kind : Fin 4) : Configured (before kind) := by
  configured_fixture [before, wordWriteState]
private def native (kind : Fin 4) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment kind⟩
private noncomputable def entry (kind : Fin 4) : UnifiedReduced.ProgramEntry :=
  ⟨0, bits kind, .ZIMOP_MOP_R (BitVec.ofNat 5 (rotation kind), .Regidx 1, .Regidx 2),
    ⟨.machine, 1, 2, 2, ⟨0, 0⟩, 65536, 47 + kind.val⟩⟩

theorem original_decoder (kind : Fin 4) :
    Airbender.Reference.RiscV.Sail.decodeOnReset (bits kind) = some (entry kind).instruction := by
  fin_cases kind <;> decode_on_reset

private theorem valid (kind : Fin 4) : (witness kind).Valid := by
  fin_cases kind <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩ <;>
    decide

theorem native_constraints (kind : Fin 4) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment kind)) (clockConstraints (Setup.table (before kind))) :=
  Completeness.Binary.complete _ (valid kind) _

theorem actual_query_contributions (kind : Fin 4) (i : Fin 4) :
    (UnifiedReduced.Proofs.leftByte (assignment kind) i).val < 256 ∧
    (UnifiedReduced.Proofs.rightByte (assignment kind) i + UnifiedReduced.Proofs.immediateByte (assignment kind) i).val < 256 ∧
    ∀ byte : Fin 4, assignment kind (58 + 4 * i.val + byte.val) =
      (((BitVec.ofNat 32 ((UnifiedReduced.Proofs.leftByte (assignment kind) i).val ^^^
        (UnifiedReduced.Proofs.rightByte (assignment kind) i + UnifiedReduced.Proofs.immediateByte (assignment kind) i).val)).rotateRight
        (#[16, 12, 8, 7][kind.val]!)).extractLsb' (8 * byte.val) 8).toNat := by
  apply UnifiedReduced.Proofs.xorrot_query_values (by decide)
    (Verification.holds_of_sublist (native_constraints kind)
      (List.sublist_append_left _ importedConstraintsTimestampLookups))
    ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ kind rfl i

private def cells : List Cell := [.register 1, .register 2]
private noncomputable def trace (kind : Fin 4) : UnifiedTrace babyBearModulus where
  rows := [native kind]
  rom := Setup.table (before kind)
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 4 (8, 0)
  initialMemory := [Cell.initialToken (.register 1) left, Cell.initialToken (.register 2) old]
  terminalMemory := [⟨(Cell.register 1).addressCode, (4, 0), Nat.pair 0x1234 0xabcd⟩,
    ⟨(Cell.register 2).addressCode, (6, 0), Nat.pair ((result kind).toNat % 65536) ((result kind).toNat / 65536)⟩]

private theorem accepted (kind : Fin 4) : Accepted (trace kind) := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact native_constraints kind
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · fin_cases kind <;> exact List.Perm.swap _ _ []
  · fin_cases kind <;> with_unfolding_all decide

private theorem decoded (kind : Fin 4) : Decoded (trace kind) [entry kind] := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  change ∃ i : Fin 1, _
  refine ⟨0, ?_⟩
  fin_cases kind <;> with_unfolding_all decide

private theorem inputs (kind : Fin 4) : NativeInputs customDecoderFields
    (trace kind) (before kind) cells [entry kind] := by
  refine ⟨by decide, ?_, ?_, ?_, ⟨[0], ?_⟩, ?_, airbender_before kind⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · have readLeft : (Cell.register 1).read (before kind) = .ok left (before kind) := by
      apply read_register
      simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
    have readOld : (Cell.register 2).read (before kind) = .ok old (before kind) := by
      apply read_register
      simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
    simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, readLeft, readOld]
    fin_cases kind <;> with_unfolding_all rfl
  · refine ⟨(4, 0), ?_⟩
    have pc : run (SailRV32.Functions.get_arch_pc ()) (before kind) = .ok 0 (before kind) := by
      apply read_register
      simp [before, wordWriteState]
    simp [initialState, pc, trace, PCState.boundary]
  · have bytes : (Cell.ram 0).read (before kind) = .ok (bits kind) (before kind) :=
      written_word_read _ _ _
    simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, original_decoder kind,
      bind, Option.bind, pure]
    fin_cases kind <;> rfl
  · constructor
    · change (timeOfPair (4, 0)).Bounded
      constructor <;> decide
    · change (timeOfPair (4, 0)).value % 4 = 0
      decide
    · intro token member
      simp [trace] at member
      rcases member with rfl | rfl
      all_goals change (timeOfPair (0, 0)).Bounded
      all_goals constructor <;> decide

theorem actual_native_xorrot (kind : Fin 4) :
    ∃ input : XorRotate.Input,
      XorRotate.TraceMapping (trace kind) (before kind) cells [entry kind] input
        ⟨Word.ofBitVec (result kind), ⟨4, 0⟩⟩ (assignment kind) ∧
      XorRotate.spec input ⟨Word.ofBitVec (result kind), ⟨4, 0⟩⟩ := by
  obtain ⟨state, position⟩ := UnifiedReduced.Proofs.custom_row_position_exists
    (row := native kind) (by decide) (by decide) (accepted kind) (inputs kind) (decoded kind) (by simp [trace])
  let input : XorRotate.Input := ⟨kind, Word.ofBitVec left, Word.ofBitVec old,
    .Regidx 1, .Regidx 2, ⟨0, 0⟩, state⟩
  have mapping : XorRotate.TraceMapping (trace kind) (before kind) cells [entry kind] input
      ⟨Word.ofBitVec (result kind), ⟨4, 0⟩⟩ (assignment kind) := by
    refine ⟨?_, position, entry kind, by simp, ?_, rfl⟩
    · constructor
      · rw [TriAdd.leftOperand, Trace.Proofs.read_word]
        change Word.ofBitVec left = Word.mk (assignment kind 36).val (assignment kind 37).val
        fin_cases kind <;> with_unfolding_all decide
      · rw [TriAdd.rightOperand, Trace.Proofs.read_word]
        change Word.ofBitVec old = Word.mk (assignment kind 42).val (assignment kind 43).val
        fin_cases kind <;> with_unfolding_all decide
      all_goals fin_cases kind <;> with_unfolding_all rfl
    · fin_cases kind <;> with_unfolding_all decide
  exact ⟨input, mapping, UnifiedReduced.Proofs.native_xorrot_soundness (by decide) (by decide) (by decide)
    (trace kind) (before kind) cells [entry kind] input
    ⟨Word.ofBitVec (result kind), ⟨4, 0⟩⟩ (assignment kind)
    ⟨⟨inputs kind, rfl⟩, ⟨accepted kind, decoded kind, by simp [trace, native]⟩, mapping⟩⟩

theorem actual_custom_trace (kind : Fin 4) :
    Realizes (Custom.Step [entry kind]) (trace kind) (before kind) cells := by
  apply UnifiedReduced.Proofs.custom_trace_execution (by decide) (by decide) (by decide)
    (accepted := accepted kind) (decoded := decoded kind)
  refine ⟨inputs kind, rfl, ?_⟩
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  change 0 < ROM.limit ∧ 0 % 4 = 0
  decide

end Tests.UnifiedXorRotate
