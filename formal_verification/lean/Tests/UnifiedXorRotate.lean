import Airbender.Proofs.UnifiedReduced.XorRotateQueries
import Airbender.Proofs.UnifiedReduced.CustomHistory
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Sail.WordMemoryState

namespace Tests.UnifiedXorRotate
open Airbender Arithmetic UnifiedReduced Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def rotation (kind : Fin 4) : Nat := #[16, 12, 8, 7][kind.val]!
private def left : BitVec 32 := 0xabcd1234
private def old : BitVec 32 := 0xef015678
private def result (kind : Fin 4) : BitVec 32 := (left ^^^ old).rotateRight (rotation kind)
private def contribution (kind : Fin 4) (i byte : Nat) : Nat :=
  (((BitVec.ofNat 32 ((left.extractLsb' (8 * i) 8).toNat ^^^
    (old.extractLsb' (8 * i) 8).toNat)).rotateRight (rotation kind)).extractLsb' (8 * byte) 8).toNat
private def assignment (kind : Fin 4) (column : Nat) : ZMod babyBearModulus :=
  if 58 ≤ column ∧ column < 74 then contribution kind ((column - 58) / 4) ((column - 58) % 4)
  else if 92 ≤ column ∧ column < 128 then
    let i := (column - 92) / 9
    match (column - 92) % 9 with
    | 0 => (47 + kind.val : Nat)
    | 1 => (left.extractLsb' (8 * i) 8).toNat
    | 2 => (old.extractLsb' (8 * i) 8).toNat
    | 3 => contribution kind i 0
    | 4 => contribution kind i 1
    | 5 => contribution kind i 2
    | 6 => contribution kind i 3
    | _ => 0
  else match column with
    | 4 | 5 | 27 | 129 | 130 | 131 | 132 | 133 => 1
    | 6 | 7 | 38 | 44 => 2
    | 2 | 30 => 4
    | 32 => 8
    | 46 => 5
    | 10 => (47 + kind.val : Nat)
    | 36 => 0x1234 | 37 => 0xabcd | 42 | 48 => 0x5678 | 43 | 49 => 0xef01
    | 50 => (((result kind).toNat % 65536 : Nat) : ZMod babyBearModulus)
    | 51 => (((result kind).toNat / 65536 : Nat) : ZMod babyBearModulus)
    | 74 => 0x34 | 75 => 0xcd | 76 => 0x78 | 77 => 1
    | 88 => 3
    | 80 => 0xabcd1234 * 0xef015678 * 943718400
    | _ => 0
private def bits (kind : Fin 4) : BitVec 32 :=
  #[0xc1c0c173, 0x8dc0c173, 0x89c0c173, 0x85f0c173][kind.val]!
private def before (kind : Fin 4) : State :=
  wordWriteState { (default : State) with
    regs := (default : State).regs.insert .x1 left |>.insert .x2 old |>.insert .PC (0 : BitVec 32) }
    0 (bits kind)
private def native (kind : Fin 4) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment kind⟩
private def entry (kind : Fin 4) : UnifiedReduced.ProgramEntry :=
  ⟨0, bits kind, .ZIMOP_MOP_R (BitVec.ofNat 5 (rotation kind), .Regidx 1, .Regidx 2),
    ⟨.machine, 1, 2, 2, ⟨0, 0⟩, 65536, 47 + kind.val⟩⟩

theorem original_decoder (kind : Fin 4) (state : State) :
    run (SailRV32.Functions.encdec_backwards (bits kind)) state = .ok (entry kind).instruction state := by
  fin_cases kind <;> with_unfolding_all rfl

theorem native_constraints (kind : Fin 4) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment kind)) (clockConstraints (Setup.table (before kind))) := by
  apply Verification.holds_append
  · fin_cases kind
    all_goals simp [importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, assignment, result, contribution, left, old, rotation,
      Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | exact ⟨⟨1, by decide⟩, by with_unfolding_all decide⟩
      | (refine ⟨⟨786817 + 0 * 65536 + 0x34 * 256 + 0x78, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 0 * 65536 + 0x12 * 256 + 0x56, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 0 * 65536 + 0xcd * 256 + 1, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 0 * 65536 + 0xab * 256 + 0xef, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 1 * 65536 + 0x34 * 256 + 0x78, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 1 * 65536 + 0x12 * 256 + 0x56, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 1 * 65536 + 0xcd * 256 + 1, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 1 * 65536 + 0xab * 256 + 0xef, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 2 * 65536 + 0x34 * 256 + 0x78, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 2 * 65536 + 0x12 * 256 + 0x56, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 2 * 65536 + 0xcd * 256 + 1, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 2 * 65536 + 0xab * 256 + 0xef, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 3 * 65536 + 0x34 * 256 + 0x78, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 3 * 65536 + 0x12 * 256 + 0x56, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 3 * 65536 + 0xcd * 256 + 1, by decide⟩, ?_⟩; with_unfolding_all decide)
      | (refine ⟨⟨786817 + 3 * 65536 + 0xab * 256 + 0xef, by decide⟩, ?_⟩; with_unfolding_all decide)
  · fin_cases kind
    all_goals simp [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

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
    (by constructor <;> simp [assignment]) (by repeat' apply And.intro; all_goals simp [assignment])
    kind (by simp [assignment]) i

end Tests.UnifiedXorRotate
