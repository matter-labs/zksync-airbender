import Slop.UnifiedReduced.ROMRow
import Slop.UnifiedReduced.ROMLookups
import Slop.BabyBear
import Slop.Trace.Timestamps
import Slop.UnifiedReduced.Completeness.RomLoad

namespace Tests.UnifiedROM
open Airbender UnifiedReduced Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 0xef |>.insert 1 0xbe |>.insert 2 0xad |>.insert 3 0xde }

private def query (lo : Nat) : Vector (Expression (ZMod babyBearModulus)) 10 :=
  #v[.const 0, .const (lo : ZMod babyBearModulus), .const 0xdead,
    .const 0, .const 0, .const 0, .const 0, .const 0, .const 0, .const 34]
private def environment : Environment (ZMod babyBearModulus) := Verification.environment (fun _ => 0)

theorem public_word : ROM.words before 0 = 0xdeadbeef := by
  simp [ROM.words, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte, EStateM.run,
    get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
    before, Std.ExtHashMap.getElem_insert]

theorem accepted : (Lookup.mk (Setup.table before).toRaw (query 0xbeef)).Contains environment := by
  change ∃ i : Fin 2097537, (query 0xbeef).map (Expression.eval environment) =
    (Setup.row before i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨1048961, by decide⟩, ?_⟩
  change (query 0xbeef).map (Expression.eval environment) =
    (#v[0, (Word.ofBitVec (ROM.words before 0)).lo, (Word.ofBitVec (ROM.words before 0)).hi,
      0, 0, 0, 0, 0, 0, 34] : Vector Nat 10).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  rw [public_word]
  with_unfolding_all decide

theorem value_from_image :
    (Word.mk ((query 0xbeef)[1].eval environment).val ((query 0xbeef)[2].eval environment).val).toBitVec =
      ROM.words before (((query 0xbeef)[0].eval environment).val / 4) :=
  (Setup.Proofs.rom_lookup (by decide) accepted (by decide)).2.2.1

theorem wrong_value_rejected :
    ¬ (Lookup.mk (Setup.table before).toRaw (query 0xbeee)).Contains environment := by
  intro accepted
  have result := (Setup.Proofs.rom_lookup (by decide) accepted (by decide)).2.2.1
  have wrong : (Word.mk ((query 0xbeee)[1].eval environment).val
      ((query 0xbeee)[2].eval environment).val).toBitVec ≠
      ROM.words before (((query 0xbeee)[0].eval environment).val / 4)  := by
    have value : ROM.words before (((query 0xbeee)[0].eval environment).val / 4) = 0xdeadbeef := public_word
    rw [value]
    with_unfolding_all decide
  exact wrong result

/-- LW x3, 0(x0) from the ROM word 0xdeadbeef at PC 0, clock 4. -/
private def witness : Completeness.RomLoad :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩, 0, 3, 0, 0, 0, 0, 0xbeef, 0xdead, 0, 0, 0, 0⟩
private def assignment : Nat → ZMod babyBearModulus := witness.honest

theorem native_row_accepted : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (clockConstraints (Setup.table before)) :=
  Completeness.RomLoad.complete _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) before
    (by change Word.ofBitVec (ROM.words before 0) = _; rw [public_word]; rfl)

theorem public_read_row_accepted : FlatOperation.ConstraintsHoldFlat
    (Verification.environment
      (UnifiedReduced.ROMView.row before (⟨.machine, assignment⟩ : Row babyBearModulus UnifiedFamily)).assignment)
    (clockConstraints (Setup.table before)) :=
  UnifiedReduced.ROMView.row_holds (by decide) before ⟨.machine, assignment⟩
    (Setup.table before) rfl native_row_accepted

theorem shadow_read_is_zero : (Word.mk (assignment 42).val (assignment 43).val).toBitVec = 0 := by rfl

theorem public_read_is_nonzero :
    let mapped := UnifiedReduced.ROMView.row before (⟨.machine, assignment⟩ : Row babyBearModulus UnifiedFamily)
    (Word.mk (mapped.assignment 42).val (mapped.assignment 43).val).toBitVec = 0xdeadbeef := by
  have word : Trace.ROMView.publicWord before (Nat.pair 1 (Nat.pair 0 0)) = Word.ofBitVec 0xdeadbeef := by
    simp [Trace.ROMView.publicWord, Word.toBitVec, Word.value, limbBase, Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  have load : assignment 28 = 1 := rfl
  have rom : assignment 54 = 1 := rfl
  have lo : (assignment 38).val = 0 := rfl
  have hi : (assignment 39).val = 0 := rfl
  simp only [UnifiedReduced.ROMView.row, load, rom, lo, hi, and_self, ↓reduceIte, word]
  with_unfolding_all decide

end Tests.UnifiedROM
