import Tests.ControlHistory
import Airbender.Review.Trace.Families.JumpBranchSlt.Values
import Airbender.Review.Trace.Families.JumpBranchSlt.SailHistory

namespace Tests.ControlValues
open Airbender Trace Verification Arithmetic
open Tests.ControlHistory
open JumpBranchSlt.NativeSetup (words setup)

private theorem public_words (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
      .ok words[i.val] before := by
  fin_cases i <;>
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, JumpBranchSlt.NativeSetup.before, words, Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 32768 in
theorem decoder_image : JumpBranchSlt.sparseDecoderSetupImage before 3 20 = some JumpBranchSlt.NativeSetup.setup := by
  have slots : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields before) = some JumpBranchSlt.NativeSetup.setup.slots := by
    simp only [List.mapM_cons, List.mapM_nil, programSlotWith,
      show (Cell.ram 0).read before = .ok (0xffdff0ef : BitVec 32) before from public_words ⟨0, by decide⟩,
      show (Cell.ram 4).read before = .ok (0xc0001073 : BitVec 32) before from public_words ⟨1, by decide⟩,
      show (Cell.ram 8).read before = .ok (0xfff0b013 : BitVec 32) before from public_words ⟨2, by decide⟩,
      bind, Option.bind]
    cbv
  change (([0,4,8] : List (BitVec 32)).mapM (programSlotWith JumpBranchSlt.decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048573)) = some JumpBranchSlt.NativeSetup.setup
  rw [slots]
  rfl

theorem decoded : JumpBranchSlt.Decoded (trace false) setup := by
  intro row present
  have same : row = nativeRow false := by simpa [trace] using present
  subst row
  obtain ⟨i, query⟩ := exported_membership
  exact ⟨i, query.trans (JumpBranchSlt.Proofs.native_exported_rows i)⟩

theorem value_bounds :
    (∀ row ∈ (trace false).rows, ∀ port ∈ row.ports,
      (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ (trace false).rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ (trace false).terminalMemory, token.word.Bounded) :=
  JumpBranchSlt.public_value_bounds decoder_image public_inputs accepted decoded

/-- The actual destination replaces the old x1 value, rather than retaining its
    read word or mistaking the route-bit columns for the destination. -/
theorem destination :
    (readToken (assignment false) JumpBranchSlt.importedConstraintsMemoryPorts[2]).word = ⟨123,0⟩ ∧
    (writeToken (nativeRow false).columns (assignment false)
      JumpBranchSlt.importedConstraintsMemoryPorts[2]).word = ⟨4,0⟩ := by
  rw [Trace.Proofs.read_word, Trace.Proofs.write_word]
  constructor <;> decide

theorem zero_events : ∀ event ∈ (trace false).nativeEvents,
    event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0 :=
  JumpBranchSlt.Proofs.native_zero_writes (by decide) accepted
    (Trace.Proofs.image_clock_boundary (by decide) public_inputs) public_inputs.image decoded

theorem cell_history :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus JumpBranchSltFamily)) (after : Reference.RiscV.Sail.State),
      MemoryHistory (trace false) history ∧ rows.Perm (trace false).rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory [.register 0, .register 1]
        (rows.flatMap fun row => (rowEvents (trace false).memoryEpoch row).reverse) before after ∧
      SailStateMatches [.register 0, .register 1] history after :=
  JumpBranchSlt.public_sail_cell_history public_inputs accepted decoded (by
    intro cell present
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at present
    rcases present with rfl | rfl <;> simp [Cell.Aligned])

/-- Local native equations do not Boolean-constrain the external decoder flag.
    The full public lookup is essential to the initialized word-range claim. -/
def badFlag (i : Nat) : ZMod mersenne31Modulus :=
  if i = 8 then 2 else if i = 36 then -1 else if i = 38 then -4
  else assignment false i

theorem bad_flag_native :
    FlatOperation.ConstraintsHoldFlat (environment badFlag) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
      environment, badFlag, assignment, Tests.JumpDecoder.assignment, Tests.JumpPC.negativeJal,
      Tests.JumpControl.assignment]
  all_goals
    repeat' apply And.intro
    all_goals first | (apply range16_contains; decide) |
      (apply timestamp19_contains; decide) | try decide
    all_goals
      simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
        jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
        Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
        badFlag, assignment, Tests.JumpDecoder.assignment, Tests.JumpPC.negativeJal,
        Tests.JumpControl.assignment]
      solve
      | refine ⟨⟨7, by decide⟩, ?_⟩
        norm_num [conditionalControlRow, controlFlag]
      | refine ⟨⟨65532, by decide⟩, ?_⟩
        norm_num [jumpCleanupRow]

theorem bad_flag_unbounded :
    ¬(writeToken (nativeRow false).columns badFlag
      JumpBranchSlt.importedConstraintsMemoryPorts[2]).word.Bounded := by
  rw [Trace.Proofs.write_word]
  change ¬((badFlag 38).val < 65536 ∧ (badFlag 39).val < 65536)
  decide +kernel

theorem bad_flag_decoder_rejected :
    ¬setup.table.Contains #[] (JumpBranchSlt.decoderQuery badFlag) := by
  intro member
  obtain ⟨entry, _, query⟩ := JumpBranchSlt.Proofs.decoder_member
    (by decide) bad_flag_native member
  have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) query
  change (2 : ZMod mersenne31Modulus) = (if entry.data.rd = 0 then 1 else 0) at flag
  split_ifs at flag
  · exact (by decide : (2 : ZMod mersenne31Modulus) ≠ 1) flag
  · exact (by decide : (2 : ZMod mersenne31Modulus) ≠ 0) flag

end Tests.ControlValues
