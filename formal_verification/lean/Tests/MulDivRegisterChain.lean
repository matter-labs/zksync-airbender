import Tests.MulDivRegisters

namespace Tests.MulDivRegisterChain
open Airbender Arithmetic Trace Verification MulDiv Reference.RiscV.Sail Reference.Sail

/-- Two original MUL instructions. The second destination aliases its first
    source; its old-value read must see that row's earlier readonly refresh. -/
def before : State :=
  { (Tests.MulDivInitializedFixture.before .mul false false) with
    mem := ((Tests.MulDivInitializedFixture.before .mul false false).mem
      |>.insert 4 0xb3 |>.insert 5 0x80 |>.insert 6 0x20 |>.insert 7 0x02) }

def aliasEntry : MulDiv.ProgramEntry :=
  ⟨4,0x022080b3,.MUL (.Regidx 2,.Regidx 1,.Regidx 1,⟨.Low,.Signed,.Signed⟩),
    ⟨.mul,1,2,1,⟨0,0⟩,2,0⟩⟩
def setup : SparseDecoderSetup Operation := ⟨[some (Tests.MulDivInitializedFixture.entry .mul false),some aliasEntry],1048574⟩
def assignment (stale : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 4 else if i = 13 then 8 else if i = 2 then 8 else if i = 15 then 12
  else if i = 62 then 1801116374 else if i = 7 then 1 else if i = 58 then 123 else if i = 66 then 4 else if i = 69 then 5
  else if i = 72 then (if stale then 4 else 8) else Tests.MulDivInitializedFixture.assignment .mul false false i
def aliasRow (stale : Bool) : Row mersenne31Modulus MulDivFamily := ⟨.mulDiv,assignment stale⟩
private def cell (register time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair register 0),(time,0),Nat.pair (value%65536) (value/65536)⟩
def trace (stale : Bool) : Data mersenne31Modulus MulDivFamily where
  rows := [aliasRow stale,Tests.MulDivInitializedFixture.nativeRow .mul false false]
  rom := ()
  initial := ⟨(0,0),(4,0)⟩
  terminal := ⟨(8,0),(12,0)⟩
  initialMemory := (Tests.MulDivInitializedFixture.trace .mul false false).initialMemory
  terminalMemory := [cell 0 0 0,cell 1 10 861,cell 2 9 7,cell 3 6 861]

private theorem public_words (i : Fin 2) :
    (Cell.ram (_root_.BitVec.ofNat 32 (4 * i.val))).read before =
      .ok (if i.val = 0 then Tests.MulDivInitializedFixture.word .mul false else aliasEntry.bits) before := by
  fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,Tests.MulDivInitializedFixture.before,Tests.MulDivInitializedFixture.word,Operation.funct3,aliasEntry,Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 32768 in
private theorem alias_decode :
    run (SailRV32.Functions.encdec_backwards aliasEntry.bits) before =
      .ok aliasEntry.instruction before := by
  have isa : run (SailRV32.readReg .misa) before = .ok (0x40001000 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Tests.MulDivInitializedFixture.before]
  repeat' first
    | (with_unfolding_all rfl)
    | (with_unfolding_all conv_lhs => arg 1; whnf
       rw [@Reference.Sail.run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
         _ _ SailRV32.Register.misa _ _ _ isa])

theorem program_image : MulDiv.sparseDecoderSetupImage before 2 20 = some setup := by
  have isa : run (SailRV32.readReg .misa) before = .ok (0x40001000 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Tests.MulDivInitializedFixture.before]
  have first : programSlotRunWith MulDiv.decoderFields before 0 = some (some (Tests.MulDivInitializedFixture.entry .mul false)) := by
    simp only [programSlotRunWith,show (Cell.ram 0).read before = .ok (Tests.MulDivInitializedFixture.word .mul false) before from public_words 0,
      Tests.MulDivInitializedFixture.original_decode .mul false before isa,bind,Option.bind,pure]
    rfl
  have second : programSlotRunWith MulDiv.decoderFields before 4 = some (some aliasEntry) := by
    simp only [programSlotRunWith,show (Cell.ram 4).read before = .ok aliasEntry.bits before from public_words 1,
      alias_decode,bind,Option.bind,pure]
    rfl
  change (([0,4] : List (BitVec 32)).mapM (programSlotRunWith MulDiv.decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048574)) = _
  rw [List.mapM_cons,first,List.mapM_cons,second,List.mapM_nil]
  rfl

theorem native_constraints (stale : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment stale)) importedConstraints := by
  cases stale <;>
    simp [importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,Tests.MulDivInitializedFixture.assignment,Tests.MulDivWitness.assignment,Tests.MulDivWitness.witnessValues]
  all_goals repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) | (apply timestamp19_contains; decide) |
    (apply Tests.MulDivWitness.byte_query_contains <;> decide) | decide

private abbrev MemoryMatches (candidate : Data mersenne31Modulus MulDivFamily) : Prop :=
  (candidate.initialMemory ++ candidate.rows.flatMap Row.writes).Perm
    (candidate.terminalMemory ++ candidate.rows.flatMap Row.reads)

theorem state_matching (stale : Bool) :
    ((trace stale).initial :: (trace stale).rows.map Row.finish).Perm
      ((trace stale).terminal :: (trace stale).rows.map Row.start) := by
  change [(trace stale).initial,(trace stale).terminal,(aliasRow stale).start].Perm
    [(trace stale).terminal,(aliasRow stale).start,(trace stale).initial]
  exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))

theorem accepted : Accepted (trace false) := by
  constructor
  · intro row member
    simp only [trace,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl
    · exact native_constraints false
    · exact Tests.MulDivInitializedFixture.native_constraints .mul false false
  · intro row member
    simp only [trace,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> rfl
  · exact state_matching false
  · change MemoryMatches (trace false)
    decide +kernel


theorem public_inputs : ImageBoundary (trace false) before
    [.register 0,.register 1,.register 2,.register 3] := by
  have zero : (Cell.register 0).read before = .ok (0 : BitVec 32) before := rfl
  have first : (Cell.register 1).read before = .ok (123 : BitVec 32) before := by
    apply read_register
    simp [before,Tests.MulDivInitializedFixture.before,Tests.MulDivInitializedFixture.dividend,
      Tests.MulDivInitializedFixture.divisor,Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 2).read before = .ok (7 : BitVec 32) before := by
    apply read_register
    simp [before,Tests.MulDivInitializedFixture.before,Tests.MulDivInitializedFixture.dividend,
      Tests.MulDivInitializedFixture.divisor,Std.ExtDHashMap.get?_insert]
  have third : (Cell.register 3).read before = .ok (0 : BitVec 32) before := by
    apply read_register
    simp [before,Tests.MulDivInitializedFixture.before,Tests.MulDivInitializedFixture.dividend,
      Tests.MulDivInitializedFixture.divisor,Std.ExtDHashMap.get?_insert]
  have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok (0 : BitVec 32) before := by
    apply read_register
    simp [before,Tests.MulDivInitializedFixture.before,Tests.MulDivInitializedFixture.dividend,
      Tests.MulDivInitializedFixture.divisor,Std.ExtDHashMap.get?_insert]
  constructor
  · decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,first,second,third]
    rfl
  · rw [initialState,pc]
    rfl

private theorem pair_first_member (first second : MulDiv.ProgramEntry) (padding : Nat) :
    ((SparseDecoderSetup.mk [some first,some second] padding).table (p := mersenne31Modulus)).Contains
      #[] first.query := by
  refine ⟨⟨0,by simp⟩,rfl⟩
private theorem pair_second_member (first second : MulDiv.ProgramEntry) (padding : Nat) :
    ((SparseDecoderSetup.mk [some first,some second] padding).table (p := mersenne31Modulus)).Contains
      #[] second.query := by
  refine ⟨⟨1,by simp; omega⟩,rfl⟩

private theorem alias_entry_query : aliasEntry.query (p := mersenne31Modulus) =
    #v[4,0,1,2,1,0,0,0,0,2] := by decide +kernel

private theorem alias_query (stale : Bool) :
    MulDiv.decoderQuery (assignment stale) = aliasEntry.query := by
  rw [alias_entry_query]
  cases stale <;>
    norm_num [MulDiv.decoderQuery,nativeDecoderQuery,importedConstraintsTraceColumns,
      importedConstraintsDecoderColumns,assignment,Tests.MulDivInitializedFixture.assignment,
      Tests.MulDivWitness.assignment,Tests.MulDivWitness.witnessValues]

theorem decoded (stale : Bool) : MulDiv.Decoded (trace stale) setup := by
  intro row member
  simp only [trace,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl
  · rw [MulDiv.Proofs.row_decoder_query]
    change setup.table.Contains #[] (MulDiv.decoderQuery (assignment stale))
    rw [alias_query]
    exact pair_second_member (Tests.MulDivInitializedFixture.entry .mul false) aliasEntry 1048574
  · rw [MulDiv.Proofs.row_decoder_query]
    have query := (Tests.MulDivInitializedFixture.decoded .mul false false)
      (Tests.MulDivInitializedFixture.nativeRow .mul false false) (by simp [Tests.MulDivInitializedFixture.trace])
    change (Tests.MulDivInitializedFixture.setup .mul false).table.Contains #[]
      (MulDiv.decoderQuery (Tests.MulDivInitializedFixture.assignment .mul false false)) at query
    obtain ⟨actual,present,same⟩ := MulDiv.Proofs.decoder_member (by decide)
      (Tests.MulDivInitializedFixture.native_constraints .mul false false) query
    have only : actual = Tests.MulDivInitializedFixture.entry .mul false := by
      simpa [Tests.MulDivInitializedFixture.setup,SparseDecoderSetup.program] using present
    subst actual
    change setup.table.Contains #[] (MulDiv.decoderQuery (Tests.MulDivInitializedFixture.assignment .mul false false))
    rw [same]
    exact pair_first_member (Tests.MulDivInitializedFixture.entry .mul false) aliasEntry 1048574

/-- Stale alias metadata retains full local constraints, public decoding and
    state matching; native memory matching rejects the skipped readonly refresh. -/
theorem stale_rejected : ¬Accepted (trace true) := by
  intro h
  have wrong := h.memory.count_eq (cell 1 8 123)
  revert wrong
  decide +kernel


/-- Full native/public inputs construct the reversed two-row Sail GPR history. -/
theorem public_history : RegisterHistory (trace false) setup before
    [.register 0,.register 1,.register 2,.register 3] :=
  MulDiv.public_register_history program_image public_inputs accepted (decoded false)
    Tests.MulDivRegisters.aligned

private theorem sorted_rows {rows : List (Row mersenne31Modulus MulDivFamily)}
    (permutation : rows.Perm (trace false).rows)
    (ordered : rows.Pairwise (fun a b => b.clock < a.clock)) :
    rows = [aliasRow false,Tests.MulDivInitializedFixture.nativeRow .mul false false] := by
  have length : rows.length = 2 := by simpa only [trace,List.length_cons,List.length_nil] using permutation.length_eq
  cases rows with
  | nil => simp at length
  | cons a tail =>
    cases tail with
    | nil => simp at length
    | cons b rest =>
      have empty : rest = [] := by
        cases rest with
        | nil => rfl
        | cons c cs => simp only [List.length_cons] at length; omega
      subst rest
      have less : b.clock < a.clock := (List.pairwise_cons.mp ordered).1 b (by simp)
      have aMember : a = aliasRow false ∨ a = Tests.MulDivInitializedFixture.nativeRow .mul false false := by
        have member := permutation.mem_iff.mp (List.mem_cons_self (a := a) (l := [b]))
        simpa only [trace,List.mem_cons,List.mem_nil_iff,or_false] using member
      have bMember : b = aliasRow false ∨ b = Tests.MulDivInitializedFixture.nativeRow .mul false false := by
        have member := permutation.mem_iff.mp (List.mem_cons_of_mem a (List.mem_cons_self (a := b) (l := [])))
        simpa only [trace,List.mem_cons,List.mem_nil_iff,or_false] using member
      rcases aMember with rfl | rfl <;> rcases bMember with rfl | rfl
      · exact (Nat.lt_irrefl _ less).elim
      · rfl
      · have impossible : ¬(aliasRow false).clock < (Tests.MulDivInitializedFixture.nativeRow .mul false false).clock := by decide +kernel
        exact (impossible less).elim
      · exact (Nat.lt_irrefl _ less).elim

/-- The second original instruction is decoded after the first real GPR update.
    Its aliased operand/destination reads use the same actual pre-state and the
    original Sail write reaches the constructed after-state with value 861. -/
theorem alias_after_update : ∃ rowBefore after : State,
    SailHistory [Cell.register 0,.register 1,.register 2,.register 3]
      (rowEvents (trace false).memoryEpoch
        (Tests.MulDivInitializedFixture.nativeRow .mul false false)).reverse before rowBefore ∧
    aliasEntry.SourceWith rowBefore MulDiv.decoderFields ∧
    run (SailRV32.Functions.rX_bits (.Regidx 1)) rowBefore = .ok (123 : BitVec 32) rowBefore ∧
    run (SailRV32.Functions.rX_bits (.Regidx 2)) rowBefore = .ok (7 : BitVec 32) rowBefore ∧
    run (SailRV32.Functions.wX_bits (.Regidx 1) (861 : BitVec 32)) rowBefore = .ok () after ∧
    after.mem = before.mem ∧ after.regs.get? .misa = before.regs.get? .misa := by
  obtain ⟨history,rows,after,_,permutation,ordered,_,_,memory,isa,transfers⟩ := public_history
  have shape := sorted_rows permutation ordered
  obtain ⟨actual,present,rowBefore,rowAfter,_,source,query,earlier,_,later,transfer⟩ :=
    transfers [] (aliasRow false) [Tests.MulDivInitializedFixture.nativeRow .mul false false] shape
  change SailHistory _ [] rowAfter after at later
  cases later
  have choice : actual = Tests.MulDivInitializedFixture.entry .mul false ∨ actual = aliasEntry := by
    simpa [setup,SparseDecoderSetup.program] using present
  rcases choice with first | second
  · subst actual
    have pc := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[0]) query
    change (4 : ZMod mersenne31Modulus) = 0 at pc
    exact False.elim ((by decide : (4 : ZMod mersenne31Modulus) ≠ 0) pc)
  · subst actual
    have left := transfer.1 0
    have right := transfer.1 1
    have written := transfer.2
    refine ⟨rowBefore,after,earlier,source,?_,?_,?_,memory,isa⟩
    all_goals simp [aliasEntry,aliasRow,assignment,Tests.MulDivInitializedFixture.assignment,
      Tests.MulDivWitness.assignment,Tests.MulDivWitness.witnessValues,
      importedConstraintsMemoryPorts,MemoryPort.readCode,MemoryPort.writeCode,
      WordColumns.code,WordColumns.evaluate,memoryWord,Nat.unpair_pair,
      Word.toBitVec,Word.value,limbBase] at left right written ⊢
    all_goals assumption

end Tests.MulDivRegisterChain
