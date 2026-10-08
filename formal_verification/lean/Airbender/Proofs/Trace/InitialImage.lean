import Airbender.Review.Trace.InitialImage
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Sail.PC
import Airbender.Proofs.PCState

namespace Airbender.Trace.Proofs
open Arithmetic
open Reference.Sail
open _root_.Sail.ArchSem

private theorem primitive_read_frame {reg : SailRV32.Register}
    {before after : Reference.RiscV.Sail.State} {value : SailRV32.RegisterType reg}
    (read : run (SailRV32.readReg reg) before = .ok value after) : after = before := by
  dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects,
    FreeM.liftM, interpretInstructionEffect] at read
  cases found : before.regs.get? reg
  · simp [found, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.run] at read
  · simp only [found] at read
    exact (EStateM.Result.ok.inj read).2.symm

private theorem gpr_read_frame (index : BitVec 5)
    {before after : Reference.RiscV.Sail.State} {value : BitVec 32}
    (read : run (SailRV32.Functions.rX_bits (.Regidx index)) before = .ok value after) :
    after = before := by
  have bound : index.toNat < 32 := index.isLt
  change run (SailRV32.Functions.rX (.Regno (index.toNat : Int))) before = _ at read
  interval_cases index.toNat
  all_goals first
    | exact primitive_read_frame read
    | (change EStateM.Result.ok (0 : BitVec 32) before = .ok value after at read
       exact (EStateM.Result.ok.inj read).2.symm)

private theorem byte_read_frame {before after : Reference.RiscV.Sail.State}
    {address : Nat} {value : BitVec 8}
    (read : (readByte (ue := SailRV32.exception) address).run before = .ok value after) :
    after = before := by
  unfold readByte at read
  cases found : before.mem[address]? <;>
    simp_all [EStateM.run, get, getThe, MonadStateOf.get, bind, pure,
      EStateM.bind, EStateM.get, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private theorem bytes_read_frame (size address : Nat)
    {before after : Reference.RiscV.Sail.State} {value : BitVec (8 * size)}
    (read : (readBytes (ue := SailRV32.exception) size address).run before = .ok value after) :
    after = before := by
  induction size generalizing address before after with
  | zero => exact (EStateM.Result.ok.inj read).2.symm
  | succ size ih =>
    cases size with
    | zero =>
      unfold readBytes at read
      simp only [EStateM.run, bind, pure, EStateM.bind, EStateM.pure] at read
      cases first : readByte (ue := SailRV32.exception) address before with
      | error err state => simp [first] at read
      | ok byte middle =>
        have frame := byte_read_frame first
        subst middle
        simp [first] at read
        exact read.2.symm
    | succ size =>
      unfold readBytes at read
      simp only [EStateM.run, bind, pure, EStateM.bind, EStateM.pure] at read
      cases first : readByte (ue := SailRV32.exception) address before with
      | error err state => simp [first] at read
      | ok byte middle =>
        have frame := byte_read_frame first
        subst middle
        cases rest : readBytes (ue := SailRV32.exception) (size + 1) (address + 1) before with
        | error err state => simp [first, rest] at read
        | ok bytes last =>
          have frame := ih _ rest
          subst last
          simp [first, rest] at read
          exact read.2.symm

/-- Every successful image read preserves the supplied Sail state. -/
theorem cell_read_frame (cell : Cell) {before after : Reference.RiscV.Sail.State}
    {value : BitVec 32} (read : cell.read before = .ok value after) : after = before := by
  cases cell with
  | register index => exact gpr_read_frame index read
  | ram address => exact bytes_read_frame 4 address.toNat read

theorem initial_token_word (cell : Cell) (value : BitVec 32) :
    (cell.initialToken (p := p) value).word = Word.ofBitVec value := by
  simp [Cell.initialToken, MemoryToken.word]

/-- Successful extraction records actual Sail reads, in the public domain's
    order, with no witness-supplied initial values. -/
theorem image_reads {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens) :
    List.Forall₂ (fun cell token => ∃ value, cell.read before = .ok value before ∧
      token = cell.initialToken value) cells tokens := by
  induction cells generalizing tokens with
  | nil =>
    have empty : tokens = [] := by simpa [initialImage] using image.symm
    subst tokens
    exact .nil
  | cons cell tail ih =>
    change List.mapM _ (cell :: tail) = some tokens at image
    rw [List.mapM_cons] at image
    change Option.bind
      (match cell.read before with
        | .ok value _ => some (cell.initialToken value)
        | .error _ _ => none)
      (fun token => Option.bind (initialImage before tail)
        (fun remaining => some (token :: remaining))) = some tokens at image
    cases first : cell.read before with
    | error err state => simp [first] at image
    | ok value after =>
      have frame := cell_read_frame cell first
      subst after
      cases rest : initialImage (p := p) before tail with
      | none => simp [first, rest] at image
      | some remaining =>
        have result : cell.initialToken value :: remaining = tokens := by
          simpa [first, rest] using image
        subst tokens
        exact .cons ⟨value, first, rfl⟩ (ih rest)

theorem image_sources {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens) :
    ∀ token ∈ tokens, ∃ cell ∈ cells, ∃ value,
      cell.read before = .ok value before ∧ token = cell.initialToken value := by
  have reads := image_reads image
  clear image
  induction reads with
  | nil => simp
  | @cons cell token cells tokens head tail ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨value, read, same⟩ := head
      exact ⟨cell, List.mem_cons_self, value, read, same⟩
    · obtain ⟨source, sourceMember, value, read, same⟩ := ih actual member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, value, read, same⟩

theorem image_addresses {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens) :
    tokens.map MemoryToken.address = cells.map Cell.addressCode := by
  have reads := image_reads image
  clear image
  induction reads with
  | nil => rfl
  | @cons cell token cells tokens head tail ih =>
    obtain ⟨value, _, rfl⟩ := head
    simpa only [List.map_cons, Cell.initialToken] using congrArg (List.cons cell.addressCode) ih

theorem image_cell_source {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens) :
    ∀ cell ∈ cells, ∃ token ∈ tokens, ∃ value,
      cell.read before = .ok value before ∧ token = cell.initialToken value := by
  have reads := image_reads image
  clear image
  induction reads with
  | nil => simp
  | @cons cell token cells tokens head tail ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨value, read, same⟩ := head
      exact ⟨token, List.mem_cons_self, value, read, same⟩
    · obtain ⟨source, sourceMember, value, read, same⟩ := ih actual member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, value, read, same⟩

theorem image_bounds {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens) :
    ∀ token ∈ tokens, token.word.Bounded := by
  intro token member
  obtain ⟨cell, _, value, _, rfl⟩ := image_sources image token member
  rw [initial_token_word]
  exact Word.ofBitVec_bound value

theorem image_clocks {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens) :
    ∀ token ∈ tokens, (timeOfPair token.time).Bounded := by
  intro token member
  obtain ⟨cell, _, value, _, rfl⟩ := image_sources image token member
  simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]

theorem cell_address_injective : Function.Injective Cell.addressCode := by
  intro left right same
  cases left with
  | register a =>
    cases right with
    | register b =>
      have index := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp same).2).1
      exact congrArg Cell.register (BitVec.eq_of_toNat_eq index)
    | ram b => simp [Cell.addressCode, Nat.pair_eq_pair] at same
  | ram a =>
    cases right with
    | register b => simp [Cell.addressCode, Nat.pair_eq_pair] at same
    | ram b =>
      have limbs := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp same).2
      apply congrArg Cell.ram
      apply BitVec.eq_of_toNat_eq
      rw [← Word.ofBitVec_value a, ← Word.ofBitVec_value b]
      simp only [Word.value, limbs.1, limbs.2]

theorem image_unique {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens)
    (domain : cells.Nodup) : (tokens.map MemoryToken.address).Nodup := by
  rw [image_addresses image]
  exact domain.map cell_address_injective

theorem initial_state_source {before : Reference.RiscV.Sail.State}
    {timestamp : ZMod p × ZMod p} {state : PCState.State p}
    (initial : initialState before timestamp = some state) :
    ∃ pc, run (SailRV32.Functions.get_arch_pc ()) before = .ok pc before ∧
      state = PCState.boundary pc timestamp := by
  unfold initialState at initial
  cases read : run (SailRV32.Functions.get_arch_pc ()) before with
  | error err after => simp [read] at initial
  | ok pc after =>
    have frame := primitive_read_frame read
    subst after
    exact ⟨pc, rfl, by simpa [read] using initial.symm⟩

theorem initial_pc_bound {before : Reference.RiscV.Sail.State}
    {timestamp : ZMod p × ZMod p} {state : PCState.State p} (hp : limbBase < p)
    (initial : initialState before timestamp = some state) : state.word.Bounded := by
  obtain ⟨pc, _, rfl⟩ := initial_state_source initial
  exact PCState.Proofs.encoded_bounds hp pc

/-- The public constructor supplies the actual Sail PC read, not merely
    bounds for the native encoding. -/
theorem initial_state_pc {before : Reference.RiscV.Sail.State}
    {timestamp : ZMod p × ZMod p} {state : PCState.State p} (hp : limbBase < p)
    (initial : initialState before timestamp = some state) :
    run (SailRV32.Functions.get_arch_pc ()) before = .ok state.word.toBitVec before := by
  obtain ⟨pc, read, rfl⟩ := initial_state_source initial
  have bounds := Word.ofBitVec_bound pc
  change pc.toNat % limbBase < limbBase ∧ pc.toNat / limbBase < limbBase at bounds
  have encoded : (PCState.boundary (p := p) pc timestamp).word = Word.ofBitVec pc := by
    change Word.mk ((pc.toNat % limbBase : Nat) : ZMod p).val
      ((pc.toNat / limbBase : Nat) : ZMod p).val = Word.ofBitVec pc
    rw [ZMod.val_natCast_of_lt (lt_trans bounds.1 hp),
      ZMod.val_natCast_of_lt (lt_trans bounds.2 hp)]
    rfl
  rw [encoded, Word.ofBitVec_roundtrip]
  exact read

end Airbender.Trace.Proofs
