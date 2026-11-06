import Human.Helpers.Decoder.Program
import Slop.Trace.InitialImage
import Slop.Trace.DecoderBits
import Slop.Sail.DecoderFrame
import Slop.Sail.ResetState
import Human.Helpers.Context.FamilyLayout
import Human.Helpers.Decoder.Decoded
namespace Airbender.Trace.Proofs
open Arithmetic

private theorem arithmetic_field_bounds (rs1 rs2 rd : BitVec 5) (bits : BitVec 32)
    {mask : Nat} (small : mask ≤ 4) :
    (arithmeticFields rs1 rs2 rd bits mask).immediate.Bounded ∧
      (arithmeticFields rs1 rs2 rd bits mask).mask ≤ 4 := by
  unfold arithmeticFields
  split
  · exact ⟨by simp [Word.Bounded, limbBase], by decide⟩
  · exact ⟨Word.ofBitVec_bound bits, small⟩

theorem decoder_field_bounds {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : decoderFields instruction = some data) : data.immediate.Bounded ∧ data.mask ≤ 4 := by
  unfold decoderFields at fields
  split at fields
  case h_6 =>
    rename_i original imm rs1 rd
    change (if (rd : BitVec 5) = 0 then some (arithmeticFields 0 0 0 0 1)
      else some ⟨.wordMemory, rs1, 0, rd,
        Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩) = some data at fields
    by_cases zero : (rd : BitVec 5) = 0
    · rw [ite_eq_left zero, Option.some.injEq] at fields
      subst data
      exact arithmetic_field_bounds _ _ _ _ (by decide)
    · rw [ite_eq_right zero, Option.some.injEq] at fields
      subst data
      exact ⟨Word.ofBitVec_bound _, by change 0 ≤ 4; decide⟩
  all_goals first
    | (simp only [Option.some.injEq] at fields
       subst data
       exact arithmetic_field_bounds _ _ _ _ (by decide))
    | (simp only [Option.some.injEq] at fields
       subst data
       exact ⟨Word.ofBitVec_bound _, by dsimp; omega⟩)
    | (cases fields)

open Lean Meta Elab Tactic in
/-- Find `Configured state` in the local context (a hypothesis, or the `configuration` field of a
    hypothesis, also through `boot`, `inputs`, `initialization`, `publicProgram`), or a `Configured`
    theorem of the current file (test fixtures). Proof search only. -/
elab "find_configured" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    for path in [[], [`configuration], [`boot, `configuration], [`inputs, `configuration],
        [`initialization, `configuration], [`boundary, `configuration],
        [`publicProgram, `configuration], [`toSharedMemoryInputs, `publicProgram, `configuration]] do
      let saved ← saveState
      try
        let base ← Term.exprToSyntax decl.toExpr
        let stx ← path.foldlM (fun (acc : TSyntax `term) field => `($acc.$(mkIdent field):ident)) base
        let value ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTermEnsuringType stx target
        if (← instantiateMVars value).hasExprMVar then throwError "open"
        goal.assign value
        replaceMainGoal []
        return
      catch _ => restoreState saved
  -- `Configured` theorems of the current file (test fixtures), possibly with parameters.
  for (name, info) in (← getEnv).constants.map₂.toList do
    let type := info.type
    let (_, _, body) ← forallMetaTelescope type
    unless body.isAppOf ``Airbender.Reference.RiscV.Sail.Configured do continue
    let saved ← saveState
    try
      let (args, _, body) ← forallMetaTelescope type
      if ← isDefEq body target then
        let value ← instantiateMVars (mkAppN (← mkConstWithFreshMVarLevels name) args)
        if value.hasExprMVar then throwError "open"
        goal.assign value
        replaceMainGoal []
        return
      restoreState saved
    catch _ => restoreState saved
  throwError "find_configured: no `Configured` fact for {target}"

theorem entry_source {Kind : Type} {before : Reference.RiscV.Sail.State} {pc : BitVec 32}
    {entry : ProgramEntry Kind}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (configured : Reference.RiscV.Sail.Configured before)
    (image : programEntryWith projection before pc = some entry) :
    entry.pc = pc ∧ entry.SourceWith before projection := by
  unfold programEntryWith at image
  split at image
  · cases image
  cases read : (Cell.ram pc).read before with
  | error error after => simp [read, bind, Option.bind] at image
  | ok bits after =>
    have frame := cell_read_frame (.ram pc) read
    subst after
    simp only [read, bind, Option.bind] at image
    cases decoded : Reference.RiscV.Sail.decodeOnReset bits with
    | none => simp [decoded] at image
    | some instruction =>
      simp only [decoded] at image
      cases fields : projection instruction with
      | none => simp [fields] at image
      | some data =>
        simp only [fields, pure, Option.some.injEq] at image
        subst entry
        exact ⟨rfl, ⟨read, Reference.RiscV.Sail.decode_on_reset_run configured decoded, fields⟩⟩

/-- Every entry of a public program image comes from the bytes and the decoder of a `Configured` state. -/
theorem program_sources {Kind : Type} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List (ProgramEntry Kind)}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (image : programImageWith projection before addresses = some program)
    (entry : ProgramEntry Kind) (present : entry ∈ program)
    (configured : Reference.RiscV.Sail.Configured before := by find_configured) :
    entry.SourceWith before projection := by
  unfold programImageWith at image
  induction addresses generalizing program with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at image
    subst program
    simp at present
  | cons address addresses ih =>
    rw [List.mapM_cons] at image
    cases first : programEntryWith projection before address with
    | none => simp [first, bind, Option.bind] at image
    | some head =>
      cases rest : addresses.mapM (programEntryWith projection before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some entries =>
        simp only [first, rest, bind, Option.bind, pure, Option.some.injEq] at image
        subst program
        rcases List.mem_cons.mp present with rfl | present
        · exact (entry_source configured first).2
        · exact ih rest present

/-- Native metadata of a public image entry (no decoder run needed). -/
theorem decoder_fields_of_image {Kind : Type} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List (ProgramEntry Kind)}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (image : programImageWith projection before addresses = some program)
    (entry : ProgramEntry Kind) (present : entry ∈ program) :
    projection entry.instruction = some entry.data := by
  unfold programImageWith at image
  induction addresses generalizing program with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at image
    subst program
    simp at present
  | cons address addresses ih =>
    rw [List.mapM_cons] at image
    cases first : programEntryWith projection before address with
    | none => simp [first, bind, Option.bind] at image
    | some head =>
      cases rest : addresses.mapM (programEntryWith projection before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some entries =>
        simp only [first, rest, bind, Option.bind, pure, Option.some.injEq] at image
        subst program
        rcases List.mem_cons.mp present with rfl | present
        · unfold programEntryWith at first
          split at first
          · cases first
          cases read : (Cell.ram address).read before with
          | error => simp [read, bind, Option.bind] at first
          | ok bits after =>
            simp only [read, bind, Option.bind] at first
            cases decoded : Reference.RiscV.Sail.decodeOnReset bits with
            | none => simp [decoded] at first
            | some instruction =>
              simp only [decoded] at first
              cases fields : projection instruction with
              | none => simp [fields] at first
              | some data =>
                simp only [fields, pure, Option.some.injEq] at first
                subst_vars
                exact fields
        · exact ih rest present

/-- The same as `program_sources` (the former stateful image). -/
abbrev run_program_sources := @program_sources

theorem decoder_member {Kind : Type} [DecidableEq Kind]
    {p : Nat} [Fact p.Prime] {program : List (ProgramEntry Kind)}
    {family : Kind} {query : Vector (ZMod p) 9}
    (member : (decoderTable program family).Contains #[] query) :
    ∃ entry ∈ program, entry.data.family = family ∧ query = entry.query := by
  change ∃ i, query = ((program.filter fun entry => entry.data.family == family).get i).query at member
  obtain ⟨i, equal⟩ := member
  have present := List.get_mem (program.filter fun entry => entry.data.family == family) i
  obtain ⟨present, selected⟩ := List.mem_filter.mp present
  exact ⟨_, present, by simpa using selected, equal⟩

theorem word_of_pc_query {p : Nat} (hp : limbBase < p) {lo hi : ZMod p} {pc : BitVec 32}
    (low : lo = ((Word.ofBitVec pc).lo : ZMod p))
    (high : hi = ((Word.ofBitVec pc).hi : ZMod p)) :
    (⟨lo.val, hi.val⟩ : Word) = Word.ofBitVec pc := by
  have bound := Word.ofBitVec_bound pc
  rw [low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 hp),
    ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]

/-- The native fetch query fixes both canonical PC limbs, for any family. -/
theorem native_query_pc_word {Kind : Type} {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p}
    {entry : ProgramEntry Kind}
    (equal : nativeDecoderQuery columns decoder w = entry.query) :
    (⟨(w columns.initialPC[0]).val, (w columns.initialPC[1]).val⟩ : Word) =
      Word.ofBitVec entry.pc := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[0]) equal
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[1]) equal
  change w columns.initialPC[0] = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
  change w columns.initialPC[1] = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
  exact word_of_pc_query hp low high

/-- The same imported query fixes immediate limbs for every circuit family. -/
theorem native_query_immediate_word {Kind : Type} {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p}
    {entry : ProgramEntry Kind} (bound : entry.data.immediate.Bounded)
    (equal : nativeDecoderQuery columns decoder w = entry.query) :
    (⟨(w decoder.immediate[0]).val, (w decoder.immediate[1]).val⟩ : Word) =
      entry.data.immediate := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) equal
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) equal
  change w decoder.immediate[0] = (entry.data.immediate.lo : ZMod p) at low
  change w decoder.immediate[1] = (entry.data.immediate.hi : ZMod p) at high
  rw [low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 hp),
    ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]

/-- Canonical register indices from any family's imported nine-column query. -/
theorem native_query_indices {Kind : Type} {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p}
    {entry : ProgramEntry Kind}
    (equal : nativeDecoderQuery columns decoder w = entry.query) :
    (w decoder.rs1).val = entry.data.rs1.toNat ∧
    (w decoder.rs2).val = entry.data.rs2.toNat ∧
    (w decoder.rd).val = entry.data.rd.toNat := by
  have scalar {column : Nat} {index : BitVec 5}
      (same : w column = (index.toNat : ZMod p)) : (w column).val = index.toNat := by
    rw [same, ZMod.val_natCast_of_lt (lt_trans index.isLt (by dsimp [limbBase] at hp; omega))]
  exact ⟨scalar (congrArg (fun q : Vector (ZMod p) 9 => q[2]) equal),
    scalar (congrArg (fun q : Vector (ZMod p) 9 => q[3]) equal),
    scalar (congrArg (fun q : Vector (ZMod p) 9 => q[4]) equal)⟩

end Airbender.Trace.Proofs
