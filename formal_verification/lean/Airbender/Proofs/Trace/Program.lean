import Airbender.Review.Helpers.Decoder.Program
import Airbender.Proofs.Trace.InitialImage

namespace Airbender.Trace.Proofs
open Arithmetic

theorem entry_source {Kind : Type} {before : Reference.RiscV.Sail.State} {pc : BitVec 32}
    {entry : ProgramEntry Kind}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (image : programEntryWith projection before pc = some entry) :
    entry.pc = pc ∧ entry.SourceWith before projection := by
  unfold programEntryWith at image
  cases read : (Cell.ram pc).read before with
  | error error after => simp [read, bind, Option.bind] at image
  | ok bits after =>
    have frame := cell_read_frame (.ram pc) read
    subst after
    simp only [read, bind, Option.bind] at image
    cases decoded : SailRV32.Functions.encdec_backwards bits with
    | impure _ _ => simp [decoded] at image
    | pure instruction =>
      simp only [decoded] at image
      cases fields : projection instruction with
      | none => simp [fields] at image
      | some data =>
        simp only [fields, pure, Option.some.injEq] at image
        subst entry
        exact ⟨rfl, ⟨read, by rw [decoded]; rfl, fields⟩⟩

theorem program_sources {Kind : Type} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List (ProgramEntry Kind)}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (image : programImageWith projection before addresses = some program) :
    ∀ entry ∈ program, entry.SourceWith before projection := by
  unfold programImageWith at image
  induction addresses generalizing program with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at image
    subst program
    simp
  | cons address addresses ih =>
    rw [List.mapM_cons] at image
    cases first : programEntryWith projection before address with
    | none => simp [first, bind, Option.bind] at image
    | some entry =>
      cases rest : addresses.mapM (programEntryWith projection before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some entries =>
        simp only [first, rest, bind, Option.bind, pure,
          Option.some.injEq] at image
        subst program
        intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact (entry_source first).2
        · exact ih rest actual member

theorem decoder_field_bounds {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : decoderFields instruction = some data) : data.immediate.Bounded ∧ data.mask ≤ 16 := by
  unfold decoderFields at fields
  split at fields
  all_goals first
    | (simp only [Option.some.injEq] at fields
       subst data
       exact ⟨Word.ofBitVec_bound _, by dsimp [arithmeticFields]; omega⟩)
    | cases fields

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
  have low := congrArg (fun q : Vector (ZMod p) 10 => q[0]) equal
  have high := congrArg (fun q : Vector (ZMod p) 10 => q[1]) equal
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
  have low := congrArg (fun q : Vector (ZMod p) 10 => q[6]) equal
  have high := congrArg (fun q : Vector (ZMod p) 10 => q[7]) equal
  change w decoder.immediate[0] = (entry.data.immediate.lo : ZMod p) at low
  change w decoder.immediate[1] = (entry.data.immediate.hi : ZMod p) at high
  rw [low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 hp),
    ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]

/-- Canonical register indices from any family's imported ten-column query. -/
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
  exact ⟨scalar (congrArg (fun q : Vector (ZMod p) 10 => q[2]) equal),
    scalar (congrArg (fun q : Vector (ZMod p) 10 => q[3]) equal),
    scalar (congrArg (fun q : Vector (ZMod p) 10 => q[4]) equal)⟩

/-- All three native register indices are fixed by the same decoder query. -/
theorem query_register_indices {p : Nat} (hp : limbBase < p) {row : Row p} {entry : ProgramEntry}
    (equal : row.decoderQuery = entry.query) :
    (row.assignment row.decoderColumns.rs1).val = entry.data.rs1.toNat ∧
    (row.assignment row.decoderColumns.rs2).val = entry.data.rs2.toNat ∧
    (row.assignment row.decoderColumns.rd).val = entry.data.rd.toNat :=
  native_query_indices hp equal

end Airbender.Trace.Proofs
