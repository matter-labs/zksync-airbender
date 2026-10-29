import Airbender.Review.Helpers.Decoder.ProgramRows
import Airbender.Review.Helpers.UnifiedReduced.Modular

namespace Airbender.Trace.NativeDecoder.UnifiedProgramRows
open Reference.RiscV.Sail Reference.Sail
open Airbender.Trace.NativeDecoder.ProgramRows

/-- The unified setup's Rust allowlist. Split Keccak belongs to the full
unrolled machine; unified keeps special5 and Blake2 G. -/
def delegationCSR : Nat → Bool
  | 0x7c7 | 0x7c8 | 0x7ca | 0x7cb => true
  | _ => false

/-- Unified's public group-shape premise. Bigint calls are singletons; split
Keccak CSR words are outside this setup's allowlist. -/
structure WellFormedDelegationText (text : List (BitVec 32)) : Prop where
  blake : ∀ (index : Nat), text[index]? = some (csrWord 0x7c7) →
    RepeatedCallGroup text (csrWord 0x7c7) 7 index ∨
      RepeatedCallGroup text (csrWord 0x7c7) 10 index
  g : ∀ (index : Nat), text[index]? = some (csrWord 0x7c8) →
    RepeatedCallGroup text (csrWord 0x7c8) 56 index ∨
      RepeatedCallGroup text (csrWord 0x7c8) 80 index
  special5 : ∀ (index : Nat), text[index]? = some (csrWord 0x7cb) →
    RepeatedCallGroup text (csrWord 0x7cb) 649 index
  noSplit : ∀ (index : Nat),
    text[index]? ≠ some (csrWord 0x7cc) ∧
    text[index]? ≠ some (csrWord 0x7cd) ∧
    text[index]? ≠ some (csrWord 0x7ce)

/-- Existing unified ordinary, custom and modular projections, extended with
the `0x7c0` external stream forms. Each branch retains its original Sail
instruction and native metadata. -/
def decoderFields (instruction : SailRV32.instruction) :
    Option (DecoderData UnifiedFamily) :=
  match instruction with
  | .CSRReg (csr, _, _, .CSRRW) =>
      if csr = 0x7c0 then
        (NonDeterminism.decoderFields instruction).map UnifiedReduced.arithmeticFields
      else UnifiedReduced.Modular.decoderFields instruction
  | _ => UnifiedReduced.Modular.decoderFields instruction

abbrev Entry := UnifiedReduced.ProgramEntry ⊕ CallerEntry

def entry (initial : State) (bits : BitVec 32) (index : Nat) : Option Entry :=
  (callerEntryWith delegationCSR initial bits index).map Sum.inr <|> do
    let instruction ← match SailRV32.Functions.encdec_backwards bits with
      | .pure instruction => some instruction
      | .impure _ _ => none
    let data ← decoderFields instruction
    pure <| Sum.inl ⟨BitVec.ofNat 32 (4 * index), bits, instruction, data⟩

def Entry.query {p : Nat} : Entry → Vector (ZMod p) 9
  | .inl ordinary => ordinary.query
  | .inr caller => caller.query

def programOf (initial : State) (text : List (BitVec 32)) : List Entry :=
  text.zipIdx.filterMap fun (bits, index) => entry initial bits index

/-- The public ordinary/custom/MOP instruction entries after removing virtual
CSR callers. The caller branch remains in `programOf` for its own binding. -/
def ordinaryProgramOf (initial : State) (text : List (BitVec 32)) :
    List UnifiedReduced.ProgramEntry :=
  (programOf initial text).filterMap fun
    | .inl ordinary => some ordinary
    | .inr _ => none

def decoderTable {p : Nat} [Fact p.Prime] (program : List Entry) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.UnifiedNativeProgramDecoder"
  length := program.length
  row i := (program.get i).query
  index values := program.toArray.findIdx (fun item => item.query == values)
  Spec values := ∃ item ∈ program, values = item.query
  contains_iff := by
    intro values
    constructor
    · rintro ⟨i, equal⟩
      exact ⟨program.get i, List.get_mem _ _, equal⟩
    · rintro ⟨item, member, equal⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
      exact ⟨i, equal⟩ }

def wordRow {p : Nat} (initial : State) (bits : BitVec 32) (index : Nat) :
    Vector (ZMod p) 9 :=
  match entry initial bits index with
  | some decoded => decoded.query
  | none => sentinel

def rows {p : Nat} (initial : State) (text : List (BitVec 32)) (capacity : Nat)
    (_fits : text.length ≤ capacity) : List (Vector (ZMod p) 9) :=
  text.zipIdx.map (fun (bits, index) => wordRow initial bits index) ++
    List.replicate (capacity - text.length) sentinel

def nativeDecoderRows {p : Nat} (initial : State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity) (mask : Mask) :
    List (List (ZMod p)) :=
  (rows initial text capacity fits).map (maskRow mask)

end Airbender.Trace.NativeDecoder.UnifiedProgramRows
