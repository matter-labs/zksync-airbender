import Airbender.Review.Helpers.Decoder.ModularExternal
import Airbender.Review.Trace.Workers.Keccak.SplitSchedule

namespace Airbender.Trace.NativeDecoder.ProgramRows
open Reference.RiscV.Sail Reference.Sail Arithmetic

/-- The two Rust preprocessing configurations used by the unrolled setup
machines. This is a Lean model; equality to Rust output needs a differential
test for every admitted public program. -/
inductive Config where
  | fullUnsigned | reduced
  deriving DecidableEq

def Config.fields (config : Config) :
    SailRV32.instruction → Option (DecoderData PooledFamily) :=
  match config with
  | .fullUnsigned => AddSub.Modular.External.decoderFields
  | .reduced => fun instruction =>
      (AddSub.Modular.External.decoderFields instruction).filter fun data =>
        match data.family with
        | .addSub | .jumpBranchSlt | .shiftBinop | .wordMemory => true
        | .mulDiv | .subwordMemory => false

/-- Decode one public text word at its native byte PC. Unsupported words have
no entry. The original Sail instruction and native-family projection remain
visible in the entry, independently of witness values. -/
def wordEntry (config : Config) (initial : State) (bits : BitVec 32)
    (index : Nat) : Option PooledProgramEntry := do
  let instruction ← match run (SailRV32.Functions.encdec_backwards bits) initial with
    | .ok instruction _ => some instruction
    | .error _ _ => none
  let data ← config.fields instruction
  pure ⟨BitVec.ofNat 32 (4 * index), bits, instruction, data⟩

/-- Public entries for all supported words; unsupported encodings are retained
as holes in the row function below, rather than rejecting the whole program. -/
def programOf (config : Config) (initial : State) (text : List (BitVec 32)) :
    List PooledProgramEntry :=
  text.zipIdx.filterMap fun (bits, index) => wordEntry config initial bits index

/-- The native preprocessor reserves the add/sub decoder for admitted virtual
CSR calls. The full 12-bit CSR is a request identifier, not a five-bit GPR.
Rust accepts these instructions only as well-formed public call groups; the
group-shape premise is kept separate from this per-word projection. -/
def Config.delegationCSR (config : Config) : Nat → Bool
  | 0x7c7 => true
  | 0x7ca | 0x7cb | 0x7cc | 0x7cd | 0x7ce => config == .fullUnsigned
  | _ => false

/-- Public instruction encoding of `csrrw x0, csr, x0`. -/
def csrWord (csr : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (csr * 1048576 + 0x1073)

def RepeatedCallGroup (text : List (BitVec 32)) (word : BitVec 32)
    (size index : Nat) : Prop :=
  ∃ start, start ≤ index ∧ index < start + size ∧
    (∀ offset < size, text[start + offset]? = some word) ∧
    (start = 0 ∨ text[start - 1]? ≠ some word) ∧
    text[start + size]? ≠ some word

/-- The blessed 361-call sequence is the public Rust wrapper's split order.
This checks code shape only; worker control, pointer and functional conditions
remain separate public-use and circuit obligations. -/
def SplitCallGroup (text : List (BitVec 32)) (index : Nat) : Prop :=
  ∃ start, start ≤ index ∧ index < start + 361 ∧
    ∀ offset < 361,
      text[start + offset]? = some (csrWord (Keccak.Split.kindAt offset).csr)

/-- Public syntax accepted by native delegation preprocessing. This is an
explicit program premise: the per-word row projection alone cannot justify a
native group, and it does not assume any witness values or worker results. -/
structure WellFormedDelegationText (config : Config)
    (text : List (BitVec 32)) : Prop where
  blake : ∀ (index : Nat), text[index]? = some (csrWord 0x7c7) →
    RepeatedCallGroup text (csrWord 0x7c7) 7 index ∨
      RepeatedCallGroup text (csrWord 0x7c7) 10 index
  special5 : config = .fullUnsigned → ∀ (index : Nat),
    text[index]? = some (csrWord 0x7cb) →
      RepeatedCallGroup text (csrWord 0x7cb) 649 index
  split : config = .fullUnsigned → ∀ (index : Nat),
    (text[index]? = some (csrWord 0x7cc) ∨
      text[index]? = some (csrWord 0x7cd) ∨
      text[index]? = some (csrWord 0x7ce)) → SplitCallGroup text index
  fullNoG : config = .fullUnsigned → ∀ (index : Nat),
    text[index]? ≠ some (csrWord 0x7c8)
  reducedAllowlist : config = .reduced → ∀ (index : Nat),
    text[index]? ≠ some (csrWord 0x7c8) ∧
    text[index]? ≠ some (csrWord 0x7ca) ∧
    text[index]? ≠ some (csrWord 0x7cb) ∧
    text[index]? ≠ some (csrWord 0x7cc) ∧
    text[index]? ≠ some (csrWord 0x7cd) ∧
    text[index]? ≠ some (csrWord 0x7ce)

structure CallerEntry where
  pc : BitVec 32
  bits : BitVec 32
  instruction : SailRV32.instruction
  csr : Nat

def callerEntryWith (allowed : Nat → Bool) (initial : State) (bits : BitVec 32)
    (index : Nat) : Option CallerEntry := do
  let instruction ← match run (SailRV32.Functions.encdec_backwards bits) initial with
    | .ok instruction _ => some instruction
    | .error _ _ => none
  match instruction with
  | .CSRReg (address, .Regidx source, .Regidx destination, .CSRRW) =>
      if source == 0 && destination == 0 && allowed address.toNat then
        some ⟨BitVec.ofNat 32 (4 * index), bits, instruction, address.toNat⟩
      else none
  | _ => none

def callerEntry (config : Config) (initial : State) (bits : BitVec 32)
    (index : Nat) : Option CallerEntry :=
  callerEntryWith config.delegationCSR initial bits index

def CallerEntry.query {p : Nat} (entry : CallerEntry) : Vector (ZMod p) 9 :=
  let pc := Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, 0, entry.csr, 0, 0, 0, 0, 128]

abbrev NativeEntry := PooledProgramEntry ⊕ CallerEntry

def nativeEntry (config : Config) (initial : State) (bits : BitVec 32)
    (index : Nat) : Option NativeEntry :=
  (callerEntry config initial bits index).map Sum.inr <|>
    (wordEntry config initial bits index).map Sum.inl

def nativeProgramOf (config : Config) (initial : State) (text : List (BitVec 32)) :
    List NativeEntry :=
  text.zipIdx.filterMap fun (bits, index) => nativeEntry config initial bits index

def NativeEntry.family : NativeEntry → PooledFamily
  | .inl entry => entry.data.family
  | .inr _ => .addSub

def NativeEntry.query {p : Nat} : NativeEntry → Vector (ZMod p) 9
  | .inl entry => entry.query
  | .inr entry => entry.query

/-- Logical table for both ordinary rows and full-width virtual CSR caller
rows. Its membership is still an exact-lookup premise at the circuit boundary. -/
def nativeDecoderTable {p : Nat} [Fact p.Prime]
    (program : List NativeEntry) (family : PooledFamily) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.NativeProgramDecoder"
  length := (program.filter fun entry => entry.family == family).length
  row i := ((program.filter fun entry => entry.family == family).get i).query
  index query := (program.filter fun entry => entry.family == family).toArray.findIdx
    (fun entry => entry.query == query)
  Spec query := ∃ entry ∈ program, entry.family = family ∧ query = entry.query
  contains_iff := by
    intro query
    constructor
    · rintro ⟨i, rfl⟩
      have member := List.get_mem (program.filter fun entry => entry.family == family) i
      obtain ⟨member, selected⟩ := List.mem_filter.mp member
      exact ⟨_, member, by simpa using selected, rfl⟩
    · rintro ⟨entry, member, selected, equal⟩
      have filtered : entry ∈ program.filter (fun entry => entry.family == family) := by
        simp [member, selected]
      obtain ⟨i, index⟩ := List.mem_iff_get.mp filtered
      exact ⟨i, equal.trans (congrArg NativeEntry.query index).symm⟩ }

/-- Rust uses minus one in every selected column for an unsupported word. -/
def sentinel {p : Nat} : Vector (ZMod p) 9 :=
  #v[-1, -1, -1, -1, -1, -1, -1, -1, -1]

def familyRow {p : Nat} (config : Config) (initial : State)
    (family : PooledFamily) (bits : BitVec 32) (index : Nat) :
    Vector (ZMod p) 9 :=
  match wordEntry config initial bits index with
  | some entry => if entry.data.family = family then entry.query else sentinel
  | none => sentinel

/-- Public word row after the native delegation-call preprocessing projection.
The actual Rust preprocessor additionally validates complete call groups; a
program-level well-formedness premise is required at that boundary. -/
def nativeFamilyRow {p : Nat} (config : Config) (initial : State)
    (family : PooledFamily) (bits : BitVec 32) (index : Nat) :
    Vector (ZMod p) 9 :=
  match nativeEntry config initial bits index with
  | some entry => if entry.family = family then entry.query else sentinel
  | none => sentinel

/-- One row per public word index, followed by unsupported padding up to the
native ROM capacity. -/
def rows {p : Nat} (config : Config) (initial : State)
    (text : List (BitVec 32)) (capacity : Nat)
    (_fits : text.length ≤ capacity) (family : PooledFamily) :
    List (Vector (ZMod p) 9) :=
  text.zipIdx.map (fun (bits, index) => familyRow config initial family bits index) ++
    List.replicate (capacity - text.length) sentinel

def nativeRows {p : Nat} (config : Config) (initial : State)
    (text : List (BitVec 32)) (capacity : Nat)
    (_fits : text.length ≤ capacity) (family : PooledFamily) :
    List (Vector (ZMod p) 9) :=
  text.zipIdx.map (fun (bits, index) => nativeFamilyRow config initial family bits index) ++
    List.replicate (capacity - text.length) sentinel

/-- The native setup keeps precisely the columns selected by its circuit mask,
in their original order. A mask has the full nine-column width and selects both
PC limbs, as required by Rust's materializer. -/
structure Mask where
  columns : Array Bool
  width : columns.size = 9
  pcLow : columns[0]?.getD false = true
  pcHigh : columns[1]?.getD false = true

def maskRow {p : Nat} (mask : Mask) (row : Vector (ZMod p) 9) : List (ZMod p) :=
  row[0] :: row[1] ::
  ((mask.columns.toList.drop 2).zip (row.toList.drop 2)).filterMap fun (selected, value) =>
    if selected then some value else none

/-- Program-dependent decoder columns, including unsupported and padded rows.
The remaining premise for a native circuit is equality of its imported setup
columns to these rows; this definition alone does not assert that equality. -/
def nativeDecoderRows {p : Nat} (config : Config) (initial : State)
    (text : List (BitVec 32)) (capacity : Nat)
    (fits : text.length ≤ capacity) (family : PooledFamily) (mask : Mask) :
    List (List (ZMod p)) :=
  (nativeRows config initial text capacity fits family).map (maskRow mask)

end Airbender.Trace.NativeDecoder.ProgramRows
