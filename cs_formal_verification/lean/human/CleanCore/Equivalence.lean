module
public import CleanCore
public import Clean.Circuit.Operations
public import Clean.Specs.Keccak256
public import Clean.Specs.BLAKE3
public import Clean.Utils.Bits
public import Clean.Utils.Field
public import Clean.Utils.OfflineMemory
public import Clean.Utils.Rotation

@[expose] public section

/-! # CleanCore is Clean

`CleanCore` (namespace `Airbender`) transcribes the part of Clean (Verified-zkEVM/clean, pinned b41c196 =
tag v4.35.0 in `lakefile.toml`) that the spec and the proofs use. This file is the only one in `human/` that
imports Clean; it is a leaf (nothing imports it), checked on every build.

What it shows, per transcribed definition:
* constraint semantics: our expressions, environments, tables, lookups and flat operations translate one to
  one into Clean's (`toClean`), and evaluation, lookup containment and `ConstraintsHoldFlat` agree on the
  translation;
* specifications and utilities (Keccak-f[1600], BLAKE3, rotations, byte splitting, offline memory): each is equal to
  Clean's definition.

Deviations (by design; each is visible in the statements below):
1. `Airbender.FlatOperation` has only `assert` and `lookup`. Clean's `witness` (witness generation) and
   `interact` (channel interaction, balanced globally) impose no local constraint in Clean's
   `ConstraintsHoldFlat`, and the importer never emits them: `constraintsHoldFlat_iff` is stated for the
   image of the translation.
2. Our constraint semantics needs only `[Field F]`; Clean's needs `[FiniteField F]` (a field with a
   canonical embedding into `ℕ`). The correspondence is stated for every `FiniteField`, with our side at its
   underlying field; `ZMod p` for prime `p` (the only field our statements use) is one.
3. Omitted: prover-only data (`ProverEnvironment`, hints), Clean's circuit/gadget layer, the BLAKE3
   compression/chunking and the Keccak sponge, and lemmas our proofs do not cite.

Clean definitions and lemmas only the proofs use (bit decompositions, source–sink paths, per-address memory
filtering, the constraint and lookup lists) are transcribed in `proven/Proven/CleanCore/` and need no correspondence:
no claim mentions them. -/

namespace Airbender.CleanEquivalence

variable {F : Type}

/-! ## Constraint semantics -/

def Expression.toClean : Airbender.Expression F → _root_.Expression F
  | .var v => .var ⟨v.index⟩
  | .const c => .const c
  | .add a b => .add (Expression.toClean a) (Expression.toClean b)
  | .mul a b => .mul (Expression.toClean a) (Expression.toClean b)

def Environment.toClean (env : Airbender.Environment F) : _root_.Environment F := ⟨env.get, env.data⟩

def RawTable.toClean (t : Airbender.RawTable F) : _root_.RawTable F :=
  ⟨t.name, t.arity, t.Contains, t.Soundness, t.Completeness, t.imply_soundness, t.implied_by_completeness⟩

def Lookup.toClean (l : Airbender.Lookup F) : _root_.Lookup F :=
  ⟨RawTable.toClean l.table, l.entry.map Expression.toClean⟩

def FlatOperation.toClean : Airbender.FlatOperation F → _root_.FlatOperation F
  | .assert e => .assert (Expression.toClean e)
  | .lookup l => .lookup (Lookup.toClean l)

section
variable [FiniteField F]

theorem eval_toClean (env : Airbender.Environment F) (e : Airbender.Expression F) :
    (Expression.toClean e).eval (Environment.toClean env) = e.eval env := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add a b iha ihb => simp only [Expression.toClean, _root_.Expression.eval, Airbender.Expression.eval, iha, ihb]
  | mul a b iha ihb => simp only [Expression.toClean, _root_.Expression.eval, Airbender.Expression.eval, iha, ihb]

theorem contains_toClean (env : Airbender.Environment F) (l : Airbender.Lookup F) :
    (Lookup.toClean l).Contains (Environment.toClean env) ↔ l.Contains env := by
  have h : (l.entry.map Expression.toClean).map (Environment.toClean env) = l.entry.map env := by
    ext i hi
    simp only [Vector.getElem_map]
    exact eval_toClean env _
  simp only [_root_.Lookup.Contains, Airbender.Lookup.Contains, Lookup.toClean, RawTable.toClean]
  rw [show (Environment.toClean env).data = env.data from rfl]
  exact Iff.of_eq (congrArg _ h)

/-- The satisfaction relation of an imported circuit is Clean's, on the translated operations. -/
theorem constraintsHoldFlat_iff (env : Airbender.Environment F) (ops : List (Airbender.FlatOperation F)) :
    Airbender.FlatOperation.ConstraintsHoldFlat env ops ↔
      _root_.FlatOperation.ConstraintsHoldFlat (Environment.toClean env) (ops.map FlatOperation.toClean) := by
  induction ops with
  | nil => exact Iff.rfl
  | cons op ops ih =>
    cases op with
    | assert e =>
      simp only [Airbender.FlatOperation.ConstraintsHoldFlat, _root_.FlatOperation.ConstraintsHoldFlat,
        List.map_cons, FlatOperation.toClean, ih]
      exact and_congr (by rw [← eval_toClean env e]) Iff.rfl
    | lookup l =>
      simp only [Airbender.FlatOperation.ConstraintsHoldFlat, _root_.FlatOperation.ConstraintsHoldFlat,
        List.map_cons, FlatOperation.toClean, ih]
      exact and_congr (contains_toClean env l).symm Iff.rfl

end

/-! ## Tables: the four row types we use flatten as in Clean -/

/-- A table over one of our row types, as Clean's table over the same row type. -/
def Table.toClean {Row : TypeMap} [Airbender.ProvableType Row] [_root_.ProvableType Row]
    (t : Airbender.Table F Row) : _root_.Table F Row :=
  ⟨t.name, t.Contains, t.Soundness, t.Completeness, t.imply_soundness, t.implied_by_completeness⟩

theorem toRaw_field (t : Airbender.Table F Airbender.field) :
    RawTable.toClean t.toRaw = (Table.toClean (Row := _root_.field) t).toRaw := by rfl

theorem toRaw_fieldPair (t : Airbender.Table F Airbender.fieldPair) :
    RawTable.toClean t.toRaw = (Table.toClean (Row := _root_.fieldPair) t).toRaw := by rfl

theorem toRaw_fieldTriple (t : Airbender.Table F Airbender.fieldTriple) :
    RawTable.toClean t.toRaw = (Table.toClean (Row := _root_.fieldTriple) t).toRaw := by rfl

theorem toRaw_fields {n : ℕ} (t : Airbender.Table F (Airbender.fields n)) :
    RawTable.toClean t.toRaw = (Table.toClean (Row := _root_.fields n) t).toRaw := by rfl

theorem fromStatic_fields {n : ℕ} (t : Airbender.StaticTable F (Airbender.fields n)) :
    Table.toClean (Row := _root_.fields n) (Airbender.Table.fromStatic t) =
      _root_.Table.fromStatic (⟨t.name, t.length, t.row, t.index, t.Spec, t.contains_iff⟩ :
        _root_.StaticTable F (_root_.fields n)) := by rfl

/-! ## Specifications: equal to Clean's definitions -/

theorem keccak_roundConstants : Airbender.Specs.Keccak256.roundConstants = _root_.Specs.Keccak256.roundConstants := by rfl
theorem keccak_thetaC : Airbender.Specs.Keccak256.thetaC = _root_.Specs.Keccak256.thetaC := by rfl
theorem keccak_thetaD : Airbender.Specs.Keccak256.thetaD = _root_.Specs.Keccak256.thetaD := by rfl
theorem keccak_thetaXor : Airbender.Specs.Keccak256.thetaXor = _root_.Specs.Keccak256.thetaXor := by rfl
theorem keccak_theta : Airbender.Specs.Keccak256.theta = _root_.Specs.Keccak256.theta := by rfl
theorem keccak_rhoPi : Airbender.Specs.Keccak256.rhoPi = _root_.Specs.Keccak256.rhoPi := by rfl
theorem keccak_chi : Airbender.Specs.Keccak256.chi = _root_.Specs.Keccak256.chi := by rfl
theorem keccak_iota : Airbender.Specs.Keccak256.iota = _root_.Specs.Keccak256.iota := by rfl
theorem keccak_keccakRound : Airbender.Specs.Keccak256.keccakRound = _root_.Specs.Keccak256.keccakRound := by rfl
theorem keccak_keccakPermutation :
    Airbender.Specs.Keccak256.keccakPermutation = _root_.Specs.Keccak256.keccakPermutation := by rfl

theorem blake3_iv : Airbender.Specs.BLAKE3.iv = _root_.Specs.BLAKE3.iv := by rfl
theorem blake3_g : Airbender.Specs.BLAKE3.g = _root_.Specs.BLAKE3.g := by rfl
theorem blake3_roundConstants : Airbender.Specs.BLAKE3.roundConstants = _root_.Specs.BLAKE3.roundConstants := by rfl
theorem blake3_round : Airbender.Specs.BLAKE3.round = _root_.Specs.BLAKE3.round := by rfl

/-! ## Utilities: equal to Clean's definitions -/

theorem not64_eq : Airbender.not64 = _root_.not64 := by rfl
theorem add32_eq : Airbender.add32 = _root_.add32 := by rfl
theorem rotRight64_eq : Airbender.rotRight64 = _root_.rotRight64 := by rfl
theorem rotRight32_eq : Airbender.rotRight32 = _root_.rotRight32 := by rfl
theorem rotLeft64_eq : Airbender.rotLeft64 = _root_.rotLeft64 := by rfl
theorem splitTwoBytes_eq : Airbender.ByteUtils.splitTwoBytes = _root_.ByteUtils.splitTwoBytes := by rfl

theorem memoryAccess_eq : Airbender.MemoryAccess = _root_.MemoryAccess := by rfl
theorem isTimestampSorted_eq :
    Airbender.MemoryAccessList.isTimestampSorted = _root_.MemoryAccessList.isTimestampSorted := by rfl
theorem lastWriteValue_eq :
    Airbender.MemoryAccessList.lastWriteValue = _root_.MemoryAccessList.lastWriteValue := by
  funext accesses
  induction accesses with
  | nil => rfl
  | cons a rest ih =>
    funext h addr
    obtain ⟨t, a', r, w⟩ := a
    simp only [Airbender.MemoryAccessList.lastWriteValue, _root_.MemoryAccessList.lastWriteValue]
    rw [ih]
theorem isConsistentOnline_eq :
    Airbender.MemoryAccessList.isConsistentOnline = _root_.MemoryAccessList.isConsistentOnline := by
  funext accesses
  induction accesses with
  | nil => rfl
  | cons a rest ih =>
    funext h
    obtain ⟨t, a', r, w⟩ := a
    simp only [Airbender.MemoryAccessList.isConsistentOnline, _root_.MemoryAccessList.isConsistentOnline]
    rw [ih, lastWriteValue_eq]
/-! ## Axioms: the correspondence uses only Lean's standard axioms -/

/-- info: 'Airbender.CleanEquivalence.constraintsHoldFlat_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms constraintsHoldFlat_iff

end Airbender.CleanEquivalence
