module
public import Human.Import.Exec.Decode
public import Slop.Import.Json.Lexical

@[expose] public section

/-! The decoders' combinators are lawful: each returns `a` from a value exactly when the value is `encode a`.
The schema types' instances (`Schema.lean`) follow by composing these lemmas. -/

namespace Airbender.Decode
open Json (Value)
open Serde (encode)

/-- `decode` returns `a` exactly when the value is `encode a`. -/
class Lawful (α : Type) [Serde α] [Decode α] : Prop where
  iff : ∀ (v : Value) (a : α), (decode v : Except String α) = .ok a ↔ encode a = v

theorem decode_encode [Serde α] [Decode α] [Lawful α] (a : α) :
    (decode (encode a) : Except String α) = .ok a :=
  (Lawful.iff _ _).2 rfl

/-- The encoding is never `null` (so `Option` can use `null` for `none`). -/
class NotNull (α : Type) [Serde α] : Prop where
  ne : ∀ a : α, encode a ≠ .null

theorem bind_ok {x : Except String α} {f : α → Except String β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem map_ok {x : Except String α} {f : α → β} {b : β} :
    f <$> x = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Functor.map, Except.map]

theorem pure_ok {a b : α} : (pure a : Except String α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

@[simp] theorem fail_ne (w : String) (a : α) : fail w ≠ .ok a := by simp [fail]

/-! Scalars, options, sequences -/

instance : Lawful Nat where
  iff v n := by
    rcases v with _ | _ | (m | m) | _ | _ | _ <;> simp [decode, fail, encode]
    omega

instance : Lawful Bool where
  iff v b := by cases v <;> simp [decode, fail, encode] <;> exact eq_comm

instance : Lawful String where
  iff v s := by cases v <;> simp [decode, fail, encode] <;> exact eq_comm

instance [Serde α] [Decode α] [Lawful α] [NotNull α] : Lawful (Option α) where
  iff v a := by
    by_cases hv : v = .null
    · subst hv
      show Except.ok none = _ ↔ _
      cases a with
      | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | some x => exact ⟨nofun, fun h => absurd h (NotNull.ne x)⟩
    · have : (decode v : Except String (Option α)) = some <$> decode v := by
        cases v <;> first | exact absurd rfl hv | rfl
      rw [this, map_ok]
      cases a with
      | none => exact ⟨fun ⟨_, _, h⟩ => (nomatch h), fun (h : Value.null = v) => absurd h.symm hv⟩
      | some x =>
        show _ ↔ encode x = v
        rw [← Lawful.iff]
        exact ⟨fun ⟨_, h, he⟩ => by cases he; exact h, fun h => ⟨x, h, rfl⟩⟩

theorem items_iff [Serde α] [Decode α] [Lawful α] :
    ∀ (vs : List Value) (l : List α), items vs = .ok l ↔ l.map encode = vs
  | [], l => by
    cases l
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | v :: vs, l => by
    simp only [items, bind_ok, pure_ok, Lawful.iff, items_iff vs]
    cases l with
    | nil => exact ⟨fun ⟨_, _, _, _, h⟩ => (nomatch h), fun h => (nomatch h)⟩
    | cons a l =>
      simp [List.map_cons, List.cons.injEq]

instance [Serde α] [Decode α] [Lawful α] : Lawful (List α) where
  iff v l := by
    cases v with
    | arr vs => exact (items_iff vs l).trans (by simp only [encode, Value.arr.injEq])
    | _ => exact ⟨fun h => absurd h (fail_ne _ _), nofun⟩

instance [Serde α] [Decode α] [Lawful α] : Lawful (Array α) where
  iff v a := by
    show List.toArray <$> (decode v : Except String (List α)) = .ok a ↔ _
    rw [map_ok]
    constructor
    · rintro ⟨l, h, rfl⟩
      exact (Lawful.iff v l).1 h
    · intro h
      exact ⟨a.toList, (Lawful.iff v a.toList).2 h, rfl⟩

instance [Serde α] [Decode α] [Lawful α] [Serde β] [Decode β] [Lawful β] : Lawful (α × β) where
  iff v p := by
    rcases p with ⟨a, b⟩
    rcases v with _ | _ | _ | _ | (_ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩) | _
    case arr.cons.cons.nil =>
      show (do return ((← decode x : α), (← decode y : β))) = Except.ok (a, b) ↔
        Value.arr [encode a, encode b] = Value.arr [x, y]
      simp only [bind_ok, pure_ok, Lawful.iff, Value.arr.injEq, List.cons.injEq, and_true, Prod.mk.injEq]
      constructor
      · rintro ⟨a', rfl, b', rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; exact ⟨a, rfl, b, rfl, rfl, rfl⟩
    all_goals exact ⟨fun h => absurd h (fail_ne _ _), fun h => by simp [encode] at h⟩

instance : Lawful (BoundedNat bound) where
  iff v n := by
    show (do let m : Nat ← decode v
             if h : m < bound then return (⟨m, h⟩ : BoundedNat bound) else fail _) = _ ↔ _
    rw [bind_ok]
    constructor
    · rintro ⟨m, hm, h⟩
      split at h
      · cases h; exact (Lawful.iff v m).1 hm
      · exact absurd h (fail_ne _ _)
    · intro h
      exact ⟨n.val, (Lawful.iff v n.val).2 h, by simp only [n.isLt, ↓reduceDIte]; rfl⟩

instance [Serde α] [Decode α] [Lawful α] : Lawful (Fixed n α) where
  iff v a := by
    show (do let b : Array α ← decode v
             if h : b.size = n then return (⟨b, h⟩ : Fixed n α) else fail _) = _ ↔ _
    rw [bind_ok]
    constructor
    · rintro ⟨b, hb, h⟩
      split at h
      · cases h; exact (Lawful.iff v b).1 hb
      · exact absurd h (fail_ne _ _)
    · intro h
      exact ⟨a.values, (Lawful.iff v a.values).2 h, by simp only [a.size_eq, ↓reduceDIte]; rfl⟩

instance [Serde α] [Decode α] [Lawful α] [Serde β] [Decode β] [Lawful β] [Serde γ] [Decode γ] [Lawful γ] :
    Lawful (Triple α β γ) where
  iff v t := by
    rcases t with ⟨a, b, c⟩
    rcases v with _ | _ | _ | _ | (_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩⟩) | _
    case arr.cons.cons.cons.nil =>
      show (do return (⟨(← decode x : α), (← decode y : β), (← decode z : γ)⟩ : Triple α β γ)) =
        Except.ok ⟨a, b, c⟩ ↔ Value.arr [encode a, encode b, encode c] = Value.arr [x, y, z]
      simp only [bind_ok, pure_ok, Lawful.iff, Value.arr.injEq, List.cons.injEq, and_true, Triple.mk.injEq]
      constructor
      · rintro ⟨a', rfl, b', rfl, c', rfl, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩; exact ⟨a, rfl, b, rfl, c, rfl, rfl, rfl, rfl⟩
    all_goals exact ⟨fun h => absurd h (fail_ne _ _), fun h => by simp [encode] at h⟩

instance : Lawful JsonNull where
  iff v a := by
    cases a
    cases v
    case null => exact ⟨fun _ => rfl, fun _ => rfl⟩
    all_goals exact ⟨fun h => absurd h (fail_ne _ _), nofun⟩

instance : Lawful Coefficient where
  iff v c := by
    show Coefficient.mk <$> (decode v : Except String (BoundedNat babyBearModulus)) = _ ↔ _
    rw [map_ok]
    constructor
    · rintro ⟨r, h, rfl⟩; exact (Lawful.iff v r).1 h
    · intro h; exact ⟨c.raw, (Lawful.iff v c.raw).2 h, rfl⟩

instance : NotNull Nat := ⟨fun _ => nofun⟩
instance : NotNull (BoundedNat b) := ⟨fun _ => nofun⟩
instance : NotNull Coefficient := ⟨fun _ => nofun⟩
instance [Serde α] [Serde β] : NotNull (α × β) := ⟨fun _ => nofun⟩
instance [Serde α] : NotNull (Array α) := ⟨fun _ => nofun⟩

/-! Map keys and maps -/

/-- `decodeKey` returns `k` exactly when the member name is `ObjectKey.encode k`. -/
class LawfulKey (κ : Type) [ObjectKey κ] [Key κ] : Prop where
  iff : ∀ (s : String) (k : κ), Key.decodeKey s = .ok k ↔ ObjectKey.encode k = s

instance : LawfulKey Nat where
  iff s n := by
    show (if toString _ = s then .ok _ else fail _) = _ ↔ _
    split
    · rename_i h
      simp only [Except.ok.injEq]
      constructor
      · rintro rfl; exact h
      · rintro rfl; exact Json.Parser.digitsValue_utf8 n
    · rename_i h
      simp only [fail_ne, false_iff]
      rintro rfl
      exact h (by show toString (Json.Parser.digitsValue (Json.utf8 (toString n))) = _; rw [Json.Parser.digitsValue_utf8]; rfl)

theorem entries_iff [ObjectKey κ] [Key κ] [LawfulKey κ] [Serde α] [Decode α] [Lawful α] :
    ∀ (ms : List (String × Value)) (l : List (κ × α)),
      entries ms = .ok l ↔ l.map (fun (k, a) => (ObjectKey.encode k, encode a)) = ms
  | [], l => by cases l <;> simp [entries]
  | (s, v) :: ms, l => by
    simp only [entries, bind_ok, pure_ok, Lawful.iff, LawfulKey.iff, entries_iff ms]
    cases l with
    | nil => simp
    | cons p l =>
      rcases p with ⟨k, a⟩
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨_, h1, _, h2, _, h3, ⟨rfl, rfl⟩, rfl⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨k, h1, a, h2, l, h3, ⟨rfl, rfl⟩, rfl⟩

instance [ObjectKey κ] [Key κ] [LawfulKey κ] [Serde α] [Decode α] [Lawful α] : Lawful (ObjectMap κ α) where
  iff v m := by
    rcases m with ⟨⟨l⟩⟩
    cases v with
    | obj ms =>
      show (fun l : List (κ × α) => (⟨l.toArray⟩ : ObjectMap κ α)) <$> entries ms = _ ↔ _
      rw [map_ok]
      simp only [entries_iff]
      constructor
      · rintro ⟨l', rfl, h⟩; cases h; rfl
      · intro h; exact ⟨l, Value.obj.inj h, rfl⟩
    | _ => exact ⟨fun h => absurd h (fail_ne _ _), nofun⟩

/-! Objects: exact member lists -/

/-- The members decoder `m` returns `a` exactly when the members are `e a`. -/
def MLawful (m : Members α) (e : α → List (String × Value)) : Prop :=
  ∀ ms a, m ms = .ok a ↔ e a = ms

theorem done_lawful : MLawful done (fun _ => []) := by
  intro ms a; cases ms <;> simp [done]

theorem field_lawful [Serde α] [Decode α] [Lawful α] (k : String) {m : Members β} {e}
    (h : MLawful m e) : MLawful (field (α := α) k m) (fun p => (k, encode p.1) :: e p.2) := by
  intro ms p
  rcases p with ⟨a, b⟩
  rcases ms with _ | ⟨⟨k', v⟩, ms⟩
  · simp [field]
  · simp only [field]
    split
    · subst k'; simp [bind_ok, map_ok, Lawful.iff, h ms]
    · rename_i hk; simp [Ne.symm hk]

theorem optField_lawful [Serde α] [Decode α] [Lawful α] (k : String) {m : Members β} {e}
    (h : MLawful m e) (hk : ∀ b v, (e b).head? ≠ some (k, v)) :
    MLawful (optField (α := α) k m) (fun p => Json.omitNone k p.1 ++ e p.2) := by
  intro ms p
  rcases p with ⟨oa, b⟩
  rcases ms with _ | ⟨⟨k', v⟩, ms⟩
  · cases oa <;> simp [optField, Json.omitNone, map_ok, h []]
  · simp only [optField]
    split
    · subst k'
      cases oa with
      | none =>
        simp only [bind_ok, pure_ok, Json.omitNone, List.nil_append, Prod.mk.injEq, reduceCtorEq, false_and,
          and_false, exists_false, false_iff]
        intro he; exact hk b v (by rw [he]; rfl)
      | some a => simp [bind_ok, map_ok, Json.omitNone, Lawful.iff, h ms]
    · rename_i hne
      cases oa with
      | none => simp [map_ok, Json.omitNone, h ((k', v) :: ms)]
      | some a => simp [map_ok, Json.omitNone, Ne.symm hne]

/-- A struct decoder is lawful when its members decoder is, and `encode` is the object of the members. -/
theorem struct_lawful [Serde β] {f : α → β} {m : Members α} {e} (g : β → α) (h : MLawful m e)
    (hfg : ∀ b, f (g b) = b) (hgf : ∀ a, g (f a) = a) (henc : ∀ b, encode b = .obj (e (g b))) :
    ∀ v b, struct f m v = .ok b ↔ encode b = v := by
  intro v b
  rw [henc]
  cases v with
  | obj ms =>
    simp only [struct, map_ok, Value.obj.injEq]
    constructor
    · rintro ⟨a, ha, rfl⟩; rw [hgf]; exact (h ms a).1 ha
    · intro he; exact ⟨g b, (h ms (g b)).2 he, hfg b⟩
  | _ => simp [struct]

/-! Enums: externally tagged variants -/

theorem lookup_mem {l : List (String × α)} {k : String} {a : α} (h : l.lookup k = some a) : (k, a) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    rcases p with ⟨k', a'⟩
    simp only [List.lookup] at h
    split at h
    · rename_i hk; simp at h hk; subst h hk; simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem unitKey_ok {units : List (String × α)} {k : String} {a : α} (h : unitKey units k = .ok a) :
    (k, a) ∈ units := by
  unfold unitKey at h
  split at h
  · cases h; exact lookup_mem ‹_›
  · exact absurd h (fail_ne _ _)

/-- A newtype variant decodes what its constructor's encoding tags. -/
theorem newtype_sound [Serde α] [Decode α] [Lawful α] [Serde β] {C : α → β} {k : String}
    (hC : ∀ x, encode (C x) = Json.tag k (encode x)) : ∀ p b, newtype C p = .ok b → encode b = Json.tag k p := by
  intro p b h
  obtain ⟨x, hx, rfl⟩ := map_ok.1 h
  rw [hC, (Lawful.iff p x).1 hx]

/-- A variant with named fields decodes what its constructor's encoding tags. -/
theorem fields_sound [Serde β] {f : α → β} {m : Members α} {e} {k : String} (h : MLawful m e)
    (hC : ∀ t, encode (f t) = Json.tag k (.obj (e t))) : ∀ p b, struct f m p = .ok b → encode b = Json.tag k p := by
  intro p b hp
  cases p with
  | obj ms =>
    obtain ⟨t, ht, rfl⟩ := map_ok.1 hp
    rw [hC, (h ms t).1 ht]
  | _ => simp [struct] at hp

/-- An enum decoder is lawful when each unit variant's name encodes it, each tagged decoder only returns what its
    tag encodes, and decoding inverts encoding. -/
theorem variants_lawful [Serde α] (units : List (String × α)) (tagged : List (String × (Value → Except String α)))
    (hu : ∀ e ∈ units, encode e.2 = .str e.1)
    (ht : ∀ e ∈ tagged, ∀ p a, e.2 p = .ok a → encode a = Json.tag e.1 p)
    (hrt : ∀ a, variants units tagged (encode a) = .ok a) :
    ∀ v a, variants units tagged v = .ok a ↔ encode a = v := by
  intro v a
  refine ⟨fun h => ?_, fun h => h ▸ hrt a⟩
  match v, h with
  | .str k, h => exact hu _ (unitKey_ok h)
  | .obj [(k, p)], h =>
    simp only [variants] at h
    split at h
    · exact ht _ (lookup_mem ‹_›) p a h
    · exact absurd h (fail_ne _ _)
  | .null, h | .bool _, h | .int _, h | .arr _, h | .obj [], h | .obj (_ :: _ :: _), h =>
    simp [variants] at h

theorem forall_mem_cons' {p : α → Prop} {a : α} {l : List α} (h : p a) (hl : ∀ x ∈ l, p x) :
    ∀ x ∈ a :: l, p x := List.forall_mem_cons.2 ⟨h, hl⟩

theorem forall_mem_nil' {p : α → Prop} : ∀ x ∈ ([] : List α), p x := nofun

/-- An enum key decoder is lawful when each name encodes its variant and decoding inverts encoding. -/
theorem unitKey_lawful [ObjectKey κ] (units : List (String × κ)) (hu : ∀ e ∈ units, ObjectKey.encode e.2 = e.1)
    (hrt : ∀ k, unitKey units (ObjectKey.encode k) = .ok k) :
    ∀ s k, unitKey units s = .ok k ↔ ObjectKey.encode k = s :=
  fun _ _ => ⟨fun h => hu _ (unitKey_ok h), fun h => h ▸ hrt _⟩

/-- `variants` on a tagged value runs the decoder of its tag. -/
theorem variants_tag {units : List (String × α)} {tagged : List (String × (Value → Except String α))}
    {k : String} {d} (h : tagged.lookup k = some d) (p : Value) : variants units tagged (Json.tag k p) = d p := by
  simp [variants, Json.tag, h]

theorem newtype_encode [Serde α] [Decode α] [Lawful α] (C : α → β) (x : α) :
    newtype C (encode x) = .ok (C x) := by
  simp [newtype, decode_encode]; rfl

theorem struct_obj {f : α → β} {m : Members α} {e} (h : MLawful m e) (t : α) :
    struct f m (.obj (e t)) = .ok (f t) := by
  simp [struct, (h _ t).2 rfl]; rfl

end Airbender.Decode
