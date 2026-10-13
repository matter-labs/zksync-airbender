import Lean

/- JSON primitives matching Rust serde, without floating point conversions. -/
namespace Airbender
open Lean

/-- A JSON natural number with a checked upper bound. -/
structure BoundedNat (bound : Nat) where
  val : Nat
  isLt : val < bound
  deriving Repr, DecidableEq

instance : FromJson (BoundedNat bound) where
  fromJson? j := do
    let n ← j.getNat?
    if h : n < bound then return ⟨n, h⟩
    else throw s!"integer {n} must be less than {bound}"

instance : ToJson (BoundedNat bound) where
  toJson n := toJson n.val

abbrev U16 := BoundedNat 65536
abbrev U32 := BoundedNat 4294967296

/-- Rust fixed arrays are JSON arrays, with their lengths checked during decoding. -/
structure Fixed (n : Nat) (α : Type) where
  values : Array α
  size_eq : values.size = n
  deriving Repr

instance [FromJson α] : FromJson (Fixed n α) where
  fromJson? j := do
    let values : Array α ← fromJson? j
    if h : values.size = n then return ⟨values, h⟩
    else throw s!"expected array of length {n}, got {values.size}"

instance [ToJson α] : ToJson (Fixed n α) where
  toJson a := toJson a.values

/-- Rust triples serialize as flat arrays, unlike nested Lean products. -/
structure Triple (α β γ : Type) where
  first : α
  second : β
  third : γ
  deriving Repr

instance [FromJson α] [FromJson β] [FromJson γ] : FromJson (Triple α β γ) where
  fromJson? j := do
    let a ← j.getArr?
    if a.size != 3 then throw "expected a three-element tuple"
    return ⟨← fromJson? a[0]!, ← fromJson? a[1]!, ← fromJson? a[2]!⟩

instance [ToJson α] [ToJson β] [ToJson γ] : ToJson (Triple α β γ) where
  toJson t := .arr #[toJson t.first, toJson t.second, toJson t.third]

class ObjectKey (κ : Type) where
  decode : String → Except String κ
  encode : κ → String

instance : ObjectKey Nat where
  decode s := match s.toNat? with
    | some n => .ok n
    | none => .error "expected a natural-number object key"
  encode := toString

/-- Typed entries of a Rust BTreeMap serialized as a JSON object. -/
structure ObjectMap (κ α : Type) where
  entries : Array (κ × α)
  deriving Repr

instance [ObjectKey κ] [FromJson α] : FromJson (ObjectMap κ α) where
  fromJson? j := do
    let obj ← j.getObj?
    let entries ← obj.toArray.mapM fun (key, value) => do
      return (← ObjectKey.decode key, ← fromJson? value)
    return ⟨entries⟩

instance [ObjectKey κ] [ToJson α] : ToJson (ObjectMap κ α) where
  toJson m := Json.mkObj <| m.entries.toList.map fun (key, value) =>
    (ObjectKey.encode key, toJson value)

inductive JsonNull where
  | null
  deriving Repr

instance : FromJson JsonNull where
  fromJson? j := if j == .null then .ok .null else .error "expected null"

instance : ToJson JsonNull where
  toJson _ := .null

end Airbender
