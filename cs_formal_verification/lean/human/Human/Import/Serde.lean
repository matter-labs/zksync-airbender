module
public import Human.Import.BabyBear
public import Human.Import.JsonGrammar

@[expose] public section

/-! # The JSON value serde_json writes

`Serde.encode a` is the JSON value Rust's serde_json writes for `a`: integers as numbers, `None` as `null`,
sequences and tuples as arrays, a struct as the object of its fields in declaration order, an enum variant
externally tagged (`"Name"`, `{"Name": payload}`, or `{"Name": {fields…}}`). The instances of the schema types are
next to them in `Schema.lean`. The decoder (`Exec/Decode.lean`) is fixed by `DecodeClaim` (`Theorems.lean`): it
returns `c` from a value exactly when the value is `encode c`. -/

namespace Airbender

class Serde (α : Type) where
  encode : α → Json.Value

open Serde (encode)

/-- An externally tagged enum variant with a payload: `{"name": payload}`. -/
def Json.tag (name : String) (payload : Value) : Value := .obj [(name, payload)]

/-- A struct field that serde omits when it is `None` (`skip_serializing_if = "Option::is_none"`). -/
def Json.omitNone [Serde α] (name : String) : Option α → List (String × Value)
  | none => []
  | some a => [(name, encode a)]

instance : Serde Nat := ⟨fun n => .int n⟩
instance : Serde Bool := ⟨.bool⟩
instance : Serde String := ⟨.str⟩
instance [Serde α] : Serde (Option α) := ⟨fun | none => .null | some a => encode a⟩
instance [Serde α] : Serde (List α) := ⟨fun l => .arr (l.map encode)⟩
instance [Serde α] : Serde (Array α) := ⟨fun a => .arr (a.toList.map encode)⟩
instance [Serde α] [Serde β] : Serde (α × β) := ⟨fun (a, b) => .arr [encode a, encode b]⟩

instance : Serde (BoundedNat bound) := ⟨fun n => encode n.val⟩
instance [Serde α] : Serde (Fixed n α) := ⟨fun a => encode a.values⟩
instance [Serde α] [Serde β] [Serde γ] : Serde (Triple α β γ) :=
  ⟨fun t => .arr [encode t.first, encode t.second, encode t.third]⟩
instance : Serde JsonNull := ⟨fun _ => .null⟩
/-- The Montgomery residue, as stored. -/
instance : Serde Coefficient := ⟨fun c => encode c.raw⟩

/-- A map key as a JSON member name: a number as its decimal digits, an enum variant as its name. -/
class ObjectKey (κ : Type) where
  encode : κ → String

instance : ObjectKey Nat := ⟨toString⟩
instance [ObjectKey κ] [Serde α] : Serde (ObjectMap κ α) :=
  ⟨fun m => .obj (m.entries.toList.map fun (k, a) => (ObjectKey.encode k, encode a))⟩

end Airbender
