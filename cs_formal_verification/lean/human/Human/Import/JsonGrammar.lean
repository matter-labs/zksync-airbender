module

@[expose] public section
/-! # JSON texts (RFC 8259), at the level of bytes

The grammar the artifact parser is checked against (`Human/Import/Theorems.lean`). It is RFC 8259 with two
deviations, both marked where they apply:
* numbers are integers written as `toString n` (no `-0`, leading zeros, fraction or exponent);
* `\u` escapes only for characters below U+10000 (no surrogate pairs). -/

namespace Airbender.Json

/-- A JSON value (RFC 8259). Numbers are integers: the artifacts have no fractions or exponents. -/
inductive Value where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | arr (items : List Value)
  | obj (members : List (String × Value))

/-- No object, at any depth, has two members with the same name. -/
inductive NoDuplicateKeys : Value → Prop
  | null : NoDuplicateKeys .null
  | bool : NoDuplicateKeys (.bool b)
  | int : NoDuplicateKeys (.int n)
  | str : NoDuplicateKeys (.str s)
  | arr : (∀ v ∈ items, NoDuplicateKeys v) → NoDuplicateKeys (.arr items)
  | obj : (members.map Prod.fst).Nodup → (∀ m ∈ members, NoDuplicateKeys m.2) → NoDuplicateKeys (.obj members)

/-- The UTF-8 bytes of a string. -/
abbrev utf8 (s : String) : List UInt8 := s.toUTF8.toList

/-- RFC 8259 §2: insignificant whitespace. -/
def Ws (bs : List UInt8) : Prop := ∀ b ∈ bs, b = 0x20 ∨ b = 0x09 ∨ b = 0x0A ∨ b = 0x0D

/-- §7: the two-character escapes `\" \\ \/ \b \f \n \r \t`, as (character, byte after `\`). -/
def shortEscapes : List (Char × UInt8) :=
  [('"', 0x22), ('\\', 0x5C), ('/', 0x2F), ('\x08', 0x62), ('\x0C', 0x66), ('\n', 0x6E), ('\r', 0x72), ('\t', 0x74)]

/-- The value of an ASCII hex digit (either case). -/
def hexDigit? (b : UInt8) : Option Nat :=
  if 0x30 ≤ b ∧ b ≤ 0x39 then some (b - 0x30).toNat
  else if 0x61 ≤ b ∧ b ≤ 0x66 then some ((b - 0x61).toNat + 10)
  else if 0x41 ≤ b ∧ b ≤ 0x46 then some ((b - 0x41).toNat + 10)
  else none

/-- §7: one character of a string. Unescaped: U+0020 and above except `"` and `\`, in UTF-8.
    Deviation: `\u` escapes only for characters below U+10000 (no surrogate pairs). -/
inductive CharText : Char → List UInt8 → Prop
  | raw : 0x20 ≤ c.val → c ≠ '"' → c ≠ '\\' → CharText c (utf8 c.toString)
  | short : (c, e) ∈ shortEscapes → CharText c [0x5C, e]
  | unicode : c.val < 0x10000 → ds.map hexDigit? = [some d₃, some d₂, some d₁, some d₀] →
      c.val.toNat = ((d₃ * 16 + d₂) * 16 + d₁) * 16 + d₀ → CharText c (0x5C :: 0x75 :: ds)

/-- §7: the characters of a string, one encoding each. -/
inductive CharsText : List Char → List UInt8 → Prop
  | nil : CharsText [] []
  | cons : CharText c bs → CharsText cs rest → CharsText (c :: cs) (bs ++ rest)

mutual
/-- §3–§7: a value. Deviation: numbers are integers written as `toString n` (no `-0`, fraction or exponent). -/
inductive ValueText : Value → List UInt8 → Prop
  | null : ValueText .null (utf8 "null")
  | true : ValueText (.bool true) (utf8 "true")
  | false : ValueText (.bool false) (utf8 "false")
  | int : ValueText (.int n) (utf8 (toString n))
  | str : CharsText s.toList bs → ValueText (.str s) (0x22 :: bs ++ [0x22])
  | emptyArr : Ws w → ValueText (.arr []) (0x5B :: w ++ [0x5D])
  | arr : ElementsText items bs → ValueText (.arr items) (0x5B :: bs ++ [0x5D])
  | emptyObj : Ws w → ValueText (.obj []) (0x7B :: w ++ [0x7D])
  | obj : MembersText members bs → ValueText (.obj members) (0x7B :: bs ++ [0x7D])
/-- §5: one or more `ws value ws`, separated by commas. -/
inductive ElementsText : List Value → List UInt8 → Prop
  | one : Ws w₁ → ValueText v bs → Ws w₂ → ElementsText [v] (w₁ ++ bs ++ w₂)
  | cons : Ws w₁ → ValueText v bs → Ws w₂ → ElementsText vs rest →
      ElementsText (v :: vs) (w₁ ++ bs ++ w₂ ++ 0x2C :: rest)
/-- §4: one or more `ws string ws : ws value ws`, separated by commas. -/
inductive MembersText : List (String × Value) → List UInt8 → Prop
  | one : Ws w₁ → ValueText (.str k) ks → Ws w₂ → Ws w₃ → ValueText v bs → Ws w₄ →
      MembersText [(k, v)] (w₁ ++ ks ++ w₂ ++ 0x3A :: w₃ ++ bs ++ w₄)
  | cons : Ws w₁ → ValueText (.str k) ks → Ws w₂ → Ws w₃ → ValueText v bs → Ws w₄ → MembersText ms rest →
      MembersText ((k, v) :: ms) (w₁ ++ ks ++ w₂ ++ 0x3A :: w₃ ++ bs ++ w₄ ++ 0x2C :: rest)
end

/-- §2: a JSON text is `ws value ws`. -/
def Text (bytes : List UInt8) (v : Value) : Prop :=
  ∃ w₁ bs w₂, Ws w₁ ∧ ValueText v bs ∧ Ws w₂ ∧ bytes = w₁ ++ bs ++ w₂

end Airbender.Json
