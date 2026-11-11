-- No need to review: behaviour is fixed by `ParseSoundClaim` and `TextUniqueClaim` (Human/Import/Theorems.lean).
module
public import Human.Import.JsonGrammar

@[expose] public section

/-! A total recursive-descent JSON parser over the input bytes, read by index. Recursion is on a fuel bound by the
input length or well-founded on the bytes left. Whitespace runs are skipped with `ByteArray` comparisons of up to 64
bytes at a time, not byte by byte. The kernel does not evaluate it: `Slop/Import/Json/Index.lean` proves that it
returns what the list-based parser of `Slop/Import/Json/ListParser.lean` (which the kernel can evaluate) returns. -/

namespace Airbender.Json.Parser

def isWs (b : UInt8) : Bool := b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D

def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

def digitsValue (ds : List UInt8) : Nat := ds.foldl (fun n d => 10 * n + (d - 0x30).toNat) 0

/-- The character of a `\uXXXX` escape: below U+10000 and not a surrogate. -/
def hexChar? (a b c d : UInt8) : Option Char :=
  match hexDigit? a, hexDigit? b, hexDigit? c, hexDigit? d with
  | some d₃, some d₂, some d₁, some d₀ =>
    let n := ((d₃ * 16 + d₂) * 16 + d₁) * 16 + d₀
    if h : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x10000) then
      some (Char.ofNatAux n (by unfold Nat.isValidChar; omega))
    else none
  | _, _, _, _ => none

/-- The character of a two-character escape `\e`. -/
def unescape? (e : UInt8) : Option Char := (shortEscapes.find? (·.2 == e)).map (·.1)

def nullTail : List UInt8 := [0x75, 0x6C, 0x6C]
def trueTail : List UInt8 := [0x72, 0x75, 0x65]
def falseTail : List UInt8 := [0x61, 0x6C, 0x73, 0x65]

/-- `k` spaces. -/
def spaces (k : Nat) : ByteArray := (List.replicate k 0x20).toByteArray
def sp64 : ByteArray := spaces 64
def sp32 : ByteArray := spaces 32
def sp16 : ByteArray := spaces 16
def sp8 : ByteArray := spaces 8
def sp4 : ByteArray := spaces 4
def sp2 : ByteArray := spaces 2

/-- `i + k` if the `k` bytes at `i` are `chunk`, else `i`. -/
def stepIf (a : ByteArray) (k : Nat) (chunk : ByteArray) (i : Nat) : Nat :=
  if a.extract i (i + k) == chunk then i + k else i

/-- `i + 1` if the byte at `i` is a space, else `i`. -/
def spaceAt (a : ByteArray) (i : Nat) : Nat :=
  if h : i < a.size then if a[i] == 0x20 then i + 1 else i else i

/-- Index of the first byte at or after `i` that is not a space: runs of 64 spaces, then the rest (fewer than
    64) by halving. -/
def spacesAt (a : ByteArray) (i : Nat) : Nat :=
  if i + 64 ≤ a.size ∧ a.extract i (i + 64) == sp64 then spacesAt a (i + 64)
  else spaceAt a (stepIf a 2 sp2 (stepIf a 4 sp4 (stepIf a 8 sp8 (stepIf a 16 sp16 (stepIf a 32 sp32 i)))))
termination_by a.size - i

/-- Index of the first non-whitespace byte at or after `i`. -/
def skipWsAt (a : ByteArray) (i : Nat) : Nat :=
  if h : i < a.size then
    let b := a[i]
    if isWs b then
      let j := spacesAt a (i + 1)
      if i < j then skipWsAt a j else i
    else i
  else i
termination_by a.size - i

/-- End of the digit run at `i`, and `acc` extended by its digits (as `digitsValue`). -/
def digitsAt (a : ByteArray) (i acc : Nat) : Nat × Nat :=
  if h : i < a.size then
    let b := a[i]
    if isDigit b then digitsAt a (i + 1) (10 * acc + (b - 0x30).toNat) else (i, acc)
  else (i, acc)
termination_by a.size - i

/-- An integer at `i`, as `int?`: accepted iff the bytes read are `toString n`; returns the index after it. -/
def intAt (a : ByteArray) (i : Nat) : Option (Int × Nat) :=
  if h : i < a.size then
    if a[i] == 0x2D then
      let (e, d) := digitsAt a (i + 1) 0
      let n : Int := -(d : Int)
      if (toString n).toUTF8 == a.extract i e then some (n, e) else none
    else
      let (e, d) := digitsAt a i 0
      let n : Int := d
      if (toString n).toUTF8 == a.extract i e then some (n, e) else none
  else none

/-- One UTF-8 encoded character at `i` (the decoded character re-encodes to the bytes read). -/
def rawCharAt (a : ByteArray) (i : Nat) : Option (Char × Nat) :=
  if h : i < a.size then
    let b := a[i]
    if b < 0x80 then some (Char.ofNat b.toNat, i + 1)
    else
      let w := a.extract i (i + 4)
      match w.utf8DecodeChar? 0 with
      | some c =>
        if (String.utf8EncodeChar c).isPrefixOf w.data.toList then some (c, i + (String.utf8EncodeChar c).length)
        else none
      | none => none
  else none

/-- The characters of a string from `i` up to its closing quote, appended to `acc`; returns the index after the
    quote. -/
def charsAt (a : ByteArray) : Nat → String → Nat → Except String (String × Nat)
  | 0, _, _ => .error "string too long"
  | fuel + 1, acc, i =>
    if h : i < a.size then
      let b := a[i]
      if b == 0x22 then .ok (acc, i + 1)
      else if b == 0x5C then
        if h' : i + 1 < a.size then
          let e := a[i + 1]
          if e == 0x75 then
            if h'' : i + 5 < a.size then
              match hexChar? a[i + 2] a[i + 3] a[i + 4] a[i + 5] with
              | some c => charsAt a fuel (acc.push c) (i + 6)
              | none => .error "invalid \\u escape"
            else .error "invalid \\u escape"
          else
            match unescape? e with
            | some c => charsAt a fuel (acc.push c) (i + 2)
            | none => .error "invalid escape"
        else .error "unterminated string"
      else
        match rawCharAt a i with
        | some (c, j) =>
          if 0x20 ≤ c.val && c != '"' && c != '\\' then charsAt a fuel (acc.push c) j
          else .error "control character in string"
        | none => .error "invalid UTF-8"
    else .error "unterminated string"

/-- The literals after their first byte. -/
def nullB : ByteArray := nullTail.toByteArray
def trueB : ByteArray := trueTail.toByteArray
def falseB : ByteArray := falseTail.toByteArray

mutual
/-- A value at `i` (no leading whitespace); returns the index after it. -/
def valueAt (a : ByteArray) : Nat → Nat → Except String (Value × Nat)
  | 0, _ => .error "nesting too deep"
  | fuel + 1, i =>
    if h : i < a.size then
      let b := a[i]
      if b == 0x22 then
        match charsAt a fuel "" (i + 1) with
        | .ok (s, j) => .ok (.str s, j)
        | .error e => .error e
      else if b == 0x5B then
        let j := skipWsAt a (i + 1)
        if h' : j < a.size then
          if a[j] == 0x5D then .ok (.arr [], j + 1)
          else
            match elementsAt a fuel (i + 1) [] with
            | .ok (vs, k) => .ok (.arr vs, k)
            | .error e => .error e
        else .error "unexpected end of input"
      else if b == 0x7B then
        let j := skipWsAt a (i + 1)
        if h' : j < a.size then
          if a[j] == 0x7D then .ok (.obj [], j + 1)
          else
            match membersAt a fuel (i + 1) [] with
            | .ok (ms, k) => .ok (.obj ms, k)
            | .error e => .error e
        else .error "unexpected end of input"
      else if b == 0x6E then
        if a.extract (i + 1) (i + 4) == nullB then .ok (.null, i + 4) else .error "invalid literal"
      else if b == 0x74 then
        if a.extract (i + 1) (i + 4) == trueB then .ok (.bool true, i + 4) else .error "invalid literal"
      else if b == 0x66 then
        if a.extract (i + 1) (i + 5) == falseB then .ok (.bool false, i + 5) else .error "invalid literal"
      else
        match intAt a i with
        | some (n, j) => .ok (.int n, j)
        | none => .error "invalid value"
    else .error "unexpected end of input"
/-- `ws value ws` items separated by commas, up to the closing `]`; `acc` holds the items read, reversed. -/
def elementsAt (a : ByteArray) : Nat → Nat → List Value → Except String (List Value × Nat)
  | 0, _, _ => .error "array too long"
  | fuel + 1, i, acc =>
    match valueAt a fuel (skipWsAt a i) with
    | .error e => .error e
    | .ok (v, j) =>
      let k := skipWsAt a j
      if h : k < a.size then
        let c := a[k]
        if c == 0x2C then elementsAt a fuel (k + 1) (v :: acc)
        else if c == 0x5D then .ok ((v :: acc).reverse, k + 1)
        else .error "expected ',' or ']'"
      else .error "unexpected end of input"
/-- `ws string ws : ws value ws` members separated by commas, up to the closing `}`; `acc` reversed. -/
def membersAt (a : ByteArray) : Nat → Nat → List (String × Value) → Except String (List (String × Value) × Nat)
  | 0, _, _ => .error "object too long"
  | fuel + 1, i, acc =>
    let i := skipWsAt a i
    if h : i < a.size then
      if a[i] == 0x22 then
        match charsAt a fuel "" (i + 1) with
        | .error e => .error e
        | .ok (k, j) =>
          let j := skipWsAt a j
          if h : j < a.size then
            if a[j] == 0x3A then
              match valueAt a fuel (skipWsAt a (j + 1)) with
              | .error e => .error e
              | .ok (v, l) =>
                let l := skipWsAt a l
                if h : l < a.size then
                  let c := a[l]
                  if c == 0x2C then membersAt a fuel (l + 1) ((k, v) :: acc)
                  else if c == 0x7D then .ok (((k, v) :: acc).reverse, l + 1)
                  else .error "expected ',' or '}'"
                else .error "unexpected end of input"
            else .error "expected ':'"
          else .error "unexpected end of input"
      else .error "expected a member name"
    else .error "unexpected end of input"
end

mutual
/-- No object, at any depth, has two members with the same name. -/
def noDup : Value → Bool
  | .arr items => noDupItems items
  | .obj ms => decide (ms.map Prod.fst).Nodup && noDupMembers ms
  | _ => true
def noDupItems : List Value → Bool
  | [] => true
  | v :: vs => noDup v && noDupItems vs
def noDupMembers : List (String × Value) → Bool
  | [] => true
  | m :: ms => noDup m.2 && noDupMembers ms
end

end Parser

/-- The JSON value of the bytes; an error on malformed input or a duplicate member name. -/
def parse (bytes : ByteArray) : Except String Value :=
  match Parser.valueAt bytes (bytes.size + 1) (Parser.skipWsAt bytes 0) with
  | .ok (v, j) =>
    if bytes.size ≤ Parser.skipWsAt bytes j then
      if Parser.noDup v then .ok v else .error "duplicate member name"
    else .error "trailing bytes after the value"
  | .error e => .error e

end Airbender.Json
