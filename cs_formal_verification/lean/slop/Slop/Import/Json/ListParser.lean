module
public import Human.Import.Exec.JsonParser

@[expose] public section

/-! The list-based JSON parser: recursion is structural (on the input list or on a fuel bound by the input length),
so the kernel can evaluate it. `parse` (Human/Import/Exec/JsonParser.lean) returns what `parseReference` returns
(`parse_eq`, Index.lean); the claims are proved for this one. -/

namespace Airbender.Json.Parser

def skipWs : List UInt8 → List UInt8
  | b :: bs => if isWs b then skipWs bs else b :: bs
  | [] => []

/-- `some rest` iff the input is `p ++ rest`. -/
def dropPrefix? : List UInt8 → List UInt8 → Option (List UInt8)
  | [], l => some l
  | p :: ps, b :: l => if p == b then dropPrefix? ps l else none
  | _ :: _, [] => none

/-- An integer: `-`, if present, then the longest run of digits; accepted iff the bytes read are `toString n`. -/
def int? : List UInt8 → Option (Int × List UInt8)
  | [] => none
  | b :: r =>
    if b == 0x2D then
      let n : Int := -(digitsValue (r.takeWhile isDigit) : Int)
      if utf8 (toString n) == 0x2D :: r.takeWhile isDigit then some (n, r.dropWhile isDigit) else none
    else
      let n : Int := digitsValue ((b :: r).takeWhile isDigit)
      if utf8 (toString n) == (b :: r).takeWhile isDigit then some (n, (b :: r).dropWhile isDigit) else none

/-- One UTF-8 encoded character at the start of the input (the decoded character re-encodes to the bytes read). -/
def rawChar? : List UInt8 → Option (Char × List UInt8)
  | [] => none
  | b :: r =>
    if b < 0x80 then some (Char.ofNat b.toNat, r)
    else
      match ByteArray.utf8DecodeChar? ((b :: r).take 4).toByteArray 0 with
      | some c =>
        if (String.utf8EncodeChar c).isPrefixOf (b :: r) then
          some (c, (b :: r).drop (String.utf8EncodeChar c).length)
        else none
      | none => none

/-- The characters of a string up to its closing quote, appended to `acc`; returns the bytes after the quote. -/
def chars : Nat → String → List UInt8 → Except String (String × List UInt8)
  | 0, _, _ => .error "string too long"
  | _ + 1, _, [] => .error "unterminated string"
  | fuel + 1, acc, b :: r =>
    if b == 0x22 then .ok (acc, r)
    else if b == 0x5C then
      match r with
      | e :: r =>
        if e == 0x75 then
          match r with
          | h₃ :: h₂ :: h₁ :: h₀ :: r =>
            match hexChar? h₃ h₂ h₁ h₀ with
            | some c => chars fuel (acc.push c) r
            | none => .error "invalid \\u escape"
          | _ => .error "invalid \\u escape"
        else
          match unescape? e with
          | some c => chars fuel (acc.push c) r
          | none => .error "invalid escape"
      | [] => .error "unterminated string"
    else
      match rawChar? (b :: r) with
      | some (c, r) =>
        if 0x20 ≤ c.val && c != '"' && c != '\\' then chars fuel (acc.push c) r
        else .error "control character in string"
      | none => .error "invalid UTF-8"

mutual
/-- A value at the start of the input (no leading whitespace); returns the bytes after it. -/
def value : Nat → List UInt8 → Except String (Value × List UInt8)
  | 0, _ => .error "nesting too deep"
  | _ + 1, [] => .error "unexpected end of input"
  | fuel + 1, b :: r =>
    if b == 0x22 then
      match chars fuel "" r with
      | .ok (s, r) => .ok (.str s, r)
      | .error e => .error e
    else if b == 0x5B then
      match skipWs r with
      | c :: r' =>
        if c == 0x5D then .ok (.arr [], r')
        else
          match elements fuel r [] with
          | .ok (vs, r) => .ok (.arr vs, r)
          | .error e => .error e
      | [] => .error "unexpected end of input"
    else if b == 0x7B then
      match skipWs r with
      | c :: r' =>
        if c == 0x7D then .ok (.obj [], r')
        else
          match members fuel r [] with
          | .ok (ms, r) => .ok (.obj ms, r)
          | .error e => .error e
      | [] => .error "unexpected end of input"
    else if b == 0x6E then
      match dropPrefix? nullTail r with
      | some r => .ok (.null, r)
      | none => .error "invalid literal"
    else if b == 0x74 then
      match dropPrefix? trueTail r with
      | some r => .ok (.bool true, r)
      | none => .error "invalid literal"
    else if b == 0x66 then
      match dropPrefix? falseTail r with
      | some r => .ok (.bool false, r)
      | none => .error "invalid literal"
    else
      match int? (b :: r) with
      | some (n, r) => .ok (.int n, r)
      | none => .error "invalid value"
/-- `ws value ws` items separated by commas, up to the closing `]`; `acc` holds the items read, reversed. -/
def elements : Nat → List UInt8 → List Value → Except String (List Value × List UInt8)
  | 0, _, _ => .error "array too long"
  | fuel + 1, l, acc =>
    match value fuel (skipWs l) with
    | .error e => .error e
    | .ok (v, r) =>
      match skipWs r with
      | c :: r =>
        if c == 0x2C then elements fuel r (v :: acc)
        else if c == 0x5D then .ok ((v :: acc).reverse, r)
        else .error "expected ',' or ']'"
      | [] => .error "unexpected end of input"
/-- `ws string ws : ws value ws` members separated by commas, up to the closing `}`; `acc` reversed. -/
def members : Nat → List UInt8 → List (String × Value) → Except String (List (String × Value) × List UInt8)
  | 0, _, _ => .error "object too long"
  | fuel + 1, l, acc =>
    match skipWs l with
    | c :: r =>
      if c == 0x22 then
        match chars fuel "" r with
        | .error e => .error e
        | .ok (k, r) =>
          match skipWs r with
          | c :: r =>
            if c == 0x3A then
              match value fuel (skipWs r) with
              | .error e => .error e
              | .ok (v, r) =>
                match skipWs r with
                | c :: r =>
                  if c == 0x2C then members fuel r ((k, v) :: acc)
                  else if c == 0x7D then .ok (((k, v) :: acc).reverse, r)
                  else .error "expected ',' or '}'"
                | [] => .error "unexpected end of input"
            else .error "expected ':'"
          | [] => .error "unexpected end of input"
      else .error "expected a member name"
    | [] => .error "unexpected end of input"
end

/-- A JSON text: `ws value ws`. -/
def parseList (l : List UInt8) : Except String Value :=
  match value (l.length + 1) (skipWs l) with
  | .ok (v, r) => if (skipWs r).isEmpty then .ok v else .error "trailing bytes after the value"
  | .error e => .error e

/-- What `parse` returns, by the list parser. -/
def parseReference (bytes : ByteArray) : Except String Value :=
  match parseList bytes.data.toList with
  | .ok v => if noDup v then .ok v else .error "duplicate member name"
  | .error e => .error e

end Airbender.Json.Parser
