import Lean.Data.Json

namespace Airbender.Import.SetupJson
open Lean
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def whitespace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t'

private def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def digits : List Char → Nat → Nat → Nat × Nat × List Char
  | [], value, count => (value, count, [])
  | c :: rest, value, count =>
    if digit c then digits rest (10 * value + (c.toNat - '0'.toNat)) (count + 1)
    else (value, count, c :: rest)

private def digits1 (input : List Char) : Except String (Nat × Nat × List Char) :=
  match input with
  | c :: _ => if digit c then .ok (digits input 0 0) else .error "expected JSON digit"
  | [] => .error "expected JSON digit"

private def unsigned (input : List Char) : Except String (Nat × List Char) := do
  match input with
  | '0' :: rest => pure (0, rest)
  | c :: _ =>
    unless '1' ≤ c && c ≤ '9' do throw "expected JSON number"
    let (value, _, rest) ← digits1 input
    pure (value, rest)
  | [] => throw "expected JSON number"

/-- Keep the supported 64-bit JSON number bound explicit in the kernel. -/
private def number (input : List Char) : Except String (JsonNumber × List Char) := do
  let (sign, input) := match input with
    | '-' :: rest => ((-1 : Int), rest)
    | _ => (1, input)
  let (whole, input) ← unsigned input
  let (value, input) ← match input with
    | '.' :: rest => do
      let (fraction, count, rest) ← digits1 rest
      if count > 18446744073709551616 then throw "too many JSON decimal places"
      pure (JsonNumber.mk (sign * (whole * 10 ^ count + fraction)) count, rest)
    | _ => pure (JsonNumber.mk (sign * whole) 0, input)
  match input with
  | 'e' :: rest | 'E' :: rest =>
    let (negative, rest) := match rest with
      | '-' :: tail => (true, tail)
      | '+' :: tail => (false, tail)
      | _ => (false, rest)
    let (exponent, _, tail) ← digits1 rest
    if negative then pure (value.shiftr exponent, tail)
    else
      if exponent > 18446744073709551616 then throw "JSON exponent too large"
      pure (value.shiftl exponent, tail)
  | _ => pure (value, input)

private def hexDigit (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
  else .error "invalid JSON hex digit"

private def hex4 : List Char → Except String (Nat × List Char)
  | a :: b :: c :: d :: rest => do
    let a ← hexDigit a
    let b ← hexDigit b
    let c ← hexDigit c
    let d ← hexDigit d
    pure (4096 * a + 256 * b + 16 * c + d, rest)
  | _ => .error "incomplete JSON Unicode escape"

private def escaped : List Char → Except String (Char × List Char)
  | '\\' :: rest => .ok ('\\', rest)
  | '"' :: rest => .ok ('"', rest)
  | '/' :: rest => .ok ('/', rest)
  | 'b' :: rest => .ok ('\x08', rest)
  | 'f' :: rest => .ok ('\x0c', rest)
  | 'n' :: rest => .ok ('\n', rest)
  | 'r' :: rest => .ok ('\r', rest)
  | 't' :: rest => .ok ('\t', rest)
  | 'u' :: rest => do
    let (value, rest) ← hex4 rest
    if value < 0xD800 || 0xE000 ≤ value then pure (Char.ofNat value, rest)
    else if value < 0xDC00 then
      match rest with
      | '\\' :: 'u' :: tail =>
        match hex4 tail with
        | .ok (high, tail) =>
          if 0xDC00 ≤ high && high < 0xE000 then
            pure (Char.ofNat (0x10000 + (value - 0xD800) * 1024 + high - 0xDC00), tail)
          else pure ('\ufffd', rest)
        | .error _ => pure ('\ufffd', rest)
      | _ => pure ('\ufffd', rest)
    else pure ('\ufffd', rest)
  | _ => .error "invalid JSON escape"

private def stringCore : Nat → List Char → List Char → Except String (String × List Char)
  | 0, _, _ => .error "JSON string fuel exhausted"
  | fuel + 1, input, acc => do
    match input with
    | '"' :: rest => pure (String.ofList acc.reverse, rest)
    | '\\' :: rest =>
      let (c, rest) ← escaped rest
      stringCore fuel rest (c :: acc)
    | c :: rest =>
      if c.toNat < 0x20 then throw "invalid JSON string character"
      stringCore fuel rest (c :: acc)
    | [] => throw "incomplete JSON string"

inductive Frame where
  | array (entries : List Json)
  | object (entries : List (String × Json)) (key : Option String)

inductive Phase where
  | value (allowEmpty : Bool)
  | key (allowEmpty : Bool)
  | colon
  | delimiter
  | done
  | string (key : Bool) (escaped : Bool) (reversed : List Char)
  | number (reversed : List Char)
  | literal (remaining : List Char) (result : Json)

structure State where
  frames : List Frame := []
  phase : Phase := .value false
  result : Option Json := none

private def acceptValue (state : State) (value : Json) : Except String State := do
  match state.frames with
  | [] => pure { state with phase := .done, result := some value }
  | .array entries :: frames =>
    pure { state with frames := .array (value :: entries) :: frames, phase := .delimiter }
  | .object entries (some key) :: frames =>
    pure { state with frames := .object ((key, value) :: entries) none :: frames, phase := .delimiter }
  | .object _ none :: _ => throw "JSON object has no key"

private def closeArray (state : State) : Except String State := do
  let .array entries :: frames := state.frames | throw "unexpected JSON array end"
  acceptValue { state with frames := frames } (.arr entries.reverse.toArray)

private def closeObject (state : State) : Except String State := do
  let .object entries none :: frames := state.frames | throw "unexpected JSON object end"
  acceptValue { state with frames := frames } (Json.mkObj entries.reverse)

private def acceptKey (state : State) (key : String) : Except String State := do
  let .object entries none :: frames := state.frames | throw "unexpected JSON object key"
  pure { state with frames := .object entries (some key) :: frames, phase := .colon }

private def completeString (state : State) (key : Bool) (reversed : List Char) : Except String State := do
  let (value, rest) ← stringCore (reversed.length + 2) (reversed.reverse ++ ['"']) []
  unless rest.isEmpty do throw "invalid JSON string token"
  if key then acceptKey state value else acceptValue state (.str value)

private def completeNumber (state : State) (reversed : List Char) : Except String State := do
  let (value, rest) ← number reversed.reverse
  unless rest.isEmpty do throw "invalid JSON number token"
  acceptValue state (.num value)

private def structural (state : State) (c : Char) : Except String State := do
  if whitespace c then pure state else
  match state.phase with
  | .value allowEmpty =>
    match c with
    | '[' => pure { state with frames := .array [] :: state.frames, phase := .value true }
    | '{' => pure { state with frames := .object [] none :: state.frames, phase := .key true }
    | ']' => if allowEmpty then closeArray state else throw "expected JSON value"
    | '"' => pure { state with phase := .string false false [] }
    | 't' => pure { state with phase := .literal ['r', 'u', 'e'] (.bool true) }
    | 'f' => pure { state with phase := .literal ['a', 'l', 's', 'e'] (.bool false) }
    | 'n' => pure { state with phase := .literal ['u', 'l', 'l'] .null }
    | _ =>
      if c == '-' || digit c then pure { state with phase := .number [c] }
      else throw "expected JSON value"
  | .key allowEmpty =>
    if c == '"' then pure { state with phase := .string true false [] }
    else if c == '}' && allowEmpty then closeObject state
    else throw "expected JSON object key"
  | .colon =>
    if c == ':' then pure { state with phase := .value false }
    else throw "expected JSON colon"
  | .delimiter =>
    match state.frames, c with
    | .array _ :: _, ']' => closeArray state
    | .object _ _ :: _, '}' => closeObject state
    | .array _ :: _, ',' => pure { state with phase := .value false }
    | .object _ _ :: _, ',' => pure { state with phase := .key false }
    | _, _ => throw "expected JSON delimiter"
  | .done => throw "trailing JSON input"
  | _ => throw "unfinished JSON token"

/-- Consume exactly one character. Token state can cross source blocks. -/
def step (state : State) (c : Char) : Except String State := do
  match state.phase with
  | .string key escaped reversed =>
    if escaped then pure { state with phase := .string key false (c :: reversed) }
    else if c == '\\' then pure { state with phase := .string key true (c :: reversed) }
    else if c == '"' then completeString state key reversed
    else if c.toNat < 0x20 then throw "invalid JSON string character"
    else pure { state with phase := .string key false (c :: reversed) }
  | .number reversed =>
    if digit c || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E' then
      pure { state with phase := .number (c :: reversed) }
    else structural (← completeNumber state reversed) c
  | .literal remaining value =>
    match remaining with
    | [] => throw "invalid JSON literal state"
    | expected :: tail =>
      unless c == expected do throw "invalid JSON literal"
      if tail.isEmpty then acceptValue state value
      else pure { state with phase := .literal tail value }
  | _ => structural state c

/-- Run one source block. An error remains an error in all later blocks. -/
def run (state : Except String State) (input : List Char) : Except String State :=
  input.foldl (fun state c => state >>= fun state => step state c) state

/-- Source blocks compose without a change to parser state or token spelling. -/
theorem run_append (state : Except String State) (first second : List Char) :
    run state (first ++ second) = run (run state first) second := by
  exact List.foldl_append

def finish (state : State) : Except String Json := do
  let state ← match state.phase with
    | .number reversed => completeNumber state reversed
    | _ => pure state
  match state.phase, state.frames, state.result with
  | .done, [], some value => pure value
  | _, _, _ => throw "incomplete JSON input"

def parseChars (input : List Char) : Except String Json := do
  let state ← run (.ok {}) input
  finish state

def parse (source : String) : Except String Json := parseChars source.toList

theorem parse_ofList (input : List Char) : parse (String.ofList input) = parseChars input := by
  simp [parse]

/-- A checked block run and checked final state imply the exact decoded JSON. -/
theorem parse_of_run {input : List Char} {state : State} {json : Json}
    (checked : run (.ok {}) input = .ok state) (finished : finish state = .ok json) :
    parse (String.ofList input) = .ok json := by
  rw [parse_ofList]
  unfold parseChars
  rw [checked]
  exact finished

/-- A JSON number starts with one of these eleven characters. -/
inductive NumberHead where
  | minus | zero | one | two | three | four | five | six | seven | eight | nine

def NumberHead.char : NumberHead → Char
  | .minus => '-' | .zero => '0' | .one => '1' | .two => '2' | .three => '3'
  | .four => '4' | .five => '5' | .six => '6' | .seven => '7' | .eight => '8' | .nine => '9'

/-- The delimiters used by array and object source composition. -/
inductive SourceDelimiter where
  | comma | array | object

abbrev SourceDelimiter.char : SourceDelimiter → Char
  | .comma => ',' | .array => ']' | .object => '}'

def numberCharacter (c : Char) : Bool :=
  digit c || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

/-- Use the same number decoder as the incremental parser. -/
def numberToken (input : List Char) : Except String (JsonNumber × List Char) := number input

def acceptedSourceValue (frames : List Frame) (result : Option Json) (value : Json) : Except String State :=
  match frames with
  | [] => .ok {frames := [], phase := .done, result := some value}
  | .array entries :: frames =>
    .ok {frames := .array (value :: entries) :: frames, phase := .delimiter, result}
  | .object entries (some key) :: frames =>
    .ok {frames := .object ((key, value) :: entries) none :: frames, phase := .delimiter, result}
  | .object _ none :: _ => .error "JSON object has no key"

private theorem numeric_step (frames : List Frame) (result : Option Json) (earlier : List Char)
    (c : Char) (valid : numberCharacter c = true) :
    step {frames, phase := .number earlier, result} c =
      .ok {frames, phase := .number (c :: earlier), result} := by
  change (if numberCharacter c then _ else _) = _
  rw [valid]
  rfl

private theorem numeric_first_step (head : NumberHead) (frames : List Frame)
    (result : Option Json) (allow : Bool) :
    step {frames, phase := .value allow, result} head.char =
      .ok {frames, phase := .number [head.char], result} := by
  cases head <;> rfl

private theorem run_cons_numeric (state : Except String State) (c : Char) (rest : List Char) :
    run state (c :: rest) = run (state >>= fun state => step state c) rest := rfl

private theorem numeric_tail (chars : List Char) (valid : ∀ c ∈ chars, numberCharacter c = true)
    (frames : List Frame) (result : Option Json) (earlier : List Char) :
    run (.ok {frames, phase := .number earlier, result}) chars =
      .ok {frames, phase := .number (chars.reverse ++ earlier), result} := by
  induction chars generalizing earlier with
  | nil => rfl
  | cons c rest ih =>
    rw [run_cons_numeric]
    change run (step {frames, phase := .number earlier, result} c) rest = _
    rw [numeric_step frames result earlier c (valid c (by simp))]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (fun x member => valid x (by simp only [List.mem_cons]; exact Or.inr member)) (c :: earlier)

private theorem numeric_complete (chars : List Char) (value : JsonNumber)
    (decoded : numberToken chars = .ok (value, [])) (frames : List Frame) (result : Option Json) :
    completeNumber {frames, phase := .number chars.reverse, result} chars.reverse =
      acceptedSourceValue frames result (.num value) := by
  change number chars = .ok (value, []) at decoded
  unfold completeNumber
  rw [List.reverse_reverse, decoded]
  cases frames with
  | nil => rfl
  | cons frame frames =>
    cases frame with
    | array previous => rfl
    | object previous key => cases key <;> rfl

private theorem numeric_end_step (chars : List Char) (value : JsonNumber)
    (decoded : numberToken chars = .ok (value, [])) (frames : List Frame)
    (result : Option Json) (ending : SourceDelimiter) :
    run (.ok {frames, phase := .number chars.reverse, result}) [ending.char] =
      run (acceptedSourceValue frames result (.num value)) [ending.char] := by
  have invalid : numberCharacter ending.char = false := by cases ending <;> rfl
  change (if numberCharacter ending.char then _ else _) = _
  rw [invalid]
  change (do let state ← completeNumber {frames, phase := .number chars.reverse, result} chars.reverse
             structural state ending.char) = _
  rw [numeric_complete chars value decoded frames result]
  cases frames with
  | nil => rfl
  | cons frame frames =>
    cases frame with
    | array previous => rfl
    | object previous key => cases key <;> rfl

/-- A checked token has the same value in every parser context. -/
theorem run_number_token (head : NumberHead) (tail : List Char) (value : JsonNumber)
    (valid : ∀ c ∈ tail, numberCharacter c = true)
    (decoded : numberToken (head.char :: tail) = .ok (value, []))
    (frames : List Frame) (result : Option Json) (allow : Bool) (ending : SourceDelimiter) :
    run (.ok {frames, phase := .value allow, result}) ((head.char :: tail) ++ [ending.char]) =
      run (acceptedSourceValue frames result (.num value)) [ending.char] := by
  rw [List.cons_append, run_cons_numeric]
  change run (step {frames, phase := .value allow, result} head.char) (tail ++ [ending.char]) = _
  rw [numeric_first_step, run_append, numeric_tail tail valid]
  simpa only [List.reverse_cons] using
    numeric_end_step (head.char :: tail) value decoded frames result ending

/-- Check a string character that needs no JSON escape. -/
def unescapedCharacter (c : Char) : Bool :=
  c != '\\' && c != '"' && decide (0x20 ≤ c.toNat)

private theorem unescaped_step (frames : List Frame) (result : Option Json) (key : Bool)
    (earlier : List Char) (c : Char) (valid : unescapedCharacter c = true) :
    step {frames, phase := .string key false earlier, result} c =
      .ok {frames, phase := .string key false (c :: earlier), result} := by
  simp only [unescapedCharacter, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at valid
  obtain ⟨⟨noSlash, noQuote⟩, lower⟩ := valid
  simp [step, noSlash, noQuote, Nat.not_lt.mpr lower, pure, Except.pure]

private theorem unescaped_tail (chars : List Char) (valid : ∀ c ∈ chars, unescapedCharacter c = true)
    (frames : List Frame) (result : Option Json) (key : Bool) (earlier : List Char) :
    run (.ok {frames, phase := .string key false earlier, result}) chars =
      .ok {frames, phase := .string key false (chars.reverse ++ earlier), result} := by
  induction chars generalizing earlier with
  | nil => rfl
  | cons c rest ih =>
    rw [run_cons_numeric]
    change run (step {frames, phase := .string key false earlier, result} c) rest = _
    rw [unescaped_step frames result key earlier c (valid c (by simp))]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (fun x member => valid x (by simp only [List.mem_cons]; exact Or.inr member)) (c :: earlier)

private theorem stringCore_unescaped (chars : List Char)
    (valid : ∀ c ∈ chars, unescapedCharacter c = true) (earlier : List Char) (extra : Nat) :
    stringCore (chars.length + extra + 1) (chars ++ ['"']) earlier =
      .ok (String.ofList (earlier.reverse ++ chars), []) := by
  induction chars generalizing earlier with
  | nil =>
    simp only [List.nil_append, stringCore, List.append_nil, pure, Except.pure]
  | cons c rest ih =>
    have safe := valid c (by simp)
    simp only [unescapedCharacter, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at safe
    obtain ⟨⟨noSlash, noQuote⟩, lower⟩ := safe
    have recurrence : stringCore (rest.length + extra + 1 + 1) (c :: (rest ++ ['"'])) earlier =
        stringCore (rest.length + extra + 1) (rest ++ ['"']) (c :: earlier) := by
      rw [stringCore]
      · simp only [Nat.not_lt.mpr lower, ↓reduceIte, pure, Except.pure, bind, Except.bind]
      · exact noQuote
      · exact noSlash
    simpa only [List.length_cons, Nat.succ_add, List.cons_append,
      List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using
      recurrence.trans (ih (fun x member => valid x (by simp only [List.mem_cons]; exact Or.inr member))
        (c :: earlier))


private theorem completeString_unescaped (chars : List Char)
    (valid : ∀ c ∈ chars, unescapedCharacter c = true) (state : State) (key : Bool) :
    completeString state key chars.reverse =
      if key then acceptKey state (String.ofList chars) else acceptValue state (.str (String.ofList chars)) := by
  have parsed := stringCore_unescaped chars valid [] 1
  simp only [List.reverse_nil, List.nil_append] at parsed
  unfold completeString
  rw [List.length_reverse, List.reverse_reverse, parsed]
  rfl

/-- Safe string characters retain their exact value in every context. -/
theorem run_unescaped_string (chars : List Char)
    (valid : ∀ c ∈ chars, unescapedCharacter c = true)
    (frames : List Frame) (result : Option Json) (allow : Bool) :
    run (.ok {frames, phase := .value allow, result}) ('"' :: (chars ++ ['"'])) =
      acceptedSourceValue frames result (.str (String.ofList chars)) := by
  rw [run_cons_numeric]
  change run (.ok {frames, phase := .string false false [], result}) (chars ++ ['"']) = _
  rw [run_append, unescaped_tail chars valid]
  simp only [List.append_nil]
  change completeString {frames, phase := .string false false chars.reverse, result} false chars.reverse = _
  rw [completeString_unescaped chars valid]
  cases frames with
  | nil => rfl
  | cons frame frames =>
    cases frame with
    | array previous => rfl
    | object previous key => cases key <;> rfl

/-- Safe key characters retain their value and consume the following colon. -/
theorem run_unescaped_key (chars : List Char)
    (valid : ∀ c ∈ chars, unescapedCharacter c = true)
    (earlier : List (String × Json)) (frames : List Frame) (result : Option Json) (allow : Bool) :
    run (.ok {frames := .object earlier none :: frames, phase := .key allow, result})
      (('"' :: (chars ++ ['"'])) ++ [':']) =
      .ok {frames := .object earlier (some (String.ofList chars)) :: frames, phase := .value false, result} := by
  have quoted : run (.ok {frames := .object earlier none :: frames, phase := .key allow, result})
        ('"' :: (chars ++ ['"'])) =
        .ok {frames := .object earlier (some (String.ofList chars)) :: frames, phase := .colon, result} := by
    rw [run_cons_numeric]
    change run (.ok {frames := .object earlier none :: frames, phase := .string true false [], result})
      (chars ++ ['"']) = _
    rw [run_append, unescaped_tail chars valid]
    simp only [List.append_nil]
    change completeString {frames := .object earlier none :: frames, phase := .string true false chars.reverse, result} true chars.reverse = _
    rw [completeString_unescaped chars valid]
    rfl
  rw [run_append, quoted]
  rfl

end Airbender.Import.SetupJson
