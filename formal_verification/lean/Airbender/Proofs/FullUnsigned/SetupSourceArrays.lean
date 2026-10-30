import Airbender.Import.SetupSourceData
import Lean.Elab.Tactic

namespace Airbender.Setup.SourceProofs
open Lean Airbender.Import.SetupJson
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- Full transparency constructs a reflexive proof term. The kernel checks
every generated term. -/
elab "setup_source_rfl" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Meta.withTransparency .all do goal.refl
    Lean.Elab.Tactic.replaceMainGoal []

private def accepted (frames : List Frame) (result : Option Json) (value : Json) : Except String State :=
  match frames with
  | [] => .ok {frames := [], phase := .done, result := some value}
  | .array entries :: frames =>
    .ok {frames := .array (value :: entries) :: frames, phase := .delimiter, result}
  | .object entries (some key) :: frames =>
    .ok {frames := .object ((key, value) :: entries) none :: frames, phase := .delimiter, result}
  | .object _ none :: _ => .error "JSON object has no key"

private def beginning (frames : List Frame) (result : Option Json) (allow : Bool) : State :=
  {frames, phase := .value allow, result}

def EagerSource (bytes : List Char) (value : Json) : Prop :=
  ∀ frames result allow, run (.ok (beginning frames result allow)) bytes = accepted frames result value

private structure Element where
  bytes : List Char
  value : Json
  checked : EagerSource bytes value

private def contents : List Element → List Char
  | [] => []
  | [entry] => entry.bytes
  | entry :: next :: rest => entry.bytes ++ ',' :: contents (next :: rest)

private theorem run_cons (state : Except String State) (c : Char) (rest : List Char) :
    run state (c :: rest) = run (state >>= fun state => step state c) rest := rfl

private theorem close_array_value (earlier : List Json) (frames : List Frame) (result : Option Json) :
    run (.ok (beginning (.array earlier :: frames) result true)) [']'] =
      accepted frames result (.arr earlier.reverse.toArray) := by
  cases frames with
  | nil => rfl
  | cons frame frames =>
    cases frame with
    | array entries => rfl
    | object entries key => cases key <;> rfl

private theorem close_array_delimiter (earlier : List Json) (frames : List Frame) (result : Option Json) :
    run (.ok {frames := .array earlier :: frames, phase := .delimiter, result}) [']'] =
      accepted frames result (.arr earlier.reverse.toArray) := by
  cases frames with
  | nil => rfl
  | cons frame frames =>
    cases frame with
    | array entries => rfl
    | object entries key => cases key <;> rfl

private theorem array_contents (entries : List Element) (earlier : List Json)
    (frames : List Frame) (result : Option Json) (allow : Bool)
    (empty : entries = [] → allow = true) :
    run (.ok (beginning (.array earlier :: frames) result allow)) (contents entries ++ [']']) =
      accepted frames result (.arr ((earlier.reverse ++ entries.map Element.value).toArray)) := by
  induction entries generalizing earlier allow with
  | nil =>
    have h := empty rfl
    subst allow
    simpa only [contents, List.nil_append, List.map_nil, List.append_nil] using
      (close_array_value earlier frames result)
  | cons entry rest ih =>
    cases rest with
    | nil =>
      simp only [contents, List.map_cons, List.map_nil]
      rw [run_append, entry.checked]
      change run (.ok {frames := .array (entry.value :: earlier) :: frames, phase := .delimiter, result}) [']'] = _
      rw [close_array_delimiter, List.reverse_cons]
    | cons next rest =>
      have spelling : contents (entry :: next :: rest) ++ [']'] =
          entry.bytes ++ ',' :: (contents (next :: rest) ++ [']']) := by
        simp only [contents, List.append_assoc, List.cons_append]
      rw [spelling, run_append, entry.checked]
      change run (.ok (beginning (.array (entry.value :: earlier) :: frames) result false))
        (contents (next :: rest) ++ [']']) = _
      simpa only [List.reverse_cons, List.map_cons, List.append_assoc, List.singleton_append]
        using ih (entry.value :: earlier) false (by intro h; cases h)

private theorem eager_array (entries : List Element) :
    EagerSource ('[' :: (contents entries ++ [']'])) (.arr ((entries.map Element.value).toArray)) := by
  intro frames result allow
  change run (.ok (beginning (.array [] :: frames) result true))
    (contents entries ++ [']']) = _
  simpa only [List.reverse_nil, List.nil_append] using
    array_contents entries [] frames result true (by intro _; rfl)


private def arrayBytes (entries : List Element) : List Char := '[' :: (contents entries ++ [']'])

private def blocksObjectBytes (entries : List Element) : List Char :=
  "{\"blocks\":".toList ++ arrayBytes entries ++ ['}']

private theorem eager_blocks_object (entries : List Element) :
    EagerSource (blocksObjectBytes entries)
      (Json.mkObj [("blocks", .arr (entries.map Element.value).toArray)]) := by
  intro frames result allow
  unfold blocksObjectBytes
  rw [List.append_assoc, run_append]
  change run (.ok (beginning (.object [] (some "blocks") :: frames) result false))
    (arrayBytes entries ++ ['}']) = _
  rw [run_append]
  unfold arrayBytes
  rw [eager_array]
  cases frames with
  | nil => rfl
  | cons frame frames =>
    cases frame with
    | array previous => rfl
    | object previous key => cases key <;> rfl

theorem parse_of_eager {bytes : List Char} {value : Json} (checked : EagerSource bytes value) :
    Airbender.Import.SetupJson.parse (String.ofList bytes) = .ok value := by
  apply parse_of_run (checked [] none false)
  rfl


private theorem contents_map {α : Type} (bytes : α → List Char) (value : α → Json)
    (checked : ∀ index, EagerSource (bytes index) (value index)) (entries : List α) :
    contents (entries.map (fun index => Element.mk (bytes index) (value index) (checked index))) =
      SourceData.contents bytes entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simpa only [List.map_cons, contents, SourceData.contents] using
        (congrArg (bytes entry ++ ',' :: ·) ih)

/-- Each distinct element needs one source proof. Repeated elements share it. -/
theorem eager_array_family {α : Type} (bytes : α → List Char) (value : α → Json)
    (checked : ∀ index, EagerSource (bytes index) (value index)) (entries : List α) :
    EagerSource (SourceData.arrayBytes bytes entries) (.arr (entries.map value).toArray) := by
  simpa only [SourceData.arrayBytes, contents_map, List.map_map, Function.comp_def] using
    eager_array (entries.map (fun index => Element.mk (bytes index) (value index) (checked index)))

/-- A column object uses the same element proofs as its block array. -/
theorem eager_blocks_object_family {α : Type} (bytes : α → List Char) (value : α → Json)
    (checked : ∀ index, EagerSource (bytes index) (value index)) (entries : List α) :
    EagerSource (SourceData.blocksObjectBytes bytes entries)
      (Json.mkObj [("blocks", .arr (entries.map value).toArray)]) := by
  simpa only [blocksObjectBytes, SourceData.blocksObjectBytes, arrayBytes,
    SourceData.arrayBytes, contents_map, List.map_map, Function.comp_def] using
    eager_blocks_object (entries.map (fun index => Element.mk (bytes index) (value index) (checked index)))

/-- Array decoding preserves every element and its order. -/
theorem decode_array_family {α β : Type} [FromJson β] (value : α → Json) (decodedValue : α → β)
    (checked : ∀ index, (fromJson? (value index) : Except String β) = .ok (decodedValue index))
    (entries : List α) :
    (fromJson? (.arr (entries.map value).toArray) : Except String (Array β)) =
      .ok (entries.map decodedValue).toArray := by
  change (entries.map value).toArray.mapM fromJson? = _
  rw [List.mapM_toArray]
  have decoded : (entries.map value).mapM fromJson? =
      (.ok (entries.map decodedValue) : Except String (List β)) := by
    induction entries with
    | nil => rfl
    | cons entry rest ih =>
      simp only [List.map_cons, List.mapM_cons, checked, ih]
      rfl
  rw [decoded]
  rfl


/-- A column decoder returns the exact supplied RLE blocks. -/
theorem decode_blocks_object_family {α : Type} (value : α → Json) (block : α → Block)
    (checked : ∀ index, (fromJson? (value index) : Except String Block) = .ok (block index))
    (entries : List α) :
    (fromJson? (Json.mkObj [("blocks", .arr (entries.map value).toArray)]) :
      Except String Column) = .ok ⟨(entries.map block).toArray⟩ := by
  have field : (Json.mkObj [("blocks", .arr (entries.map value).toArray)]).getObjValAs?
      (Array Block) "blocks" = .ok (entries.map block).toArray := by
    change (fromJson? (.arr (entries.map value).toArray) : Except String (Array Block)) = _
    exact decode_array_family value block checked entries
  change instFromJsonColumn.fromJson _ = _
  simp only [instFromJsonColumn.fromJson, field, Except.mapError, bind, Except.bind,
    pure, Except.pure]


/-- Number tokens complete when the next array or object delimiter arrives. -/
def FollowingSource (bytes : List Char) (value : Json) : Prop :=
  ∀ frames result allow ending,
    run (.ok (beginning frames result allow)) (bytes ++ [SourceDelimiter.char ending]) =
      run (acceptedSourceValue frames result value) [SourceDelimiter.char ending]

theorem following_of_eager {bytes : List Char} {value : Json}
    (checked : EagerSource bytes value) : FollowingSource bytes value := by
  intro frames result allow ending
  rw [run_append, checked]
  rfl

/-- Check token spelling, complete consumption and the exact JSON number. -/
def check_number_token (token : SourceData.NumberToken) : Bool :=
  token.tail.all numberCharacter &&
    match numberToken token.bytes with
    | .error _ => false
    | .ok (parsed, rest) => decide (parsed = token.value) && rest.isEmpty

/-- A successful number check proves source parsing in every context. -/
theorem check_number_token_sound (token : SourceData.NumberToken)
    (checked : check_number_token token = true) :
    FollowingSource token.bytes (.num token.value) := by
  unfold check_number_token at checked
  rw [Bool.and_eq_true] at checked
  have valid := List.all_eq_true.mp checked.1
  cases decoded : numberToken token.bytes with
  | error error => simp [decoded] at checked
  | ok parsed =>
    obtain ⟨value, rest⟩ := parsed
    simp only [decoded, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at checked
    obtain ⟨_, same, rfl⟩ := checked
    subst value
    intro frames result allow ending
    exact run_number_token token.head token.tail token.value valid decoded frames result allow ending



private theorem accepted_eq_source (frames : List Frame) (result : Option Json) (value : Json) :
    accepted frames result value = acceptedSourceValue frames result value := by
  cases frames with
  | nil => rfl
  | cons frame frames =>
    cases frame with
    | array previous => rfl
    | object previous key => cases key <;> rfl

private theorem array_following_contents {α : Type} (bytes : α → List Char) (value : α → Json)
    (checked : ∀ index, FollowingSource (bytes index) (value index))
    (entries : List α) (earlier : List Json) (frames : List Frame) (result : Option Json) (allow : Bool)
    (empty : entries = [] → allow = true) :
    run (.ok (beginning (.array earlier :: frames) result allow))
        (SourceData.contents bytes entries ++ [']']) =
      acceptedSourceValue frames result (.arr ((earlier.reverse ++ entries.map value).toArray)) := by
  induction entries generalizing earlier allow with
  | nil =>
    have h := empty rfl
    subst allow
    simpa only [SourceData.contents, List.nil_append, List.map_nil, List.append_nil, accepted_eq_source] using
      close_array_value earlier frames result
  | cons entry rest ih =>
    cases rest with
    | nil =>
      simp only [SourceData.contents, List.map_cons, List.map_nil]
      rw [checked entry (.array earlier :: frames) result allow .array]
      change run (.ok {frames := .array (value entry :: earlier) :: frames, phase := .delimiter, result := result}) [']'] = _
      simpa only [List.reverse_cons, accepted_eq_source] using close_array_delimiter (value entry :: earlier) frames result
    | cons next rest =>
      have spelling : SourceData.contents bytes (entry :: next :: rest) ++ [']'] =
          (bytes entry ++ [',']) ++ (SourceData.contents bytes (next :: rest) ++ [']']) := by
        simp only [SourceData.contents, List.append_assoc, List.cons_append, List.nil_append]
      rw [spelling, run_append, checked entry (.array earlier :: frames) result allow .comma]
      change run (.ok (beginning (.array (value entry :: earlier) :: frames) result false))
        (SourceData.contents bytes (next :: rest) ++ [']']) = _
      simpa only [List.reverse_cons, List.map_cons, List.append_assoc, List.singleton_append] using
        ih (value entry :: earlier) false (by intro h; cases h)

/-- A complete array accepts both eager values and checked number tokens. -/
theorem eager_array_of_following_family {α : Type} (bytes : α → List Char) (value : α → Json)
    (checked : ∀ index, FollowingSource (bytes index) (value index)) (entries : List α) :
    EagerSource (SourceData.arrayBytes bytes entries) (.arr (entries.map value).toArray) := by
  intro frames result allow
  change run (.ok (beginning (.array [] :: frames) result true))
    (SourceData.contents bytes entries ++ [']']) = _
  simpa only [List.reverse_nil, List.nil_append, accepted_eq_source] using
    array_following_contents bytes value checked entries [] frames result true (by intro _; rfl)

/-- A key certificate includes its exact following colon. -/
def KeySource (bytes : List Char) (key : String) : Prop :=
  ∀ earlier frames result allow,
    run (.ok {frames := .object earlier none :: frames, phase := .key allow, result})
      (bytes ++ [':']) =
      .ok (beginning (.object earlier (some key) :: frames) result false)

private theorem close_object_value (earlier : List (String × Json)) (frames : List Frame)
    (result : Option Json) :
    run (.ok {frames := .object earlier none :: frames, phase := .key true, result}) ['}'] =
      acceptedSourceValue frames result (Json.mkObj earlier.reverse) := by
  cases frames with
  | nil => rfl
  | cons frame frames =>
    cases frame with
    | array previous => rfl
    | object previous key => cases key <;> rfl

private theorem close_object_delimiter (earlier : List (String × Json)) (frames : List Frame)
    (result : Option Json) :
    run (.ok {frames := .object earlier none :: frames, phase := .delimiter, result}) ['}'] =
      acceptedSourceValue frames result (Json.mkObj earlier.reverse) := by
  cases frames with
  | nil => rfl
  | cons frame frames =>
    cases frame with
    | array previous => rfl
    | object previous key => cases key <;> rfl

private theorem object_following_contents {α : Type}
    (keyBytes bytes : α → List Char) (key : α → String) (value : α → Json)
    (keyChecked : ∀ index, KeySource (keyBytes index) (key index))
    (checked : ∀ index, FollowingSource (bytes index) (value index))
    (entries : List α) (earlier : List (String × Json)) (frames : List Frame)
    (result : Option Json) (allow : Bool) (empty : entries = [] → allow = true) :
    run (.ok {frames := .object earlier none :: frames, phase := .key allow, result})
        (SourceData.objectContents keyBytes bytes entries ++ ['}']) =
      acceptedSourceValue frames result
        (Json.mkObj (earlier.reverse ++ entries.map (fun entry => (key entry, value entry)))) := by
  induction entries generalizing earlier allow with
  | nil =>
    have h := empty rfl
    subst allow
    simpa only [SourceData.objectContents, List.nil_append, List.map_nil, List.append_nil] using
      close_object_value earlier frames result
  | cons entry rest ih =>
    cases rest with
    | nil =>
      have spelling : SourceData.objectContents keyBytes bytes [entry] ++ ['}'] =
          (keyBytes entry ++ [':']) ++ (bytes entry ++ ['}']) := by
        simp only [SourceData.objectContents, List.append_assoc, List.cons_append, List.nil_append]
      rw [spelling, run_append, keyChecked entry earlier frames result allow,
        checked entry (.object earlier (some (key entry)) :: frames) result false .object]
      change run (.ok {frames := .object ((key entry, value entry) :: earlier) none :: frames, phase := .delimiter, result := result}) ['}'] = _
      simpa only [List.reverse_cons, List.map_cons, List.map_nil] using
        close_object_delimiter ((key entry, value entry) :: earlier) frames result
    | cons next rest =>
      have spelling : SourceData.objectContents keyBytes bytes (entry :: next :: rest) ++ ['}'] =
          (keyBytes entry ++ [':']) ++ ((bytes entry ++ [',']) ++
            (SourceData.objectContents keyBytes bytes (next :: rest) ++ ['}'])) := by
        simp only [SourceData.objectContents, List.append_assoc, List.cons_append, List.nil_append]
      rw [spelling, run_append, keyChecked entry earlier frames result allow, run_append,
        checked entry (.object earlier (some (key entry)) :: frames) result false .comma]
      change run (.ok {frames := .object ((key entry, value entry) :: earlier) none :: frames, phase := .key false, result := result}) (SourceData.objectContents keyBytes bytes (next :: rest) ++ ['}']) = _
      simpa only [List.reverse_cons, List.map_cons, List.append_assoc, List.singleton_append] using
        ih ((key entry, value entry) :: earlier) false (by intro h; cases h)

/-- Object composition preserves source order and the JSON field values. -/
theorem eager_object_family {α : Type}
    (keyBytes bytes : α → List Char) (key : α → String) (value : α → Json)
    (keyChecked : ∀ index, KeySource (keyBytes index) (key index))
    (checked : ∀ index, FollowingSource (bytes index) (value index)) (entries : List α) :
    EagerSource (SourceData.objectBytes keyBytes bytes entries)
      (Json.mkObj (entries.map (fun entry => (key entry, value entry)))) := by
  intro frames result allow
  change run (.ok {frames := .object [] none :: frames, phase := .key true, result})
    (SourceData.objectContents keyBytes bytes entries ++ ['}']) = _
  simpa only [List.reverse_nil, List.nil_append, accepted_eq_source] using
    object_following_contents keyBytes bytes key value keyChecked checked entries [] frames result true
      (by intro _; rfl)

end Airbender.Setup.SourceProofs
