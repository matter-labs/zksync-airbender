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

end Airbender.Setup.SourceProofs
