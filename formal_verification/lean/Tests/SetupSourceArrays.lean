import Airbender.Proofs.FullUnsigned.SetupSourceArrays

namespace Tests.SetupSourceArrays
open Lean Airbender.Setup Airbender.Setup.SourceProofs Airbender.Import.SetupJson
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private def affineBytes : List Char :=
  ([123, 34, 107, 105, 110, 100, 34, 58, 34, 97, 102, 102, 105, 110, 101, 34, 44, 34, 108, 101, 110, 103, 116, 104, 34, 58, 51, 44, 34, 102, 105, 114, 115, 116, 34, 58, 50, 44, 34, 115, 116, 101, 112, 34, 58, 49, 125] : List Nat).map Char.ofNat
private def affineBlock : Block := .affine 3 2 1

/-- One checked source block can occur more than once. -/
theorem affine_source : EagerSource affineBytes (SourceData.blockJson affineBlock) := by
  intro frames result allow
  cases frames with
  | nil => setup_source_rfl
  | cons frame frames =>
    cases frame with
    | array previous => setup_source_rfl
    | object previous key => cases key <;> setup_source_rfl

theorem affine_decoded :
    (fromJson? (SourceData.blockJson affineBlock) : Except String Block) = .ok affineBlock := by
  setup_source_rfl

theorem repeated_array :
    Airbender.Import.SetupJson.parse
      (String.ofList (SourceData.arrayBytes (fun _ : Unit => affineBytes) [(), ()])) =
      .ok (.arr #[SourceData.blockJson affineBlock, SourceData.blockJson affineBlock]) := by
  exact parse_of_eager (eager_array_family (fun _ : Unit => affineBytes)
    (fun _ => SourceData.blockJson affineBlock) (fun _ => affine_source) [(), ()])

theorem repeated_column :
    (fromJson? (Json.mkObj [("blocks", .arr #[SourceData.blockJson affineBlock,
      SourceData.blockJson affineBlock])]) : Except String Column) =
      .ok ⟨#[affineBlock, affineBlock]⟩ := by
  exact decode_blocks_object_family (fun _ : Unit => SourceData.blockJson affineBlock)
    (fun _ => affineBlock) (fun _ => affine_decoded) [(), ()]

theorem repeated_column_source :
    Airbender.Import.SetupJson.parse
      (String.ofList (SourceData.blocksObjectBytes (fun _ : Unit => affineBytes) [(), ()])) =
      .ok (Json.mkObj [("blocks", .arr #[SourceData.blockJson affineBlock,
        SourceData.blockJson affineBlock])]) := by
  exact parse_of_eager (eager_blocks_object_family (fun _ : Unit => affineBytes)
    (fun _ => SourceData.blockJson affineBlock) (fun _ => affine_source) [(), ()])

private def denseBytes : List Char :=
  ([123, 34, 107, 105, 110, 100, 34, 58, 34, 100, 101, 110, 115, 101, 34, 44, 34, 118, 97, 108, 117, 101, 115, 34, 58, 91, 50, 44, 51, 44, 50, 93, 125] : List Nat).map Char.ofNat
private def denseBlock : Block := .dense #[2, 3, 2]

theorem dense_source : EagerSource denseBytes (SourceData.blockJson denseBlock) := by
  intro frames result allow
  cases frames with
  | nil => setup_source_rfl
  | cons frame frames =>
    cases frame with
    | array previous => setup_source_rfl
    | object previous key => cases key <;> setup_source_rfl

theorem dense_decoded :
    (fromJson? (SourceData.blockJson denseBlock) : Except String Block) = .ok denseBlock := by
  setup_source_rfl

private def periodicBytes : List Char :=
  ([123, 34, 107, 105, 110, 100, 34, 58, 34, 112, 101, 114, 105, 111, 100, 105, 99, 34, 44, 34, 114, 101, 112, 101, 116, 105, 116, 105, 111, 110, 115, 34, 58, 50, 44, 34, 115, 116, 114, 105, 100, 101, 34, 58, 45, 49, 44, 34, 118, 97, 108, 117, 101, 115, 34, 58, 91, 50, 44, 51, 93, 125] : List Nat).map Char.ofNat
private def periodicBlock : Block := .periodic 2 (-1) #[2, 3]

theorem periodic_source : EagerSource periodicBytes (SourceData.blockJson periodicBlock) := by
  intro frames result allow
  cases frames with
  | nil => setup_source_rfl
  | cons frame frames =>
    cases frame with
    | array previous => setup_source_rfl
    | object previous key => cases key <;> setup_source_rfl

theorem periodic_decoded :
    (fromJson? (SourceData.blockJson periodicBlock) : Except String Block) = .ok periodicBlock := by
  setup_source_rfl

/-- Missing separators cannot obtain an eager source certificate. -/
theorem missing_comma_rejected : ¬ EagerSource ['[', '{', '}', '{', '}', ']']
    (.arr #[Json.mkObj [], Json.mkObj []]) := by
  intro checked
  have invalid := checked [] none false
  cases invalid

/-- A changed numeric field cannot reuse the old source certificate. -/
theorem changed_value_rejected : ¬ EagerSource affineBytes
    (SourceData.blockJson (.affine 4 2 1)) := by
  intro checked
  have decoded := parse_of_eager checked
  have observed := congrArg
    (fun parsed : Except String Json => parsed >>= fun json => json.getObjValAs? Nat "length") decoded
  change (Except.ok 3 : Except String Nat) = .ok 4 at observed
  cases observed

end Tests.SetupSourceArrays
