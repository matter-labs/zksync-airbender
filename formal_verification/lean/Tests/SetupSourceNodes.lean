import Airbender.Proofs.FullUnsigned.SetupSourceArrays

namespace Tests.SetupSourceNodes
open Lean Airbender.Setup Airbender.Setup.SourceProofs Airbender.Import.SetupJson
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false

theorem string_checked : check_string "columns" = true := by decide +kernel
theorem empty_checked : check_string "" = true := by decide +kernel
theorem space_checked : check_string "a b" = true := by decide +kernel
theorem unicode_checked : check_string "λ" = true := by decide +kernel
theorem quote_rejected : check_string "a\"b" = false := by decide +kernel
theorem backslash_rejected : check_string "a\\b" = false := by decide +kernel
theorem control_rejected : check_string "a\nb" = false := by decide +kernel

theorem string_value_source :
    Airbender.Import.SetupJson.parse (String.ofList (SourceData.stringBytes "columns")) =
      .ok (.str "columns") := parse_of_eager (check_string_sound "columns" string_checked).1

theorem empty_value_source :
    Airbender.Import.SetupJson.parse (String.ofList (SourceData.stringBytes "")) =
      .ok (.str "") := parse_of_eager (check_string_sound "" empty_checked).1

theorem string_key_source : KeySource (SourceData.stringBytes "columns") "columns" :=
  (check_string_sound "columns" string_checked).2

theorem null_value_source :
    Airbender.Import.SetupJson.parse (String.ofList SourceData.nullBytes) = .ok .null :=
  parse_of_eager null_source

theorem boolean_values_source (value : Bool) :
    Airbender.Import.SetupJson.parse (String.ofList (SourceData.booleanBytes value)) = .ok (.bool value) :=
  parse_of_eager (boolean_source value)

theorem node_array_source :
    Airbender.Import.SetupJson.parse
      (String.ofList (SourceData.arrayNode SourceData.booleanNode [false, true]).bytes) =
      .ok (.arr #[.bool false, .bool true]) := by
  exact parse_of_eager (eager_array_of_following_family SourceData.booleanBytes Json.bool
    (fun value => boolean_node_source value) [false, true])

private def key (index : Bool) : String := if index then "flag" else "name"
private def child (index : Bool) : SourceData.Node :=
  if index then SourceData.booleanNode true else SourceData.stringNode "columns"

theorem node_object_source :
    Airbender.Import.SetupJson.parse
      (String.ofList (SourceData.objectNode key child [false, true]).bytes) =
      .ok (Json.mkObj [("name", .str "columns"), ("flag", .bool true)]) := by
  have keys : ∀ index, check_string (key index) = true := by
    intro index
    cases index <;> decide +kernel
  have children : ∀ index, NodeSource (child index) := by
    intro index
    cases index
    · exact string_node_source "columns" string_checked
    · exact boolean_node_source true
  exact parse_of_eager (object_node_eager key child keys children [false, true])

end Tests.SetupSourceNodes
