import Airbender.Proofs.FullUnsigned.SetupSourceArrays

namespace Tests.SetupSourceNumbers
open Lean Airbender.Setup Airbender.Setup.SourceProofs Airbender.Import.SetupJson
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false

private def positive : SourceData.NumberToken := ⟨.one, ['2', '3'], ⟨123, 0⟩⟩
private def negative : SourceData.NumberToken := ⟨.minus, ['4'], ⟨-4, 0⟩⟩

theorem positive_checked : check_number_token positive = true := by decide +kernel

theorem negative_checked : check_number_token negative = true := by decide +kernel

theorem exponent_checked :
    check_number_token ⟨.one, ['e', '+', '2'], ⟨100, 0⟩⟩ = true := by decide +kernel

theorem incomplete_rejected :
    check_number_token ⟨.minus, [], ⟨0, 0⟩⟩ = false := by decide +kernel

theorem trailing_character_rejected :
    check_number_token ⟨.one, ['x'], ⟨1, 0⟩⟩ = false := by decide +kernel

theorem wrong_value_rejected :
    check_number_token ⟨.one, ['2', '3'], ⟨124, 0⟩⟩ = false := by decide +kernel

theorem leading_zero_rejected :
    check_number_token ⟨.zero, ['1'], ⟨1, 0⟩⟩ = false := by decide +kernel

/-- Repeated numbers use the same checked token. -/
theorem number_array_source :
    Airbender.Import.SetupJson.parse
      (String.ofList (SourceData.arrayBytes (fun _ : Unit => positive.bytes) [(), ()])) =
      .ok (.arr #[.num ⟨123, 0⟩, .num ⟨123, 0⟩]) := by
  exact parse_of_eager (eager_array_of_following_family (fun _ : Unit => positive.bytes)
    (fun _ => .num positive.value) (fun _ => check_number_token_sound positive positive_checked) [(), ()])

theorem key_source : KeySource ['"', 'n', '"'] "n" := by
  intro earlier frames result allow
  setup_source_rfl

private def token (index : Bool) : SourceData.NumberToken := if index then negative else positive

/-- Object composition retains duplicate-key order and signed values. -/
theorem number_object_source :
    Airbender.Import.SetupJson.parse
      (String.ofList (SourceData.objectBytes (fun _ : Bool => ['"', 'n', '"'])
        (fun index => (token index).bytes) [false, true])) =
      .ok (Json.mkObj [("n", .num ⟨123, 0⟩), ("n", .num ⟨-4, 0⟩)]) := by
  apply parse_of_eager
  apply eager_object_family (fun _ : Bool => ['"', 'n', '"']) (fun index => (token index).bytes)
    (fun _ => "n") (fun index => .num (token index).value) (fun _ => key_source)
  intro index
  cases index
  · exact check_number_token_sound positive positive_checked
  · exact check_number_token_sound negative negative_checked

end Tests.SetupSourceNumbers
