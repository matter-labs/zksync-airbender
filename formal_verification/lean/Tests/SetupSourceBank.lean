import Airbender.Proofs.FullUnsigned.SetupSourceBank

namespace Tests.SetupSourceBank
open Lean Airbender.Setup Airbender.Setup.SourceProofs Airbender.Setup.SourceBank
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false

private def text (index : Nat) : String := if index = 0 then "columns" else "λ"
private def token (_ : Nat) : SourceData.NumberToken := ⟨.minus, ['7'], ⟨-7, 0⟩⟩
private def bank : Bank :=
  .branch 1 (.leaf (.object [(0, 1), (1, 2)]))
    (.branch 2 (.leaf (.array [3, 4, 5, 6]))
      (.branch 3 (.leaf (.string 1))
        (.branch 4 (.leaf (.number 0))
          (.branch 5 (.leaf (.boolean false))
            (.branch 6 (.leaf .null) (.leaf (.string 0)))))))
private def root : SourceData.Node := evaluate text token bank 4 0

theorem strings_checked : ∀ index, check_string (text index) = true := by
  intro index
  unfold text
  split <;> decide +kernel

theorem numbers_checked : ∀ index, check_number_token (token index) = true := by
  intro index
  unfold token
  decide +kernel

theorem branch_lookup : bank.get 1 = .array [3, 4, 5, 6] := by setup_source_rfl

theorem default_lookup : bank.get 900 = .string 0 := by setup_source_rfl

theorem root_source : EagerSource root.bytes root.value :=
  evaluate_object_eager text token bank strings_checked numbers_checked 3 0
    [(0, 1), (1, 2)] (by setup_source_rfl)

theorem root_value : root.value = Json.mkObj
    [("columns", .arr #[.num ⟨-7, 0⟩, .bool false, .null, .str "columns"]),
     ("λ", .str "λ")] := by setup_source_rfl

theorem root_bytes : String.ofList root.bytes =
    "{\"columns\":[-7,false,null,\"columns\"],\"λ\":\"λ\"}" := by setup_source_rfl

theorem root_parsed : Airbender.Import.SetupJson.parse (String.ofList root.bytes) =
    .ok (Json.mkObj
      [("columns", .arr #[.num ⟨-7, 0⟩, .bool false, .null, .str "columns"]),
       ("λ", .str "λ")]) := by
  simpa only [root_value] using parse_of_eager root_source

theorem zero_depth : evaluate text token bank 0 0 = SourceData.nullNode := rfl

theorem bounded_cycle_source (fuel : Nat) :
    NodeSource (evaluate text token (.leaf (.array [0])) fuel 0) :=
  evaluate_source text token (.leaf (.array [0])) strings_checked numbers_checked fuel 0

theorem wrong_number_rejected :
    check_number_token (⟨.minus, ['7'], ⟨7, 0⟩⟩ : SourceData.NumberToken) = false := by
  decide +kernel

end Tests.SetupSourceBank
