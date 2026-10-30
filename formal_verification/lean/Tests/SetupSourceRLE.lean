import Airbender.Proofs.FullUnsigned.SetupSourceRLE

namespace Tests.SetupSourceRLE
open Lean Airbender.Setup Airbender.Setup.SourceBank Airbender.Setup.SourceDecoding Airbender.Setup.SourceProofs
set_option warningAsError true
set_option Elab.async false

private def text (_ : Nat) : String := ""
private def token (index : Nat) : SourceData.NumberToken :=
  if index = 0 then ⟨.six, ['4'], ⟨64, 0⟩⟩ else ⟨.one, ['2', '8'], ⟨128, 0⟩⟩
private def children (index : Nat) : Nat := if index = 0 then 1 else 2
private def values (index : Nat) : Nat := if index = 0 then 64 else 128
private def bank (entries : List Nat) : Bank :=
  .branch 1 (.leaf (.indexedArray children entries))
    (.branch 2 (.leaf (.number 0)) (.leaf (.number 1)))

theorem dictionary_scalar (entries : List Nat) (index : Nat) :
    NaturalAt text token (bank entries) 1 (children index) (values index) := by
  unfold children values
  split <;> constructor <;> setup_source_rfl

theorem dictionary_array (entries : List Nat) :
    NaturalsAt text token (bank entries) 2 0 (entries.map values).toArray :=
  naturals_at text token (bank entries) 1 0 children values entries
    (by setup_source_rfl) (dictionary_scalar entries)

theorem large_dictionary_array :
    NaturalsAt text token (bank ((List.replicate 256 [0, 1, 0, 1]).flatten)) 2 0
      (((List.replicate 256 [0, 1, 0, 1]).flatten).map values).toArray :=
  dictionary_array _

end Tests.SetupSourceRLE
