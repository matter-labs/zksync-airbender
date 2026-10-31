import Airbender.Proofs.FullUnsigned.SourceCharacterRenderer
open Airbender.Setup Airbender.Setup.SourceData Airbender.Setup.SourceBank
open Airbender.Setup.SourceCharacters.Renderer
namespace Airbender.Setup.SourceCharacters.Bytes
set_option warningAsError true
set_option Elab.async false
def byteStep (strings numbers : Nat → List Char) (bank : Bank)
    (previous : Nat → List Char → List Char) (index : Nat) (tail : List Char) : List Char :=
  match bank.get index with
  | .null => nullBytes ++ tail
  | .boolean value => booleanBytes value ++ tail
  | .number i => numbers i ++ tail
  | .string i => strings i ++ tail
  | .array entries => '[' :: contentsWith previous entries (']' :: tail)
  | .indexedArray children entries => '[' :: contentsWith (fun i => previous (children i)) entries (']' :: tail)
  | .object entries => '{' :: objectWith (fun entry => strings entry.1)
      (fun entry => previous entry.2) entries ('}' :: tail)

def byteRender (strings numbers : Nat → List Char) (bank : Bank) :
    Nat → Nat → List Char → List Char :=
  Nat.rec (motive := fun _ => Nat → List Char → List Char)
    (fun _ tail => nullBytes ++ tail)
    (fun _ previous => byteStep strings numbers bank previous)

theorem byteRender_eq (strings : Nat → String) (tokens : Nat → NumberToken) (bank : Bank)
    (stringBytes numberBytes : Nat → List Char)
    (stringsChecked : ∀ i, stringBytes i = SourceData.stringBytes (strings i))
    (numbersChecked : ∀ i, numberBytes i = (tokens i).bytes)
    (fuel : Nat) : byteRender stringBytes numberBytes bank fuel = render strings tokens bank fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext index tail
    change byteStep stringBytes numberBytes bank (byteRender stringBytes numberBytes bank fuel) index tail = _
    rw [ih]
    rw [render]
    simp only [byteStep, stringsChecked, numbersChecked]
    rfl

theorem byteRender_bytes (strings : Nat → String) (tokens : Nat → NumberToken) (bank : Bank)
    (stringBytes numberBytes : Nat → List Char)
    (stringsChecked : ∀ i, stringBytes i = SourceData.stringBytes (strings i))
    (numbersChecked : ∀ i, numberBytes i = (tokens i).bytes)
    (fuel index : Nat) :
    (evaluate strings tokens bank fuel index).bytes =
      byteRender stringBytes numberBytes bank fuel index [] := by
  rw [byteRender_eq strings tokens bank stringBytes numberBytes stringsChecked numbersChecked]
  exact render_bytes strings tokens bank fuel index

theorem byteRender_bytes_of_bank_eq (strings : Nat → String) (tokens : Nat → NumberToken)
    (bank candidate : Bank) (stringBytes numberBytes : Nat → List Char)
    (sameBank : candidate = bank)
    (stringsChecked : ∀ i, stringBytes i = SourceData.stringBytes (strings i))
    (numbersChecked : ∀ i, numberBytes i = (tokens i).bytes)
    (fuel index : Nat) :
    (evaluate strings tokens bank fuel index).bytes =
      byteRender stringBytes numberBytes candidate fuel index [] := by
  rw [sameBank]
  exact byteRender_bytes strings tokens bank stringBytes numberBytes stringsChecked numbersChecked fuel index

end Airbender.Setup.SourceCharacters.Bytes
