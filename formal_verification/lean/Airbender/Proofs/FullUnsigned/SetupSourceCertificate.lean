import Lean
import Airbender.Proofs.FullUnsigned.SetupSourceBank
namespace Airbender.Setup.SourceBankCertificate

open Lean Meta Elab Command
open Airbender.Setup Airbender.Setup.SourceProofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
private theorem chooseString (condition : Prop) [Decidable condition]
    {left right : String} (a : check_string left = true) (b : check_string right = true) :
    check_string (if condition then left else right) = true := by
  split <;> assumption

private partial def elements (value : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let value ← whnf value
  if value.isAppOf ``List.nil then return #[]
  unless value.isAppOf ``List.cons do throwError "expected a concrete source metadata list"
  let args := value.getAppArgs
  return #[args[1]!] ++ (← elements args[2]!)

/-- The command proposes ordinary theorem terms. The kernel checks each term. -/
private def addProof (name : Name) (type value : Lean.Expr) : CommandElabM Unit :=
  liftCoreM <| addDecl (.thmDecl { name, levelParams := [], type, value })

private def localName (base : Name) (label : String) : CommandElabM Name := do
  return mkPrivateNameCore (← getMainModule) (base.str label)

private partial def branchProof (body : Lean.Expr) (proved : Std.HashMap Name Name) (chooser : Name) : MetaM Lean.Expr := do
  let body := body.consumeMData
  if !body.isAppOf ``ite && body.getAppFn.isConst then
    let some proof := proved[body.getAppFn.constName!]?
      | throwError "source selector refers to an unproved entry: {body.getAppFn.constName!}"
    return mkConst proof
  unless body.isAppOf ``ite do throwError "source selector is not a constant or a conditional"
  let args := body.getAppArgs
  let left ← branchProof args[3]! proved chooser
  let right ← branchProof args[4]! proved chooser
  mkAppM chooser #[args[1]!, left, right]

private theorem chooseNumber (condition : Prop) [Decidable condition]
    {left right : SourceData.NumberToken}
    (a : check_number_token left = true) (b : check_number_token right = true) :
    check_number_token (if condition then left else right) = true := by
  split <;> assumption

private def libraryProof (selector : Lean.Expr) (proved : Std.HashMap Name Name)
    (checker chooser : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let .defnInfo definition ← getConstInfo selector.constName!
    | throwError "source library must have a definition"
  withLocalDeclD `index (mkConst ``Nat) fun index => do
    let applied := mkApp selector index
    let body := (mkApp definition.value index).headBeta
    let value ← branchProof body proved chooser
    let property ← mkEq (← mkAppM checker #[applied]) (mkConst ``Bool.true)
    return (← mkForallFVars #[index] property, ← mkLambdaFVars #[index] value)

elab "certify_source_bank " base:ident " using " data:ident : command => withEnableInfoTree false do
  let base := base.getId
  let data := data.getId
  let strings ← liftTermElabM <| elements (mkConst (data.str "strings"))
  let tokens ← liftTermElabM <| elements (mkConst (data.str "tokens"))
  let mut stringChecks : Std.HashMap Name Name := {}
  let mut tokenChecks : Std.HashMap Name Name := {}
  for index in [:strings.size] do
    let entry := strings[index]!
    let name ← localName base s!"string_{index}"
    let type ← liftTermElabM do mkEq (← mkAppM ``check_string #[entry]) (mkConst ``Bool.true)
    let proof ← liftTermElabM <| mkEqRefl (mkConst ``Bool.true)
    addProof name type proof
    stringChecks := stringChecks.insert entry.constName! name
  for index in [:tokens.size] do
    let entry := tokens[index]!
    let name ← localName base s!"number_{index}"
    let type ← liftTermElabM do mkEq (← mkAppM ``check_number_token #[entry]) (mkConst ``Bool.true)
    let proof ← liftTermElabM <| mkEqRefl (mkConst ``Bool.true)
    addProof name type proof
    tokenChecks := tokenChecks.insert entry.constName! name
  let text := mkConst (data.str "text")
  let token := mkConst (data.str "token")
  let bank := mkConst (data.str "bank")
  let fuel := mkConst (data.str "fuel")
  let index := mkConst (data.str "rootIndex")
  let entries := mkConst (data.str "rootEntries")
  let stringsName ← localName base "strings_checked"
  let (stringsType, stringsValue) ← liftTermElabM <| libraryProof text stringChecks ``check_string ``chooseString
  addProof stringsName stringsType stringsValue
  let tokensName ← localName base "tokens_checked"
  let (tokensType, tokensValue) ← liftTermElabM <| libraryProof token tokenChecks ``check_number_token ``chooseNumber
  addProof tokensName tokensType tokensValue
  let selectedName ← localName base "root_selected"
  let selectedType ← liftTermElabM do
    mkEq (← mkAppM ``SourceBank.Bank.get #[bank, index]) (mkApp (mkConst ``SourceBank.Description.object) entries)
  let selectedValue ← liftTermElabM <| mkEqRefl (mkApp (mkConst ``SourceBank.Description.object) entries)
  addProof selectedName selectedType selectedValue
  let root := mkConst (data.str "root")
  let eagerType ← liftTermElabM do
    let bytes ← mkAppM ``SourceData.Node.bytes #[root]
    let value ← mkAppM ``SourceData.Node.value #[root]
    mkAppM ``EagerSource #[bytes, value]
  let eagerValue ← liftTermElabM <| mkAppM ``SourceBank.evaluate_object_eager
    #[text, token, bank, mkConst stringsName, mkConst tokensName, fuel, index, entries, mkConst selectedName]
  addProof (base.str "root_eager") eagerType eagerValue
  let parsed ← liftTermElabM <| mkAppM ``parse_of_eager #[mkConst (base.str "root_eager")]
  let type ← liftTermElabM <| inferType parsed
  addProof (base.str "parsed") type parsed
  logInfo m!"checked {strings.size} strings and {tokens.size} number tokens against the source bank"

end Airbender.Setup.SourceBankCertificate
