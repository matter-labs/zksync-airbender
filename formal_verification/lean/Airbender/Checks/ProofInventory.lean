import Lean.Meta.InferType
import Lean.Util.FoldConsts

/-! Environment-based proof discovery shared by the assurance tools. Declaration
names need not match their origin module, and private declarations are included. -/
namespace Airbender.Checks.ProofInventory
open Lean

def origin (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index]!.toString
  | none => ""

/-- Match a module itself and its descendants, independently of declaration names. -/
def within (moduleName rootModule : String) : Bool :=
  moduleName == rootModule || moduleName.startsWith (rootModule ++ ".")

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def isProof (env : Environment) (info : ConstantInfo) : IO Bool := do
  let options := ({} : Options).set `maxHeartbeats (2000000 : Nat) |>.set `maxRecDepth (4096 : Nat)
  let (result, _, _) ← Meta.MetaM.toIO (Meta.isProp info.type)
    { fileName := "<proof-inventory>", fileMap := default, options } { env }
  pure result

def dependencies (info : ConstantInfo) : Array Name :=
  info.getUsedConstantsAsSet.toArray.qsort Name.lt

end Airbender.Checks.ProofInventory
