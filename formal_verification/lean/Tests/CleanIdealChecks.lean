import Airbender.Proofs.GKRProtocol.CleanIdealChecks

namespace Tests.CleanIdealChecks
open Airbender.Compiler Airbender.Compiler.NumericPolynomialChecks
open Airbender.Compiler.CleanIdealChecks
set_option warningAsError true

def placement (_ : Nat) : Fin 1 := ⟨0, by decide⟩
def expression : _root_.Expression (ZMod 7) := .add (.var ⟨0⟩) (.const (-1))
def expressions : LookupTable (_root_.Expression (ZMod 7)) := .leaf [expression]
def relations : List (Polynomial 1 (ZMod 7)) := [[(1, [⟨0, by decide⟩]), (-1, [])]]
def witnesses : LookupTable (Combination relations) := .leaf [[([(1, [])], ⟨0, by decide⟩)]]
def capture : Capture := ⟨.leaf [.add (.atom 0) (.constant 6)],
  .leaf [[(1, [0]), (6, [])]], .leaf [[([(1, [])], 0)]], .leaf [[0]], 1⟩

theorem binding : Bindings placement relations expressions witnesses capture := by
  constructor <;> rfl

theorem checked : check 7 capture = true := by decide +kernel

theorem original_equal :
    Airbender.Compiler.equal (CleanExpression.polynomial placement expression)
      (Airbender.Compiler.combination relations (witnesses.getD 0 [])) = true :=
  check_sound placement relations expressions witnesses capture binding checked 0 (by decide +kernel)

theorem original_scope :
    expressions.toList.all (fun expression => (CleanExpression.inputs expression).all
      (fun wire => decide (wire < capture.scopeLimit))) = true :=
  scope_sound placement relations expressions witnesses capture binding checked

def wrongCode : Capture := {capture with codes := .leaf [.constant 0]}
def wrongCoefficient : Capture := {capture with relations := .leaf [[(1, [0]), (5, [])]]}
def emptyWitness : Capture := {capture with witnesses := .leaf [[]]}
def outsideRelation : Capture := {capture with witnesses := .leaf [[([(1, [])], 1)]]}
def outsideScope : Capture := {capture with inputs := .leaf [[1]]}
def missingWitness : Capture := {capture with witnesses := .leaf []}
def wrongBranchSize : Capture := {capture with codes := .branch 2 capture.codes (.leaf [])}

theorem wrong_code_rejected : check 7 wrongCode = false := by decide +kernel
theorem wrong_coefficient_rejected : check 7 wrongCoefficient = false := by decide +kernel
theorem empty_witness_rejected : check 7 emptyWitness = false := by decide +kernel
theorem outside_relation_rejected : check 7 outsideRelation = false := by decide +kernel
theorem outside_scope_rejected : check 7 outsideScope = false := by decide +kernel
theorem missing_witness_rejected : check 7 missingWitness = false := by decide +kernel
theorem wrong_branch_size_rejected : check 7 wrongBranchSize = false := by decide +kernel

end Tests.CleanIdealChecks
