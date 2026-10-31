import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Tests.NumericArithmeticChecks
open Airbender.Compiler
open NumericPolynomialChecks
set_option warningAsError true

def identityArtifact : ArithmeticExtension 1 1 (ZMod 7) :=
  ⟨[atom 0], [.assertZero (.atom 0) (.atom 0)], id, atom⟩

def identityCertificate : Certificate identityArtifact.translation :=
  ⟨fun _ => [(constant 1, ⟨0, by decide⟩)], fun _ => [(constant 1, ⟨0, by decide⟩)]⟩

def identityData : Airbender.Compiler.NumericArithmeticChecks.Capture 1 := {
  sourceRows := .leaf [[(1, [0])]]
  normalizedSourceRows := .leaf [[(1, [0])]]
  lowerRows := .leaf [[(1, [0])]]
  computedRows := .leaf []
  backwardRows := .leaf [[([(1, [])], 0)]]
  forwardRows := .leaf [[([(1, [])], 0)]]
  gateInputs := .leaf [[(1, [0])]]
  gateOutputs := .leaf [[(1, [0])]]
  sortedAddressKeys := [0]
}

numeric_polynomials importedPolynomials from "Tests/fixtures/numeric-arithmetic.json" ["polynomials"]
numeric_combinations importedCombinations from "Tests/fixtures/numeric-arithmetic.json" ["combinations"]
numeric_naturals importedKeys from "Tests/fixtures/numeric-arithmetic.json" ["keys"]
numeric_data_binding polynomials_bound : importedPolynomials = [[(6, [0, 2]), (1, [])], []]
numeric_data_binding combinations_bound : importedCombinations = [[([(1, [])], 3)], []]
numeric_data_binding keys_bound : importedKeys = [0, 2, 15]

theorem identity_checked :
    Airbender.Compiler.NumericArithmeticChecks.check 7 identityData = true := by decide +kernel

theorem identity_binding : Airbender.Compiler.NumericArithmeticChecks.Bindings
    [.BaseLayerWitness 0] identityArtifact identityCertificate identityData := by
  refine ⟨by rfl, by rfl, by rfl, ?_, ?_, ?_, ?_, by rfl, by rfl, by rfl⟩
  · intro wire; rfl
  · intro wire
    change encode (atom (F := ZMod 7) wire) = initial 7 1 _ wire.val
    rw [encode_atom, initial, if_pos wire.isLt]
  · intro index
    have zero : index.val = 0 := by
      have inside := index.isLt
      change index.val < 1 at inside
      omega
    change [(encode (constant (F := ZMod 7) 1), 0)] = identityData.backwardRows.getD index.val []
    rw [zero]
    rfl
  · intro index
    have zero : index.val = 0 := by
      have inside := index.isLt
      change index.val < 1 at inside
      omega
    change [(encode (constant (F := ZMod 7) 1), 0)] = identityData.forwardRows.getD index.val []
    rw [zero]
    rfl

theorem original_check_preserved :
    FullArithmeticChecks.check [.BaseLayerWitness 0] identityArtifact identityCertificate = true :=
  Airbender.Compiler.NumericArithmeticChecks.full_check _ _ _ _ identity_binding identity_checked

theorem noncanonical_unit_fallback :
    fastMultiply 7 [(1, [])] [(8, [0])] = [(1, [0])] := by decide +kernel

theorem mixed_input_computed_substitution :
    fastSubstitute 7 1 (fun _ => [(3, [0])]) [(2, [0, 1])] = [(6, [0, 0])] := by decide +kernel

theorem coefficient_erasure :
    encode ([(9, [0])] : Polynomial 1 (ZMod 7)) = [(2, [0])] := by decide +kernel

theorem changed_variable_rejected :
    NumericPolynomialChecks.equal 7 [(1, [0])] [(1, [1])] = false := by decide +kernel

theorem monomial_permutation :
    NumericPolynomialChecks.equal 7 [(3, [1, 0])] [(3, [0, 1])] = true := by decide +kernel

theorem changed_normalized_source_rejected :
    Airbender.Compiler.NumericArithmeticChecks.check (inputs := 1) 7
      { identityData with normalizedSourceRows := .leaf [[(2, [0])]] } = false := by decide +kernel

theorem forward_noncanonical_fallback :
    Airbender.Compiler.NumericArithmeticChecks.forwardEqual (inputs := 1) 7
      { identityData with sourceRows := .leaf [[(8, [0])]] } [(1, [0])] [([(1, [])], 0)] = true := by decide +kernel

theorem missing_backward_rejected :
    Airbender.Compiler.NumericArithmeticChecks.check (inputs := 1) 7
      { identityData with backwardRows := .leaf [] } = false := by decide +kernel

theorem missing_forward_rejected :
    Airbender.Compiler.NumericArithmeticChecks.check (inputs := 1) 7
      { identityData with forwardRows := .leaf [] } = false := by decide +kernel

theorem changed_gate_rejected :
    Airbender.Compiler.NumericArithmeticChecks.check (inputs := 1) 7
      { identityData with gateOutputs := .leaf [[(1, [])]] } = false := by decide +kernel

theorem duplicate_address_key_rejected :
    Airbender.Compiler.NumericArithmeticChecks.check (inputs := 1) 7
      { identityData with sortedAddressKeys := [0, 0] } = false := by decide +kernel

/-- The rows stay present, but the false cached sizes skip all row loops. -/
def forgedSizes : Airbender.Compiler.NumericArithmeticChecks.Capture 1 := {
  identityData with
  sourceRows := .branch 0 (.leaf [[(1, [0])]]) (.leaf [])
  lowerRows := .branch 0 (.leaf [[(1, [0])]]) (.leaf [])
  gateInputs := .branch 0 (.leaf [[(1, [0])]]) (.leaf [])
  gateOutputs := .branch 0 (.leaf [[(1, [0])]]) (.leaf [])
}

theorem forged_sizes_skip_row_loops :
    Airbender.Compiler.NumericArithmeticChecks.translationCheck 7 forgedSizes &&
      Airbender.Compiler.NumericArithmeticChecks.gateCheck forgedSizes = true := by decide +kernel

theorem forged_sizes_rejected :
    Airbender.Compiler.NumericArithmeticChecks.check 7 forgedSizes = false := by decide +kernel

end Tests.NumericArithmeticChecks
