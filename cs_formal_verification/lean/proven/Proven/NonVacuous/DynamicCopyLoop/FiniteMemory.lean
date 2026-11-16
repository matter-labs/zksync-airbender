module
public import Proven.NonVacuous.DynamicCopyLoop.Model
public import Mathlib.Data.List.FinRange

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 8192

/-- The finite architectural permutation has 132 tokens on each side. -/
theorem memory_token_counts :
    (finiteTrace.initialMemory ++ steps.map Prod.snd).length = 132 ∧
    (finiteTrace.terminalMemory ++ steps.map Prod.fst).length = 132 := by
  decide +kernel

def matchingIndices : Vector (Fin 132) 132 :=
  #v[48, 90, 59, 3, 4, 50, 6, 7, 8, 9, 53, 56, 68, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    95, 96, 97, 98, 99, 100, 101, 102, 62, 105, 106, 107, 108, 109, 110, 111,
    49, 51, 71, 52, 55, 54, 94, 57, 60, 58, 63, 61, 103, 2, 104, 64,
    65, 66, 67, 69, 112, 70, 72, 73, 75, 74, 82, 76, 77, 78, 80, 131,
    81, 83, 84, 86, 85, 5, 87, 88, 89, 92, 91, 1, 93, 0, 113, 114,
    115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130,
    79, 10, 32, 33, 34, 35, 36, 37, 38, 39, 11, 40, 41, 42, 43, 44,
    45, 46, 47, 12]
def inverseMatchingIndices : Vector (Fin 132) 132 :=
  #v[93, 91, 61, 3, 4, 85, 6, 7, 8, 9, 113, 122, 131, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 128, 129, 130,
    0, 48, 5, 49, 51, 10, 53, 52, 11, 55, 57, 2, 56, 59, 40, 58,
    63, 64, 65, 66, 12, 67, 69, 50, 70, 71, 73, 72, 75, 76, 77, 112,
    78, 80, 74, 81, 82, 84, 83, 86, 87, 88, 1, 90, 89, 92, 54, 32,
    33, 34, 35, 36, 37, 38, 39, 60, 62, 41, 42, 43, 44, 45, 46, 47,
    68, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,
    109, 110, 111, 79]

def matchingPermutation : Equiv.Perm (Fin 132) where
  toFun index := matchingIndices[index]
  invFun index := inverseMatchingIndices[index]
  left_inv := by intro index; fin_cases index <;> decide +kernel
  right_inv := by intro index; fin_cases index <;> decide +kernel

theorem ofFn_get_length {α : Type} (values : List α) {length : Nat}
    (size : values.length = length) :
    List.ofFn (fun index : Fin length => values[index.val]'(by omega)) = values := by
  subst length
  exact List.ofFn_getElem


/-- Public seeds followed by every actual CPU and worker write token. -/
noncomputable def leftTokens := finiteTrace.initialMemory ++ steps.map Prod.snd

/-- Terminal tokens followed by every actual CPU and worker read token. -/
noncomputable def rightTokens := finiteTrace.terminalMemory ++ steps.map Prod.fst

noncomputable def leftToken (index : Fin 132) : MemoryToken babyBearModulus :=
  leftTokens[index.val]'(by have length := memory_token_counts.1; change leftTokens.length = 132 at length; omega)

noncomputable def rightToken (index : Fin 132) : MemoryToken babyBearModulus :=
  rightTokens[index.val]'(by have length := memory_token_counts.2; change rightTokens.length = 132 at length; omega)

/-- The explicit finite permutation matches addresses, both timestamp limbs and complete value codes. -/
theorem matching_tokens (index : Fin 132) :
    leftToken index = rightToken (matchingPermutation index) := by
  fin_cases index <;> decide +kernel

/-- The complete finite CPU and worker memory lists match with every occurrence retained. -/
theorem finite_memory_matching :
    (finiteTrace.initialMemory ++ steps.map Prod.snd).Perm
      (finiteTrace.terminalMemory ++ steps.map Prod.fst) := by
  have left : List.ofFn leftToken = leftTokens := ofFn_get_length _ memory_token_counts.1
  have right : List.ofFn rightToken = rightTokens := ofFn_get_length _ memory_token_counts.2
  have paired : leftToken = rightToken ∘ matchingPermutation := funext matching_tokens
  change leftTokens.Perm rightTokens
  rw [← left, ← right, paired]
  exact matchingPermutation.ofFn_comp_perm rightToken

end Airbender.NonVacuous.DynamicCopyLoop
