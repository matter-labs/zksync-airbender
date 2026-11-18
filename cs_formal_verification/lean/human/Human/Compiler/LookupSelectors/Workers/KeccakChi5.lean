module
public import Human.Compiler.NativeLookups
public import Human.Compiler.Captures.KeccakChi5

@[expose] public section
namespace Airbender.Compiler.NativeWorkerLookups

/-- Every primitive query of the cached worker, in gate and operand order. -/
def keccakChi5Selectors : List NativeLookups.Selector := [
  ⟨2, 15, 0, [26]⟩,
  ⟨0, 17, 0, [28]⟩,
  ⟨0, 18, 0, [30]⟩,
  ⟨0, 18, 1, [31]⟩,
  ⟨0, 19, 0, [32]⟩,
  ⟨0, 19, 1, [33]⟩,
  ⟨0, 20, 0, [34]⟩,
  ⟨0, 20, 1, [35]⟩,
  ⟨0, 21, 0, [36]⟩,
  ⟨0, 21, 1, [37]⟩,
  ⟨0, 22, 0, [38]⟩,
  ⟨0, 22, 1, [39]⟩,
  ⟨0, 23, 0, [40]⟩,
  ⟨0, 23, 1, [41]⟩,
  ⟨0, 24, 0, [42]⟩,
  ⟨0, 24, 1, [43]⟩,
  ⟨0, 25, 0, [44]⟩,
  ⟨0, 25, 1, [45]⟩,
  ⟨2, 50, 0, [49, 27]⟩
]

end Airbender.Compiler.NativeWorkerLookups
