module
public import Human.Compiler.NativeLookups
public import Human.Compiler.Captures.BlakeG

@[expose] public section
namespace Airbender.Compiler.NativeWorkerLookups

/-- Every primitive query of the cached worker, in gate and operand order. -/
def blakeGSelectors : List NativeLookups.Selector := [
  ⟨2, 11, 0, [20]⟩,
  ⟨2, 12, 0, [21]⟩,
  ⟨2, 12, 1, [22]⟩,
  ⟨2, 13, 0, [23]⟩,
  ⟨2, 13, 1, [24]⟩,
  ⟨2, 14, 0, [25]⟩,
  ⟨2, 14, 1, [26]⟩,
  ⟨2, 15, 0, [27]⟩,
  ⟨2, 15, 1, [28]⟩,
  ⟨2, 16, 0, [29]⟩,
  ⟨2, 16, 1, [30]⟩,
  ⟨2, 17, 0, [31]⟩,
  ⟨2, 17, 1, [32]⟩,
  ⟨2, 18, 0, [33]⟩,
  ⟨2, 18, 1, [34]⟩,
  ⟨2, 19, 0, [35]⟩,
  ⟨2, 19, 1, [36]⟩,
  ⟨2, 20, 0, [37]⟩,
  ⟨2, 20, 1, [38]⟩,
  ⟨2, 21, 0, [39]⟩,
  ⟨2, 21, 1, [40]⟩,
  ⟨0, 22, 0, [41]⟩,
  ⟨0, 23, 0, [43]⟩,
  ⟨0, 23, 1, [44]⟩,
  ⟨0, 24, 0, [45]⟩,
  ⟨0, 24, 1, [46]⟩,
  ⟨0, 25, 0, [47]⟩,
  ⟨0, 25, 1, [48]⟩,
  ⟨0, 26, 0, [49]⟩,
  ⟨0, 26, 1, [50]⟩,
  ⟨0, 27, 0, [51]⟩,
  ⟨0, 27, 1, [52]⟩,
  ⟨0, 28, 0, [53]⟩,
  ⟨0, 28, 1, [54]⟩,
  ⟨0, 29, 0, [55]⟩,
  ⟨0, 29, 1, [56]⟩,
  ⟨0, 30, 0, [57]⟩,
  ⟨0, 30, 1, [58]⟩,
  ⟨0, 31, 0, [59]⟩,
  ⟨0, 31, 1, [60]⟩
]

end Airbender.Compiler.NativeWorkerLookups
