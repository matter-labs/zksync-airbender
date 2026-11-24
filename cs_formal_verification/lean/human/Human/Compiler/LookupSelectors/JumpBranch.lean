module
public import Human.Compiler.NativeLookups
public import Human.Compiler.Captures.JumpBranch

@[expose] public section
namespace Airbender.Compiler.NativeLookups

/-- All query operands of the cached JumpBranch capture, in native leaf order. -/
def jumpBranchSelectors : List Selector := [
  ⟨⟨1, by decide⟩, 5, 0, []⟩,
  ⟨⟨1, by decide⟩, 6, 0, []⟩,
  ⟨⟨1, by decide⟩, 6, 1, []⟩,
  ⟨⟨2, by decide⟩, 8, 0, []⟩,
  ⟨⟨2, by decide⟩, 9, 0, []⟩,
  ⟨⟨2, by decide⟩, 9, 1, [8]⟩,
  ⟨⟨2, by decide⟩, 10, 0, [9]⟩,
  ⟨⟨2, by decide⟩, 10, 1, [10]⟩,
  ⟨⟨2, by decide⟩, 11, 0, [11]⟩,
  ⟨⟨2, by decide⟩, 11, 1, [12]⟩,
  ⟨⟨0, by decide⟩, 13, 0, [14]⟩,
  ⟨⟨0, by decide⟩, 14, 0, [16]⟩,
  ⟨⟨0, by decide⟩, 14, 1, [17]⟩,
  ⟨⟨0, by decide⟩, 15, 0, [18]⟩,
  ⟨⟨0, by decide⟩, 15, 1, [19]⟩,
  ⟨⟨1, by decide⟩, 45, 0, [21]⟩,
  ⟨⟨2, by decide⟩, 48, 0, [22, 13]⟩
]

end Airbender.Compiler.NativeLookups
