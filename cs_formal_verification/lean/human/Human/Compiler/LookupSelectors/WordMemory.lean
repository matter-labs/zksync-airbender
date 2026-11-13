module
public import Human.Compiler.NativeLookups
public import Human.Compiler.Captures.WordMemory

@[expose] public section
namespace Airbender.Compiler.NativeLookups

/-- All query operands of the cached WordMemory capture, in native leaf order. -/
def wordMemorySelectors : List Selector := [
  ⟨⟨1, by decide⟩, 13, 0, []⟩,
  ⟨⟨2, by decide⟩, 15, 0, []⟩,
  ⟨⟨2, by decide⟩, 16, 0, []⟩,
  ⟨⟨2, by decide⟩, 16, 1, [8]⟩,
  ⟨⟨2, by decide⟩, 17, 0, [9]⟩,
  ⟨⟨2, by decide⟩, 17, 1, [10]⟩,
  ⟨⟨2, by decide⟩, 18, 0, [11]⟩,
  ⟨⟨2, by decide⟩, 18, 1, [12]⟩,
  ⟨⟨0, by decide⟩, 20, 0, [14]⟩,
  ⟨⟨1, by decide⟩, 41, 0, [20]⟩,
  ⟨⟨2, by decide⟩, 43, 0, [21, 13]⟩,
  ⟨⟨1, by decide⟩, 53, 0, [25]⟩,
  ⟨⟨0, by decide⟩, 57, 0, [16]⟩
]

end Airbender.Compiler.NativeLookups
