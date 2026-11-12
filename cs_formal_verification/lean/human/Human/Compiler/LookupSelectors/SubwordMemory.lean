module
public import Human.Compiler.NativeLookups
public import Human.Compiler.Captures.SubwordMemory

@[expose] public section
namespace Airbender.Compiler.NativeLookups

/-- All query operands of the cached SubwordMemory capture, in native leaf order. -/
def subwordMemorySelectors : List Selector := [
  ⟨⟨1, by decide⟩, 23, 0, []⟩,
  ⟨⟨1, by decide⟩, 24, 0, []⟩,
  ⟨⟨1, by decide⟩, 24, 1, []⟩,
  ⟨⟨2, by decide⟩, 25, 0, []⟩,
  ⟨⟨2, by decide⟩, 26, 0, []⟩,
  ⟨⟨2, by decide⟩, 26, 1, [8]⟩,
  ⟨⟨2, by decide⟩, 27, 0, [9]⟩,
  ⟨⟨2, by decide⟩, 27, 1, [10]⟩,
  ⟨⟨2, by decide⟩, 28, 0, [11]⟩,
  ⟨⟨2, by decide⟩, 28, 1, [12]⟩,
  ⟨⟨0, by decide⟩, 30, 0, [14]⟩,
  ⟨⟨1, by decide⟩, 57, 0, []⟩,
  ⟨⟨1, by decide⟩, 57, 1, []⟩,
  ⟨⟨2, by decide⟩, 59, 0, [25, 13]⟩,
  ⟨⟨0, by decide⟩, 63, 0, [16]⟩,
  ⟨⟨0, by decide⟩, 72, 0, [17]⟩
]

end Airbender.Compiler.NativeLookups
