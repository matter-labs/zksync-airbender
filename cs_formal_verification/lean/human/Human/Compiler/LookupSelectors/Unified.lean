module
public import Human.Compiler.NativeLookups
public import Human.Compiler.Captures.Unified

@[expose] public section
namespace Airbender.Compiler.NativeLookups

/-- All query operands of the cached Unified capture, in native leaf order. -/
def unifiedSelectors : List Selector := [
  ⟨⟨1, by decide⟩, 48, 0, []⟩,
  ⟨⟨1, by decide⟩, 49, 0, []⟩,
  ⟨⟨1, by decide⟩, 49, 1, []⟩,
  ⟨⟨1, by decide⟩, 50, 0, []⟩,
  ⟨⟨1, by decide⟩, 50, 1, []⟩,
  ⟨⟨1, by decide⟩, 51, 0, []⟩,
  ⟨⟨1, by decide⟩, 51, 1, []⟩,
  ⟨⟨1, by decide⟩, 52, 0, []⟩,
  ⟨⟨1, by decide⟩, 52, 1, []⟩,
  ⟨⟨1, by decide⟩, 53, 0, []⟩,
  ⟨⟨1, by decide⟩, 53, 1, []⟩,
  ⟨⟨2, by decide⟩, 55, 0, []⟩,
  ⟨⟨2, by decide⟩, 56, 0, []⟩,
  ⟨⟨2, by decide⟩, 56, 1, [8]⟩,
  ⟨⟨2, by decide⟩, 57, 0, [9]⟩,
  ⟨⟨2, by decide⟩, 57, 1, [10]⟩,
  ⟨⟨2, by decide⟩, 58, 0, [11]⟩,
  ⟨⟨2, by decide⟩, 58, 1, [12]⟩,
  ⟨⟨0, by decide⟩, 60, 0, [14]⟩,
  ⟨⟨1, by decide⟩, 143, 0, [22]⟩,
  ⟨⟨1, by decide⟩, 146, 0, []⟩,
  ⟨⟨2, by decide⟩, 147, 0, [23, 13]⟩,
  ⟨⟨0, by decide⟩, 151, 0, [16]⟩,
  ⟨⟨0, by decide⟩, 151, 1, [17]⟩,
  ⟨⟨0, by decide⟩, 152, 0, [18]⟩,
  ⟨⟨0, by decide⟩, 152, 1, [19]⟩,
  ⟨⟨0, by decide⟩, 153, 0, [20]⟩
]

end Airbender.Compiler.NativeLookups
