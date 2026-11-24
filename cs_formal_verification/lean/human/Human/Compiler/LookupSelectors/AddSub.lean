module
public import Human.Compiler.NativeLookups
public import Human.Compiler.Captures.AddSub

@[expose] public section
namespace Airbender.Compiler.NativeLookups

/-- All query operands of the cached AddSub capture, in native leaf order. -/
def addSubSelectors : List Selector := [
  ⟨⟨1, by decide⟩, 5, 0, []⟩,
  ⟨⟨1, by decide⟩, 6, 0, []⟩,
  ⟨⟨1, by decide⟩, 6, 1, []⟩,
  ⟨⟨1, by decide⟩, 7, 0, []⟩,
  ⟨⟨1, by decide⟩, 7, 1, []⟩,
  ⟨⟨2, by decide⟩, 9, 0, []⟩,
  ⟨⟨2, by decide⟩, 10, 0, []⟩,
  ⟨⟨2, by decide⟩, 10, 1, [8]⟩,
  ⟨⟨2, by decide⟩, 11, 0, [9]⟩,
  ⟨⟨2, by decide⟩, 11, 1, [10]⟩,
  ⟨⟨2, by decide⟩, 12, 0, [11]⟩,
  ⟨⟨2, by decide⟩, 12, 1, [12]⟩,
  ⟨⟨0, by decide⟩, 14, 0, [14]⟩,
  ⟨⟨1, by decide⟩, 48, 0, [17]⟩,
  ⟨⟨2, by decide⟩, 50, 0, [18, 13]⟩
]

end Airbender.Compiler.NativeLookups
