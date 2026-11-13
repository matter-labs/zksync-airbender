module
public import Human.Compiler.NativeLookups
public import Human.Compiler.Captures.MulDiv

@[expose] public section
namespace Airbender.Compiler.NativeLookups

/-- All query operands of the cached MulDiv capture, in native leaf order. -/
def mulDivSelectors : List Selector := [
  ⟨⟨1, by decide⟩, 26, 0, []⟩,
  ⟨⟨1, by decide⟩, 27, 0, []⟩,
  ⟨⟨1, by decide⟩, 27, 1, []⟩,
  ⟨⟨1, by decide⟩, 28, 0, []⟩,
  ⟨⟨1, by decide⟩, 28, 1, []⟩,
  ⟨⟨1, by decide⟩, 29, 0, []⟩,
  ⟨⟨1, by decide⟩, 29, 1, []⟩,
  ⟨⟨2, by decide⟩, 31, 0, []⟩,
  ⟨⟨2, by decide⟩, 32, 0, []⟩,
  ⟨⟨2, by decide⟩, 32, 1, [8]⟩,
  ⟨⟨2, by decide⟩, 33, 0, [9]⟩,
  ⟨⟨2, by decide⟩, 33, 1, [10]⟩,
  ⟨⟨2, by decide⟩, 34, 0, [11]⟩,
  ⟨⟨2, by decide⟩, 34, 1, [12]⟩,
  ⟨⟨0, by decide⟩, 36, 0, [14]⟩,
  ⟨⟨0, by decide⟩, 37, 0, [16]⟩,
  ⟨⟨0, by decide⟩, 37, 1, [17]⟩,
  ⟨⟨0, by decide⟩, 38, 0, [18]⟩,
  ⟨⟨0, by decide⟩, 38, 1, [19]⟩,
  ⟨⟨0, by decide⟩, 39, 0, [20]⟩,
  ⟨⟨0, by decide⟩, 39, 1, [21]⟩,
  ⟨⟨1, by decide⟩, 55, 0, [34]⟩,
  ⟨⟨2, by decide⟩, 59, 0, [35, 13]⟩,
  ⟨⟨0, by decide⟩, 63, 0, [22]⟩,
  ⟨⟨0, by decide⟩, 63, 1, [23]⟩
]

end Airbender.Compiler.NativeLookups
