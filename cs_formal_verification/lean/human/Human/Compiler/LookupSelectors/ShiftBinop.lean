module
public import Human.Compiler.NativeLookups
public import Human.Compiler.Captures.ShiftBinop

@[expose] public section
namespace Airbender.Compiler.NativeLookups

/-- All query operands of the cached ShiftBinop capture, in native leaf order. -/
def shiftBinopSelectors : List Selector := [
  ⟨⟨1, by decide⟩, 45, 0, []⟩,
  ⟨⟨2, by decide⟩, 47, 0, []⟩,
  ⟨⟨2, by decide⟩, 48, 0, []⟩,
  ⟨⟨2, by decide⟩, 48, 1, [8]⟩,
  ⟨⟨2, by decide⟩, 49, 0, [9]⟩,
  ⟨⟨2, by decide⟩, 49, 1, [10]⟩,
  ⟨⟨2, by decide⟩, 50, 0, [11]⟩,
  ⟨⟨2, by decide⟩, 50, 1, [12]⟩,
  ⟨⟨0, by decide⟩, 52, 0, [14]⟩,
  ⟨⟨1, by decide⟩, 68, 0, [22]⟩,
  ⟨⟨2, by decide⟩, 69, 0, [23, 13]⟩,
  ⟨⟨0, by decide⟩, 73, 0, [16]⟩,
  ⟨⟨0, by decide⟩, 73, 1, [17]⟩,
  ⟨⟨0, by decide⟩, 74, 0, [18]⟩,
  ⟨⟨0, by decide⟩, 74, 1, [19]⟩,
  ⟨⟨0, by decide⟩, 75, 0, [20]⟩
]

end Airbender.Compiler.NativeLookups
