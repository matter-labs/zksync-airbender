import Airbender.Review.Helpers.Decoder.UnifiedProgramRows
import Airbender.Review.Helpers.Memory.TextImage

namespace Airbender.Compiler
open Airbender.Trace Airbender.Trace.NativeDecoder Reference.RiscV.Sail

/-- Public, program-dependent decoder setup for either unrolled machine.
`columns` is the independently supplied setup column data; its equality to
the public-text model is explicit. The logical exact-lookup premise must still
bind an actual circuit query to these columns. -/
structure UnrolledProgramSetup (config : ProgramRows.Config)
    (initial : State) (text : List (BitVec 32)) (capacity : Nat)
    (masks : PooledFamily → ProgramRows.Mask)
    (columns : PooledFamily → List (List (ZMod babyBearModulus))) : Prop where
  image : ROM.TextImage initial text
  size : text.length ≤ ROM.limit / 4
  fits : text.length ≤ capacity
  groups : ProgramRows.WellFormedDelegationText config text
  decoderRows : ∀ family,
    columns family = ProgramRows.nativeDecoderRows config initial text capacity
      fits family (masks family)

/-- Public, program-dependent decoder setup for the unified reduced machine.
The unified decoder uses its own allowlist and one native circuit mask. This
statement does not reuse the retained four-word decoder or ROM image. -/
structure UnifiedProgramSetup (initial : State) (text : List (BitVec 32))
    (capacity : Nat) (mask : ProgramRows.Mask)
    (columns : List (List (ZMod babyBearModulus))) : Prop where
  image : ROM.TextImage initial text
  size : text.length ≤ ROM.limit / 4
  fits : text.length ≤ capacity
  groups : UnifiedProgramRows.WellFormedDelegationText text
  decoderRows : columns = UnifiedProgramRows.nativeDecoderRows initial text
    capacity fits mask

/-- Exact decoder lookup matching for actual unrolled witness rows against
the independently supplied public setup columns. A top theorem must use the
mask selected by each imported circuit, rather than an arbitrary wider mask.
This is the permitted logical lookup abstraction, not a proved constraint. -/
def UnrolledDecoderExactLookup [Fact babyBearModulus.Prime]
    (trace : PooledTrace babyBearModulus)
    (masks : PooledFamily → ProgramRows.Mask)
    (columns : PooledFamily → List (List (ZMod babyBearModulus))) : Prop :=
  ∀ row ∈ trace.rows,
    ProgramRows.maskRow (masks row.family) row.decoderQuery ∈ columns row.family

/-- The same exact logical lookup boundary for the unified circuit. -/
def UnifiedDecoderExactLookup [Fact babyBearModulus.Prime]
    (trace : UnifiedTrace babyBearModulus)
    (mask : ProgramRows.Mask)
    (columns : List (List (ZMod babyBearModulus))) : Prop :=
  ∀ row ∈ trace.rows,
    ProgramRows.maskRow mask row.decoderQuery ∈ columns

end Airbender.Compiler
