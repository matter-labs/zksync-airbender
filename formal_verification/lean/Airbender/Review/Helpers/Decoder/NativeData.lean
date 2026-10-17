import Airbender.Review.Helpers.Decoder.Columns

namespace Airbender.Trace

/-- Preserve DecoderTableEntry.flatten order from native v2 bytecode preprocessing:
    PC, source/destination indices, destination-zero flag, immediate, funct3, mask.
    This interpretation supplies no membership or expected decoder-field values. -/
def nativeDecoderQuery {p : Nat} (columns : TraceColumns) (c : DecoderColumns)
    (w : Nat → ZMod p) : Vector (ZMod p) 10 :=
  #v[w columns.initialPC[0], w columns.initialPC[1], w c.rs1, w c.rs2,
    w c.rd, w c.rdIsZero, w c.immediate[0], w c.immediate[1], w c.funct3, w c.mask]

end Airbender.Trace
