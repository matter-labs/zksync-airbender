import Airbender.Proofs.FullUnsigned.ParityOutputPartition
import Airbender.Proofs.FullUnsigned.SourceBlockGroupChecks

namespace Airbender.Setup.SourceCaptureParityProofs.OutputIntervals
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- The complete original source output-column binding. -/
noncomputable def binding : SourceBank.ColumnBinding :=
  (SourceCaptureParity.columnBindings[5]'(by change 5 < 8; decide +kernel)).1

/-- An exact interval of original source blocks from the proved partition. -/
noncomputable def blocks (part : Nat) : List Block :=
  ((ParityOutputPartition.chunks[part]?).getD []).map binding.blocks

def offset (part : Nat) : Nat := ([0, 65781, 82164, 98548, 114932, 131316, 147700, 164084, 180468, 196852, 213236, 229604, 245988, 262372, 278756, 295140, 311524, 327908, 344292, 360676, 377060, 393444, 409828, 426212, 442596, 458980, 475364, 491748, 508132, 524516, 540900, 557284, 573668, 590052, 606436, 622820, 639204, 655588, 671972, 688356, 704740, 721124, 737508, 753892, 770276, 786660, 803044, 819428, 835812, 852196, 868580, 884964, 901348, 917732, 934116, 950500, 966884, 983268, 999652, 1016036, 1032420, 1048804, 1065188, 1081572, 1097956, 1114340, 1114356] : List Nat)[part]?.getD 0
def length (part : Nat) : Nat := ([65781, 16383, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16368, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16384, 16, 3079948] : List Nat)[part]?.getD 0

/-- The original native output formula at the physical source coordinate. -/
def expected (physical : Nat) : Nat :=
  let row := physical - 65780
  row % 16 ^^^ (row / 16 % 16) ^^^ (row / 256 % 16) ^^^ (row / 4096 % 16) ^^^ (row / 65536 % 16)

/-- A closed interval retains its exact length and every native output value. -/
def IntervalFact (part : Nat) : Prop :=
  ((blocks part).map Block.length).sum = length part ∧
    checkBlockRows expected (offset part) (blocks part) = true

end Airbender.Setup.SourceCaptureParityProofs.OutputIntervals
