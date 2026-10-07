import Airbender.Proofs.AddSub
import Airbender.Proofs.BabyBear
import Airbender.Proofs.AddSub.Modular
import Airbender.Proofs.AddSub.NonDeterminism
import Airbender.Proofs.AddSub.Discarded

namespace Airbender.AddSub
open Airbender.Reference.RiscV

/-- Any satisfying assignment with the stated interfaces agrees with Sail's execution.
    Covers ADD/ADDI/SUB/LUI/AUIPC, including x0/NOP preprocessing and discarded writes.
    Includes nextPC initialization and PC retirement for the normal decoded four-byte path. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  Proofs.soundness hp inverse

/-- Concrete instance for the imported BabyBear artifact. -/
theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  soundness (p := babyBearModulus) (by decide) (by decide)

/-- Pure RTYPE/ITYPE writes to x0 use the imported ADD/SUB NOP row. This covers
    SLT/SLTI/SLTU/SLTIU as well as retained arithmetic, bitwise, register shifts and REV8;
    original Sail reads precede discarded writes and PC retirement. -/
theorem Discarded.soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (Discarded.circuitModel (p := p)).SoundnessUnder
      Discarded.InterfaceAssumptions Discarded.spec :=
  Proofs.discarded_soundness hp inverse

theorem Discarded.babyBear_soundness :
    (Discarded.circuitModel (p := babyBearModulus)).SoundnessUnder
      Discarded.InterfaceAssumptions Discarded.spec :=
  Discarded.soundness (by decide) (by decide)

/-- ADDMOD/SUBMOD/MULMOD/FMAMOD canonical results and native register/PC effects,
    including old-destination reads, aliasing and discarded x0 writes. Custom arithmetic
    is the reviewed project specification, not an upstream Sail instruction. -/
theorem Modular.soundness :
    Modular.circuitModel.SoundnessUnder Modular.InterfaceAssumptions Modular.spec :=
  Proofs.modular_soundness

/-- CSRRW x0, 0x7C0, rs1 preserves native state except nextPC/PC retirement.
    The custom project specification treats source values as unproved hints;
    oracle responses and application I/O are not covered by this claim. -/
theorem NonDeterminism.write_soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (NonDeterminism.writeModel (p := p)).SoundnessUnder
      NonDeterminism.WriteInterfaces NonDeterminism.writeSpec :=
  Proofs.nondeterminism_write_soundness hp inverse

theorem NonDeterminism.babyBear_write_soundness :
    (NonDeterminism.writeModel (p := babyBearModulus)).SoundnessUnder
      NonDeterminism.WriteInterfaces NonDeterminism.writeSpec :=
  NonDeterminism.write_soundness (by decide) (by decide)

end Airbender.AddSub
