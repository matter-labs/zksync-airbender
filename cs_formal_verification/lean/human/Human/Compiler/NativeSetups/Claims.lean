module
public import Human.Compiler.NativeSetups.Fixture
public import Human.Compiler.NativeSetups.AddSub
public import Human.Compiler.NativeSetups.JumpBranch
public import Human.Compiler.NativeSetups.MulDiv
public import Human.Compiler.NativeSetups.ShiftBinop
public import Human.Compiler.NativeSetups.WordMemory
public import Human.Compiler.NativeSetups.SubwordMemory
public import Human.Compiler.NativeSetups.Unified

@[expose] public section
namespace Airbender.Compiler.NativeFixedRows
open Airbender Trace

/- Import claims of the generic rows of the CPU setups: for the setup fixture program, the public generic rows of each
   CPU circuit (`NativePublicSetup.genericRow`) are the imported native rows on the complete trace domain. The pooled
   circuits use the program of the full unrolled machine profile, the unified circuit the program of the unified
   profile. This module reads the raw setup data; the definitions that the machine claims use (`NativeFixedRows`,
   `NativePublicSetup`) do not import it. -/

/-- The add/sub setup has no fixed region; its padding rows hold the field element `-1` in each field. -/
def AddSubImportClaim : Prop :=
  NativeSetups.FixtureRows (.pooled .addSub) .unrolledFullUnsigned NativeSetups.addSubSetup

/-- The jump/branch setup: the fixed rows `jumpBranch`, the decoder rows, then zero padding. -/
def JumpBranchImportClaim : Prop :=
  NativeSetups.FixtureRows (.pooled .jumpBranchSlt) .unrolledFullUnsigned NativeSetups.jumpBranchSetup

/-- The multiply/divide setup: the fixed rows `mulDiv`, the decoder rows, then zero padding. -/
def MulDivImportClaim : Prop :=
  NativeSetups.FixtureRows (.pooled .mulDiv) .unrolledFullUnsigned NativeSetups.mulDivSetup

/-- The word-memory setup: the ROM rows `wordMemory` of the fixture ROM, the decoder rows, then zero padding. -/
def WordMemoryImportClaim : Prop :=
  NativeSetups.FixtureRows (.pooled .wordMemory) .unrolledFullUnsigned NativeSetups.wordMemorySetup

/-- The subword-memory setup: the fixed rows and the ROM rows of the fixture ROM (`Verification.subwordRow`), the
    decoder rows, then zero padding. -/
def SubwordMemoryImportClaim : Prop :=
  NativeSetups.FixtureRows (.pooled .subwordMemory) .unrolledFullUnsigned NativeSetups.subwordMemorySetup

/-- The unified setup: the fixed rows in native row order and the ROM rows of the fixture ROM (`unified`), the
    decoder rows, then zero padding. -/
def UnifiedImportClaim : Prop :=
  NativeSetups.FixtureRows .unified .unified NativeSetups.unifiedSetup

end Airbender.Compiler.NativeFixedRows

namespace Airbender.Verification
open Airbender Trace

/-- The shift/binary setup: the fixed rows `shiftBinopRow`, the decoder rows, then zero padding. -/
def ShiftBinopImportClaim : Prop :=
  Compiler.NativeSetups.FixtureRows (.pooled .shiftBinop) .unrolledFullUnsigned
    Compiler.NativeSetups.shiftBinopSetup

end Airbender.Verification
