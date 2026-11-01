import Airbender.Proofs.GKRProtocol.SubwordRegionLengths.Column1.Certificate

namespace Airbender.Compiler.SubwordRegionLengths.Column1
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false

theorem length0 : ((Airbender.Verification.subwordZeroData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1 := by
  rw [binding0]
  exact facts ⟨0, by decide +kernel⟩

theorem length1 : ((Airbender.Verification.storePlaceData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 131072 := by
  rw [binding1]
  exact facts ⟨1, by decide +kernel⟩

theorem length2 : ((Airbender.Verification.storeClearData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 131072 := by
  rw [binding2]
  exact facts ⟨2, by decide +kernel⟩

theorem length3 : ((Airbender.Verification.loadHalfData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 131072 := by
  rw [binding3]
  exact facts ⟨3, by decide +kernel⟩

theorem length4 : ((Airbender.Verification.loadByteData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 262144 := by
  rw [binding4]
  exact facts ⟨4, by decide +kernel⟩

end Airbender.Compiler.SubwordRegionLengths.Column1
