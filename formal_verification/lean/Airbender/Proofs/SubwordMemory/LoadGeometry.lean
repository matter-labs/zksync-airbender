import Airbender.Review.Helpers.Tables.NativeSubwordLoadData
import Airbender.Review.Helpers.Tables.SubwordLoad
import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.SubwordMemory.LoadProofs
open Setup Verification
set_option autoImplicit false

def lowSignValues : Array Nat := NativeSubwordLoad.dataValues1_0

theorem lowSignValues_size : lowSignValues.size = 256 := by
  simp only [lowSignValues, NativeSubwordLoad.dataValues1_0, Setup.Proofs.raw_size_append, Setup.Proofs.raw_literal_size,
    List.length_cons, List.length_nil, Nat.reduceAdd]

def highSignValues : Array Nat := NativeSubwordLoad.dataValues2_0

theorem highSignValues_size : highSignValues.size = 256 := by
  simp only [highSignValues, NativeSubwordLoad.dataValues2_0, Setup.Proofs.raw_size_append, Setup.Proofs.raw_literal_size,
    List.length_cons, List.length_nil, Nat.reduceAdd]

def rotatedByteValues : Array Nat := NativeSubwordLoad.dataValues1_10

theorem rotatedByteValues_size : rotatedByteValues.size = 256 := by simp only [rotatedByteValues, NativeSubwordLoad.dataValues1_10, Array.size_ofFn]

def rotatedCarryValues : Array Nat := NativeSubwordLoad.dataValues1_11

theorem rotatedCarryValues_size : rotatedCarryValues.size = 256 := by
  simp only [rotatedCarryValues, NativeSubwordLoad.dataValues1_11, Setup.Proofs.raw_size_append, Setup.Proofs.raw_literal_size,
    List.length_cons, List.length_nil, Nat.reduceAdd]

def lowBlocks : List Block :=
  [.periodic 256 0 lowSignValues,
   .periodic 128 1 (Array.replicate 256 0),
   .periodic 128 1 (Array.replicate 256 65408),
   .periodic 256 0 lowSignValues,
   .periodic 128 1 (Array.replicate 256 0),
   .periodic 128 1 (Array.replicate 256 65408),
   .affine 65536 0 1,
   .affine 65537 0 0,
   .affine 65535 1 1,
   .affine 589825 0 0,
   .periodic 256 0 rotatedByteValues,
   .periodic 255 1 rotatedCarryValues,
   .affine 255 255 0,
   .periodic 256 0 (Array.range 256),
   .periodic 256 1 (Array.replicate 256 0),
   .affine 65536 0 1,
   .affine 65537 0 0,
   .affine 65535 1 1,
   .affine 589824 0 0]

theorem lowBlocks_shape : NativeSubwordLoad.data.columns[1].blocks.toList = lowBlocks := rfl



def highBlocks : List Block :=
  [.periodic 256 0 highSignValues,
   .affine 32768 0 0,
   .affine 32768 65535 0,
   .periodic 256 0 highSignValues,
   .affine 32768 0 0,
   .affine 32768 65535 0,
   .affine 32768 0 0,
   .affine 32768 65535 0,
   .affine 98304 0 0,
   .affine 32768 65535 0,
   .affine 1638400 0 0]

theorem highBlocks_shape : NativeSubwordLoad.data.columns[2].blocks.toList = highBlocks := rfl



end Airbender.SubwordMemory.LoadProofs
