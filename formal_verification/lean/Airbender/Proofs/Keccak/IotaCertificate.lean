import Airbender.Data.Setup.Keccak.FixedData
import Airbender.Proofs.Keccak.IotaReference
import Airbender.Proofs.Tables.ImportedBlocks
namespace Airbender.Keccak.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem periodic_xor_get (count value n : Nat) (bound : n < count * 256) :
    Block.get? (.periodic count 0 (Array.ofFn (fun i : Fin 256 => i.val ^^^ value))) n =
      some (n % 256 ^^^ value) := by
  have residue : n % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [Block.get?, Block.length, bound, residue]

private theorem repeated_byte (start count value n : Nat) (aligned : start % 256 = 0)
    (bound : n < count * 256)
    (reference : ∀ control : Fin count, IotaReference.byte (start / 256 + control.val) = value) :
    Block.get? (.periodic count 0 (Array.ofFn (fun i : Fin 256 => i.val ^^^ value))) n =
      some ((start + n) % 256 ^^^ IotaReference.byte ((start + n) / 256)) := by
  have quotient : (start + n) / 256 = start / 256 + n / 256 := by omega
  have control : n / 256 < count := by omega
  rw [periodic_xor_get _ _ _ bound, quotient, reference ⟨n / 256, control⟩]
  congr 2
  omega

macro "keccak_iota_small " start:num length:num first:num count:num value:num : tactic =>
  `(tactic|
    (change ∀ i : Fin $length, Block.get? _ i.val =
       some (($start + i.val) % 256 ^^^ IotaReference.byte (($start + i.val) / 256))
     intro i
     have byte_value : IotaReference.byte (($start + i.val) / 256) = $value := by
       have bound := i.isLt
       have checked : ∀ control : Fin $count,
           IotaReference.byte ($first + control.val) = $value := by decide +kernel
       have entry := checked ⟨($start + i.val) / 256 - $first, by omega⟩
       simpa only [show $first + (($start + i.val) / 256 - $first) =
         ($start + i.val) / 256 by omega] using entry
     rw [byte_value]
     clear byte_value
     revert i
     decide +kernel))

macro "keccak_iota_repeated " start:num count:num value:num : tactic =>
  `(tactic|
    (change ∀ i : Fin ($count * 256),
       Block.get? (.periodic $count 0 (Array.ofFn (fun j : Fin 256 => j.val ^^^ $value))) i.val =
         some (($start + i.val) % 256 ^^^ IotaReference.byte (($start + i.val) / 256))
     intro i
     exact repeated_byte $start $count $value i.val (by decide) i.isLt (by decide +kernel)))

private theorem reference_output_checks :
    checkBlocks (fun n => n % 256 ^^^ IotaReference.byte (n / 256)) 0
      iotaData.columns[2].blocks.toList = true := by
  dsimp only [iotaData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append]
  simp only [checkBlocks_cons_iff, checkBlocks_nil, and_true, Block.length,
    Array.size_ofFn, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  · keccak_iota_small 0 256 0 1 0
  · keccak_iota_small 256 256 1 1 1
  · keccak_iota_small 512 128 2 1 130
  · keccak_iota_small 640 128 2 1 130
  · keccak_iota_small 768 128 3 1 138
  · keccak_iota_small 896 128 3 1 138
  · keccak_iota_small 1024 256 4 1 0
  · keccak_iota_small 1280 128 5 1 139
  · keccak_iota_small 1408 128 5 1 139
  · keccak_iota_small 1536 256 6 1 1
  · keccak_iota_small 1792 128 7 1 129
  · keccak_iota_small 1920 128 7 1 129
  · keccak_iota_small 2048 256 8 1 9
  · keccak_iota_small 2304 128 9 1 138
  · keccak_iota_small 2432 128 9 1 138
  · keccak_iota_small 2560 128 10 1 136
  · keccak_iota_small 2688 128 10 1 136
  · keccak_iota_small 2816 256 11 1 9
  · keccak_iota_small 3072 256 12 1 10
  · keccak_iota_small 3328 128 13 1 139
  · keccak_iota_small 3456 256 13 2 139
  · keccak_iota_small 3712 128 14 1 139
  · keccak_iota_small 3840 128 15 1 137
  · keccak_iota_small 3968 128 15 1 137
  · keccak_iota_small 4096 256 16 1 3
  · keccak_iota_small 4352 256 17 1 2
  · keccak_iota_small 4608 128 18 1 128
  · keccak_iota_small 4736 128 18 1 128
  · keccak_iota_small 4864 256 19 1 10
  · keccak_iota_small 5120 256 20 1 10
  · keccak_iota_small 5376 128 21 1 129
  · keccak_iota_small 5504 128 21 1 129
  · keccak_iota_small 5632 128 22 1 128
  · keccak_iota_small 5760 128 22 1 128
  · keccak_iota_small 5888 256 23 1 1
  · keccak_iota_small 6144 256 24 1 8
  · keccak_iota_repeated 6400 9 0
  · keccak_iota_repeated 8704 4 128
  · keccak_iota_small 9728 256 38 1 0
  · keccak_iota_small 9984 128 39 1 128
  · keccak_iota_small 10112 256 39 2 128
  · keccak_iota_small 10368 128 40 1 128
  · keccak_iota_small 10496 256 41 1 0
  · keccak_iota_small 10752 256 42 1 0
  · keccak_iota_small 11008 128 43 1 128
  · keccak_iota_small 11136 128 43 1 128
  · keccak_iota_small 11264 256 44 1 0
  · keccak_iota_small 11520 128 45 1 128
  · keccak_iota_small 11648 128 45 1 128
  · keccak_iota_small 11776 256 46 1 0
  · keccak_iota_small 12032 128 47 1 128
  · keccak_iota_small 12160 256 47 2 128
  · keccak_iota_small 12416 256 48 2 128
  · keccak_iota_small 12672 128 49 1 128
  · keccak_iota_small 12800 256 50 1 0
  · keccak_iota_small 13056 128 51 1 128
  · keccak_iota_small 13184 128 51 1 128
  · keccak_iota_small 13312 256 52 1 0
  · keccak_iota_small 13568 128 53 1 128
  · keccak_iota_small 13696 256 53 2 128
  · keccak_iota_small 13952 128 54 1 128
  · keccak_iota_small 14080 256 55 1 0
  · keccak_iota_small 14336 128 56 1 128
  · keccak_iota_small 14464 128 56 1 128
  · keccak_iota_repeated 14592 43 0
  · keccak_iota_small 25600 128 100 1 128
  · keccak_iota_small 25728 128 100 1 128
  · keccak_iota_small 25856 256 101 1 0
  · keccak_iota_small 26112 128 102 1 128
  · keccak_iota_small 26240 256 102 2 128
  · keccak_iota_small 26496 128 103 1 128
  · keccak_iota_small 26624 256 104 1 0
  · keccak_iota_small 26880 256 105 1 0
  · keccak_iota_small 27136 256 106 1 0
  · keccak_iota_small 27392 128 107 1 128
  · keccak_iota_small 27520 256 107 2 128
  · keccak_iota_small 27776 256 108 2 128
  · keccak_iota_small 28032 128 109 1 128
  · keccak_iota_repeated 28160 6 0
  · keccak_iota_small 29696 128 116 1 128
  · keccak_iota_small 29824 256 116 2 128
  · keccak_iota_small 30080 128 117 1 128
  · keccak_iota_small 30208 256 118 1 0
  · keccak_iota_small 30464 128 119 1 128
  · keccak_iota_small 30592 256 119 2 128
  · keccak_iota_small 30848 128 120 1 128
  · keccak_iota_repeated 30976 106 0
  · keccak_iota_small 58112 128 227 1 128
  · keccak_iota_small 58240 256 227 2 128
  · keccak_iota_small 58496 128 228 1 128
  · keccak_iota_small 58624 256 229 1 0
  · keccak_iota_small 58880 256 230 1 0
  · keccak_iota_small 59136 128 231 1 128
  · keccak_iota_small 59264 256 231 2 128
  · keccak_iota_small 59520 128 232 1 128
  · keccak_iota_repeated 59648 5 0
  · keccak_iota_repeated 60928 5 128
  · keccak_iota_small 62208 256 243 1 0
  · keccak_iota_small 62464 128 244 1 128
  · keccak_iota_small 62592 256 244 2 128
  · keccak_iota_small 62848 256 245 2 128
  · keccak_iota_small 63104 128 246 1 128
  · keccak_iota_small 63232 256 247 1 0
  · keccak_iota_small 63488 128 248 1 128
  · keccak_iota_small 63616 128 248 1 128
  · keccak_iota_repeated 63744 7 0

theorem iota_output_checks :
    checkBlocks (fun n => n % 256 ^^^ iotaByte (n / 256)) 0
      iotaData.columns[2].blocks.toList = true := by
  simpa only [IotaReference.byte_eq] using reference_output_checks

end Airbender.Keccak.Proofs
