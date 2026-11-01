import Airbender.Proofs.Tables.PackedXor9Checks

namespace Tests.PackedSignedRun
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks
set_option warningAsError true

def decreasing : Input := ⟨3, -1, 2, 458755⟩
def increasing : Input := ⟨3, 2, 2, 65536⟩
def negativeEndpoint : Input := ⟨4, -1, 1, 2⟩
def largeEndpoint : Input := ⟨2, 1, 1, 65535⟩
def extraWord : Input := ⟨1, 0, 1, 65536⟩

theorem decreasing_valid : decreasing.valid 65536 = true := by decide +kernel
theorem increasing_valid : increasing.valid 65536 = true := by decide +kernel
theorem decreasing_words : (List.range 6).map (fun index =>
    PackedSignedRun.digit 65536 (decreasing.packed 65536) index) = [3, 7, 2, 6, 1, 5] := by decide +kernel
theorem increasing_words : (List.range 6).map (fun index =>
    PackedSignedRun.digit 65536 (increasing.packed 65536) index) = [0, 1, 2, 3, 4, 5] := by decide +kernel
theorem negative_endpoint_rejected : negativeEndpoint.valid 65536 = false := by decide +kernel
theorem large_endpoint_rejected : largeEndpoint.valid 65536 = false := by decide +kernel
theorem extra_word_rejected : extraWord.valid 65536 = false := by decide +kernel

def descendingBlock : Code := .affine 2 1 (-1)
def crossingBlock : Code := .dense 2 66047
def lastBlock : Code := .affine 1 0 0
def wrongStride : Code := .affine 2 1 1
def wrongHighBit : Code := .dense 2 65791

theorem descending_checked : PackedXor9Checks.check 512 [descendingBlock] = true := by decide +kernel
theorem crossing_checked : PackedXor9Checks.check 511 [crossingBlock] = true := by decide +kernel
theorem last_checked : PackedXor9Checks.check 262143 [lastBlock] = true := by decide +kernel
theorem wrong_stride_rejected : PackedXor9Checks.check 512 [wrongStride] = false := by decide +kernel
theorem changed_high_bit_rejected : PackedXor9Checks.check 511 [wrongHighBit] = false := by decide +kernel
theorem domain_overflow_rejected : PackedXor9Checks.check 262144 [lastBlock] = false := by decide +kernel
theorem excessive_window_rejected : PackedXor9Checks.legal 0 1025 = false := by decide +kernel

theorem original_descending : checkBlocks (fun index => index / 512 ^^^ index % 512) 512
    [Block.affine 2 1 (-1)] = true :=
  PackedXor9Checks.check_sound 512 [descendingBlock] descending_checked

theorem original_crossing : checkBlocks (fun index => index / 512 ^^^ index % 512) 511
    [(crossingBlock.decode 65536)] = true :=
  PackedXor9Checks.check_sound 511 [crossingBlock] crossing_checked

theorem complete_payload_binding : (Code.dense 2 66047).decode 65536 =
    Block.dense #[511, 1] := by decide +kernel

def requests : List PackedXor9Checks.Request :=
  [⟨512, [descendingBlock], 2⟩, ⟨511, [crossingBlock], 2⟩]
def wrongSize : List PackedXor9Checks.Request := [⟨512, [descendingBlock], 3⟩]

theorem requests_checked : PackedXor9Checks.checkRequests requests = true := by decide +kernel
theorem wrong_size_rejected : PackedXor9Checks.checkRequests wrongSize = false := by decide +kernel
theorem requested_source_length :
    (([descendingBlock].map (Code.decode 65536)).map Block.length).sum = 2 :=
  (PackedXor9Checks.requests_sound requests requests_checked 0 ⟨512, [descendingBlock], 2⟩ (by rfl)).2

def crossBorrow : Input := ⟨2, -1, 2, 33488896⟩
def highSeed : Input := ⟨1, 0, 1, 512⟩
def excessiveDelta : Input := ⟨2, 512, 1, 0⟩

theorem fast_decreasing_valid : PackedWordBounds.fastValid decreasing = true := by decide +kernel
theorem fast_increasing_valid : PackedWordBounds.fastValid increasing = true := by decide +kernel
theorem packed_borrow_rejected : PackedWordBounds.fastValid crossBorrow = false := by decide +kernel
theorem packed_high_seed_rejected : PackedWordBounds.fastValid highSeed = false := by decide +kernel
theorem packed_large_delta_rejected : PackedWordBounds.fastValid excessiveDelta = false := by decide +kernel
theorem original_bounds_derived : decreasing.valid 65536 = true :=
  PackedWordBounds.fastValid_sound decreasing fast_decreasing_valid

end Tests.PackedSignedRun
