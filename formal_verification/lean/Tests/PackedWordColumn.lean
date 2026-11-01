import Airbender.Proofs.Tables.PackedWordColumn

namespace Tests.PackedWordColumn
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks PackedWordColumn
set_option warningAsError true

def first : Tree := .leaf [.affine 2 1 (-1)] 2 1
def second : Tree := .leaf [.dense 2 65536] 2 65536
def column : Tree := .branch first second
def badLength : Tree := .leaf [.affine 2 1 (-1)] 3 1
def badPayload : Tree := .leaf [.affine 2 1 (-1)] 2 65537
def extraPayload : Tree := .leaf [.affine 2 1 (-1)] 2 4294967297
def negativeEndpoint : Tree := .leaf [.affine 3 1 (-1)] 3 1
def emptyBlock : Tree := .leaf [.affine 0 0 0] 0 0

theorem checked : column.check = true := by decide +kernel
theorem bad_length_rejected : badLength.check = false := by decide +kernel
theorem changed_payload_rejected : badPayload.check = false := by decide +kernel
theorem extra_payload_rejected : extraPayload.check = false := by decide +kernel
theorem negative_endpoint_rejected : negativeEndpoint.check = false := by decide +kernel
theorem empty_block_rejected : emptyBlock.check = false := by decide +kernel

theorem row_count : column.length = 4 := by decide +kernel
theorem exact_values : (List.range 4).map (fun index => PackedSignedRun.digit 65536 column.payload index) =
    [1, 0, 0, 1] := by decide +kernel

theorem original_get (index : Nat) (within : index < 4) :
    getFromBlocks (column.blocks.map (Code.decode 65536)) index =
      some (PackedSignedRun.digit 65536 column.payload index) :=
  (column.check_sound checked).2.2 index (by simpa [row_count] using within)

theorem original_block_checks :
    checkBlocks (fun index => PackedSignedRun.digit 65536 column.payload index) 0
      (column.blocks.map (Code.decode 65536)) = true :=
  column.checkBlocks_sound _ 0 checked (by intro index within; simp only [Nat.zero_add])

def periodic : Tree := .leaf [.periodic 2 (-1) 2 65538] 4 4295032834

theorem periodic_checked : periodic.check = true := by decide +kernel

theorem reference_checked :
    column.checkReference (fun index => if index = 0 ∨ index = 3 then 1 else 0) 0 = true := by
  decide +kernel

theorem wrong_reference_rejected : column.checkReference (fun _ => 0) 0 = false := by decide +kernel

theorem reference_checks :
    checkBlocks (fun index => if index = 0 ∨ index = 3 then 1 else 0) 0
      (column.blocks.map (Code.decode 65536)) = true :=
  column.referenceChecks_sound _ 0 checked reference_checked (by intro index within; split_ifs <;> omega)

end Tests.PackedWordColumn
