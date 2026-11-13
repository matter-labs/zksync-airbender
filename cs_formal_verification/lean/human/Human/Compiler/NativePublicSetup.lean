module
public import Human.Compiler.NativeMachineArguments
public import Human.Compiler.NativeFixedRows
public import Human.Compiler.NativeFixedRows.Bindings
public import Human.Compiler.NativeSetups.Ranges

@[expose] public section
namespace Airbender.Compiler.NativePublicSetup
open Airbender Trace Arithmetic NativeArithmetic

/-- Production decoder tables have one slot per aligned ROM word. -/
abbrev decoderCapacity : Nat := 1048576

/-- The standalone AddSub table has no discriminator column. -/
def tagged : RVMachineDecoderFamily → Bool
  | .pooled .addSub => false
  | _ => true

/-- The payload uses exactly the mask stored in the current compiled circuit. -/
noncomputable def maskRow (family : RVMachineDecoderFamily) (row : Vector F 9) : List F :=
  row.toList.zipIdx.filterMap fun (value, index) =>
    if (NativeLookups.circuitFor family).decode_table_columns_mask[index]?.getD false
    then some value else none

/-- A native decoder request retains its exact projected fields and discriminator. -/
noncomputable def payload (family : RVMachineDecoderFamily) (row : Vector F 9) : List F :=
  maskRow family row ++ if tagged family then [46] else []

/-- A public program entry supplies native fields only to its selected circuit. -/
noncomputable def programRow (family : RVMachineDecoderFamily) (entry : RVMachineProgramEntry) : List F :=
  if entry.data.family = family then maskRow family ((entry.data.row entry.pc).map (fun (n : Nat) => (n : F)))
  else List.replicate ((NativeLookups.circuitFor family).generic_lookup_tables_width - if tagged family then 1 else 0) (-1)

/-- Public decoder slots retain unsupported-family sentinels and the committed tail. -/
noncomputable def decoderRow (family : RVMachineDecoderFamily)
    (program : List RVMachineProgramEntry) (index : Nat) : List F :=
  let width := (NativeLookups.circuitFor family).generic_lookup_tables_width
  let payload := (program[index]?).map (programRow family) |>.getD
    (List.replicate (width - if tagged family then 1 else 0) (-1))
  if tagged family then payload ++ [46] else payload

/-- Fixed and public-ROM native regions before the decoder table. The unified
    view only reorders the retained logical table indices. -/
noncomputable def fixedRow (family : RVMachineDecoderFamily) (words : Nat → BitVec 32)
    (index : Nat) : List F :=
  (match family with
  | .pooled .addSub => []
  | .pooled .jumpBranchSlt => (NativeFixedRows.jumpBranch (Fin.ofNat 4456448 index)).toList
  | .pooled .mulDiv => (NativeFixedRows.mulDiv (Fin.ofNat 270336 index)).toList
  | .pooled .shiftBinop => (Verification.shiftBinopRow (Fin.ofNat 524545 index)).toList
  | .pooled .wordMemory => (NativeFixedRows.wordMemory words (Fin.ofNat 1048577 index)).toList
  | .pooled .subwordMemory => (Verification.subwordRow words (Fin.ofNat 13238273 index)).toList
  | .unified => (NativeFixedRows.unified words (Fin.ofNat 2097537 index)).toList).map (fun (n : Nat) => (n : F))

/-- Native generic rows bind public program metadata and public ROM bytes.
    Tagged circuits retain zero commitment padding. AddSub retains its sentinel tail. -/
noncomputable def genericRow (family : RVMachineDecoderFamily) (initial : RV.State)
    (program : List RVMachineProgramEntry) (index : Nat) : List F :=
  let circuit := NativeLookups.circuitFor family
  if index < circuit.offset_for_decoder_table then fixedRow family (ROM.wordsRV initial) index
  else if index - circuit.offset_for_decoder_table < decoderCapacity then
    decoderRow family program (index - circuit.offset_for_decoder_table)
  else List.replicate circuit.generic_lookup_tables_width (if tagged family then 0 else -1)

/-- The independent public table interpretation for every native CPU lookup group.
    All setup imports check the full virtual columns, including zero padding. -/
noncomputable def rows (initial : RV.State) (program : List RVMachineProgramEntry) : ProgramLookupRows :=
  fun family group index =>
    if group.val = 0 then genericRow family initial program index.val
    else if group.val = 1 then [if index.val < 65536 then (index.val : F) else 0]
    else [if index.val < 524288 then (index.val : F) else 0]

/-- Public setup data. ROM bytes and native program projection are checked by the
    boot interface. This interface also pins capacity and omitted payload fields.
    Fixed-region comparisons and range checks run when their native views are imported. -/
structure Bound (initial : RV.State) (program : List RVMachineProgramEntry)
    (actual : ProgramLookupRows) : Prop where
  /-- Every public setup field equals its fixed, ROM or decoder interpretation. -/
  binding : actual = rows initial program
  /-- All supplied public entries fit the native decoder capacity. -/
  fits : program.length ≤ decoderCapacity
  /-- Each public native entry has a nonzero selector mask in the base field. -/
  mask : ∀ entry ∈ program, 0 < entry.data.mask ∧ entry.data.mask < babyBearModulus
  /-- Every omitted decoder coordinate is zero in the public native projection. -/
  omitted : ∀ entry ∈ program, ∀ index : Fin 9,
    (NativeLookups.circuitFor entry.data.family).decode_table_columns_mask[index.val]?.getD false = false →
      (entry.data.row entry.pc)[index] = 0

end Airbender.Compiler.NativePublicSetup

namespace Airbender.Compiler.NativePublicSetup
open Airbender Trace

/-- The tracked public domain contains each aligned ROM word used by the native word table. -/
def CoversROM (cells : List Cell) : Prop :=
  ∀ index : Fin 1048576, Cell.ram (BitVec.ofNat 32 (4 * index.val)) ∈ cells

end Airbender.Compiler.NativePublicSetup
