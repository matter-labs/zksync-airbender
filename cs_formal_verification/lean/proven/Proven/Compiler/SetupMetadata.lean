module
public import Human.Compiler.NativePublicSetup
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.NativePublicSetup.Metadata
open Airbender Trace
set_option warningAsError true

def hasFunct3 : RVMachineDecoderFamily → Bool
  | .pooled .jumpBranchSlt | .pooled .shiftBinop | .unified => true
  | _ => false

def maskColumn (family : RVMachineDecoderFamily) : Nat := if hasFunct3 family then 8 else 7

def columns (family : RVMachineDecoderFamily) : Array Bool :=
  #[true, true, true, true, true, true, true, hasFunct3 family, true]

def width (family : RVMachineDecoderFamily) : Nat :=
  if family = .pooled .addSub then 8 else if hasFunct3 family then 10 else 9

def offset : RVMachineDecoderFamily → Nat
  | .pooled .addSub => 0
  | .pooled .jumpBranchSlt => 4456448
  | .pooled .mulDiv => 270336
  | .pooled .shiftBinop => 524545
  | .pooled .wordMemory => 1048577
  | .pooled .subwordMemory => 13238273
  | .unified => 2097537

/-- Decoder projection uses the current compiled circuit's exact mask. -/
theorem columns_binding (family : RVMachineDecoderFamily) :
    (NativeLookups.circuitFor family).decode_table_columns_mask = columns family := by
  cases family with
  | pooled family => cases family <;> kernel_rfl
  | unified => kernel_rfl

/-- Generic row widths include the native discriminator where present. -/
theorem width_binding (family : RVMachineDecoderFamily) :
    (NativeLookups.circuitFor family).generic_lookup_tables_width = width family := by
  cases family with
  | pooled family => cases family <;> kernel_rfl
  | unified => kernel_rfl

/-- Every fixed-region extent is the offset stored in the current native capture. -/
theorem offset_binding (family : RVMachineDecoderFamily) :
    (NativeLookups.circuitFor family).offset_for_decoder_table = offset family := by
  cases family with
  | pooled family => cases family <;> kernel_rfl
  | unified => kernel_rfl

end Airbender.Compiler.NativePublicSetup.Metadata
