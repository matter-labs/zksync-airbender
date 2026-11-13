module
public import Proven.Compiler.ScopeTransport
public import Human.Compiler.LookupSelectors
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBridge.ScopeChecks
open Airbender

theorem addSub_scope :
    (AddSub.clockConstraints (p := babyBearModulus)).all (operationScope 48) = true := by
  kernel_rfl

theorem jumpBranch_scope :
    (JumpBranchSlt.clockConstraints (p := babyBearModulus)).all (operationScope 55) = true := by
  kernel_rfl

theorem mulDiv_scope :
    (MulDiv.clockConstraints (p := babyBearModulus)).all (operationScope 71) = true := by
  kernel_rfl

theorem shiftBinop_scope :
    (ShiftBinop.clockConstraints (p := babyBearModulus)).all (operationScope 98) = true := by
  kernel_rfl

theorem wordMemory_scope (setup : Table NativeArithmetic.F (fields 9)) :
    (WordMemory.clockConstraints (p := babyBearModulus) setup).all (operationScope 52) = true := by
  kernel_rfl

theorem subwordMemory_scope (setup : Table NativeArithmetic.F (fields 9)) :
    (SubwordMemory.clockConstraints (p := babyBearModulus) setup).all (operationScope 68) = true := by
  kernel_rfl

theorem unified_scope (setup : Table NativeArithmetic.F (fields 10)) :
    (UnifiedReduced.clockConstraints (p := babyBearModulus) setup).all (operationScope 137) = true := by
  kernel_rfl

end Airbender.Compiler.NativeBridge.ScopeChecks
