module
public import Human.Compiler.NativeMemory
public import Human.Compiler.Captures.AddSub
public import Human.Compiler.Captures.JumpBranch
public import Human.Compiler.Captures.MulDiv
public import Human.Compiler.Captures.ShiftBinop
public import Human.Compiler.Captures.SubwordMemory
public import Human.Compiler.Captures.WordMemory
public import Human.Compiler.Captures.Unified
public import Human.Helpers.Context.Registries.Pooled
public import Human.Helpers.UnifiedReduced.Registry

@[expose] public section
namespace Airbender.Compiler.NativeMemory

/-- Exact matching of the native PC-state tokens gives the raw state matching of the machine arguments. -/
def StateTokenMatchingClaim : Prop :=
  ∀ before after : List (PCState.State babyBearModulus),
    (before.map stateToken).Perm (after.map stateToken) → before.Perm after

/-- Two lists of PC states, the first nonempty, have matching tokens. -/
def StateTokenMatchingSatisfiableClaim : Prop :=
  ∃ before after : List (PCState.State babyBearModulus),
    (before.map stateToken).Perm (after.map stateToken) ∧ before ≠ []

end Airbender.Compiler.NativeMemory

namespace Airbender.Compiler
open Trace

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached add-sub row:
    the execute-masked products of its port tokens and PC-state tokens. -/
def AddSubCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Row babyBearModulus PooledFamily),
    row.family = .addSub →
    NativeArithmetic.Holds Captures.AddSub.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.AddSub.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.AddSub.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.AddSub.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.cpuReads row) (NativeMemory.cpuWrites row)

/-- A cached add-sub row with native base and extension values meets the memory premises. -/
def AddSubCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Row babyBearModulus PooledFamily),
    row.family = .addSub ∧
    NativeArithmetic.Holds Captures.AddSub.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.AddSub.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.AddSub.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached jump-branch row:
    the execute-masked products of its port tokens and PC-state tokens. -/
def JumpBranchCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Row babyBearModulus PooledFamily),
    row.family = .jumpBranchSlt →
    NativeArithmetic.Holds Captures.JumpBranch.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.JumpBranch.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.JumpBranch.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.JumpBranch.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.cpuReads row) (NativeMemory.cpuWrites row)

/-- A cached jump-branch row with native base and extension values meets the memory premises. -/
def JumpBranchCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Row babyBearModulus PooledFamily),
    row.family = .jumpBranchSlt ∧
    NativeArithmetic.Holds Captures.JumpBranch.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.JumpBranch.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.JumpBranch.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached mul-div row:
    the execute-masked products of its port tokens and PC-state tokens. -/
def MulDivCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Row babyBearModulus PooledFamily),
    row.family = .mulDiv →
    NativeArithmetic.Holds Captures.MulDiv.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.MulDiv.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.MulDiv.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.MulDiv.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.cpuReads row) (NativeMemory.cpuWrites row)

/-- A cached mul-div row with native base and extension values meets the memory premises. -/
def MulDivCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Row babyBearModulus PooledFamily),
    row.family = .mulDiv ∧
    NativeArithmetic.Holds Captures.MulDiv.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.MulDiv.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.MulDiv.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached shift-binop row:
    the execute-masked products of its port tokens and PC-state tokens. -/
def ShiftBinopCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Row babyBearModulus PooledFamily),
    row.family = .shiftBinop →
    NativeArithmetic.Holds Captures.ShiftBinop.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.ShiftBinop.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.ShiftBinop.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.ShiftBinop.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.cpuReads row) (NativeMemory.cpuWrites row)

/-- A cached shift-binop row with native base and extension values meets the memory premises. -/
def ShiftBinopCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Row babyBearModulus PooledFamily),
    row.family = .shiftBinop ∧
    NativeArithmetic.Holds Captures.ShiftBinop.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.ShiftBinop.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.ShiftBinop.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached subword-memory row:
    the execute-masked products of its port tokens and PC-state tokens. -/
def SubwordMemoryCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Row babyBearModulus PooledFamily),
    row.family = .subwordMemory →
    NativeArithmetic.Holds Captures.SubwordMemory.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.SubwordMemory.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.SubwordMemory.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.SubwordMemory.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.cpuReads row) (NativeMemory.cpuWrites row)

/-- A cached subword-memory row with native base and extension values meets the memory premises. -/
def SubwordMemoryCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Row babyBearModulus PooledFamily),
    row.family = .subwordMemory ∧
    NativeArithmetic.Holds Captures.SubwordMemory.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.SubwordMemory.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.SubwordMemory.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached word-memory row:
    the execute-masked products of its port tokens and PC-state tokens. -/
def WordMemoryCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Row babyBearModulus PooledFamily),
    row.family = .wordMemory →
    NativeArithmetic.Holds Captures.WordMemory.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.WordMemory.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.WordMemory.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.WordMemory.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.cpuReads row) (NativeMemory.cpuWrites row)

/-- A cached word-memory row with native base and extension values meets the memory premises. -/
def WordMemoryCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Row babyBearModulus PooledFamily),
    row.family = .wordMemory ∧
    NativeArithmetic.Holds Captures.WordMemory.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.WordMemory.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.WordMemory.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached unified row:
    the execute-masked products of its port tokens and PC-state tokens. -/
def UnifiedCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Row babyBearModulus UnifiedFamily),
    NativeArithmetic.Holds Captures.Unified.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.Unified.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.Unified.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.Unified.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.cpuReads row) (NativeMemory.cpuWrites row)

/-- A cached unified row with native base and extension values meets the memory premises. -/
def UnifiedCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Row babyBearModulus UnifiedFamily),
    NativeArithmetic.Holds Captures.Unified.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.Unified.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.Unified.imported.circuit challenges physical values

end Airbender.Compiler
