module
public import Human.Compiler.NativeMemory
public import Human.Compiler.Captures.Bigint
public import Human.Compiler.Captures.BlakeG
public import Human.Compiler.Captures.BlakeRound
public import Human.Compiler.Captures.KeccakColumnParity
public import Human.Compiler.Captures.KeccakThetaRho
public import Human.Compiler.Captures.KeccakChi5
public import Human.Trace.Machine.Model

@[expose] public section
namespace Airbender.Compiler.NativeMemory

/-- A standard worker row reads every port token and its issued request token. -/
def standardReads (row : Delegation.Row babyBearModulus) : List (Trace.MemoryToken babyBearModulus) :=
  row.ports.toList.map (Trace.readToken row.assignment) ++ [(Delegation.Requests.fulfillment row).issued]

/-- A standard worker row writes every port token and its returned request token. -/
def standardWrites (row : Delegation.Row babyBearModulus) : List (Trace.MemoryToken babyBearModulus) :=
  row.ports.toList.map row.writeToken ++ [(Delegation.Requests.fulfillment row).empty]

/-- A split worker row reads every port token and its issued request token. -/
def splitReads (row : Keccak.Split.Native.Row babyBearModulus) : List (Trace.MemoryToken babyBearModulus) :=
  row.ports.toList.map (Trace.readToken row.assignment) ++ [(Trace.Machine.splitFulfillment row).issued]

/-- A split worker row writes every port token and its returned request token. -/
def splitWrites (row : Keccak.Split.Native.Row babyBearModulus) : List (Trace.MemoryToken babyBearModulus) :=
  row.ports.toList.map row.writeToken ++ [(Trace.Machine.splitFulfillment row).empty]

end Airbender.Compiler.NativeMemory

namespace Airbender.Compiler

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached bigint row:
    the execute-masked products of its port tokens and request tokens. -/
def BigintCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Delegation.Row babyBearModulus),
    row.family = .bigint →
    NativeArithmetic.Holds Captures.Bigint.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.Bigint.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.Bigint.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.Bigint.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.standardReads row) (NativeMemory.standardWrites row)

/-- A cached bigint row with native base and extension values meets the memory premises. -/
def BigintCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Delegation.Row babyBearModulus),
    row.family = .bigint ∧
    NativeArithmetic.Holds Captures.Bigint.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.Bigint.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.Bigint.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached BLAKE2 G row:
    the execute-masked products of its port tokens and request tokens. -/
def BlakeGCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Delegation.Row babyBearModulus),
    row.family = .blakeG →
    NativeArithmetic.Holds Captures.BlakeG.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.BlakeG.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.BlakeG.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.BlakeG.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.standardReads row) (NativeMemory.standardWrites row)

/-- A cached BLAKE2 G row with native base and extension values meets the memory premises. -/
def BlakeGCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Delegation.Row babyBearModulus),
    row.family = .blakeG ∧
    NativeArithmetic.Holds Captures.BlakeG.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.BlakeG.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.BlakeG.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached BLAKE2 round row:
    the execute-masked products of its port tokens and request tokens. -/
def BlakeRoundCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Delegation.Row babyBearModulus),
    row.family = .blakeRound →
    NativeArithmetic.Holds Captures.BlakeRound.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.BlakeRound.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.BlakeRound.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.BlakeRound.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.standardReads row) (NativeMemory.standardWrites row)

/-- A cached BLAKE2 round row with native base and extension values meets the memory premises. -/
def BlakeRoundCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Delegation.Row babyBearModulus),
    row.family = .blakeRound ∧
    NativeArithmetic.Holds Captures.BlakeRound.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.BlakeRound.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.BlakeRound.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached column parity row:
    the execute-masked products of its port tokens and request tokens. -/
def KeccakColumnParityCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Keccak.Split.Native.Row babyBearModulus),
    row.kind = .columnParity →
    NativeArithmetic.Holds Captures.KeccakColumnParity.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.KeccakColumnParity.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.KeccakColumnParity.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.KeccakColumnParity.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.splitReads row) (NativeMemory.splitWrites row)

/-- A cached column parity row with native base and extension values meets the memory premises. -/
def KeccakColumnParityCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Keccak.Split.Native.Row babyBearModulus),
    row.kind = .columnParity ∧
    NativeArithmetic.Holds Captures.KeccakColumnParity.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.KeccakColumnParity.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.KeccakColumnParity.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached theta/rho row:
    the execute-masked products of its port tokens and request tokens. -/
def KeccakThetaRhoCachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Keccak.Split.Native.Row babyBearModulus),
    row.kind = .thetaRho →
    NativeArithmetic.Holds Captures.KeccakThetaRho.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.KeccakThetaRho.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.KeccakThetaRho.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.KeccakThetaRho.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.splitReads row) (NativeMemory.splitWrites row)

/-- A cached theta/rho row with native base and extension values meets the memory premises. -/
def KeccakThetaRhoCachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Keccak.Split.Native.Row babyBearModulus),
    row.kind = .thetaRho ∧
    NativeArithmetic.Holds Captures.KeccakThetaRho.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.KeccakThetaRho.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.KeccakThetaRho.imported.circuit challenges physical values

/-- Native base gates, extension caches and RAM-product gates give the RAM outputs of a cached chi5 row:
    the execute-masked products of its port tokens and request tokens. -/
def KeccakChi5CachedMemoryClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → E) (row : Keccak.Split.Native.Row babyBearModulus),
    row.kind = .chi5 →
    NativeArithmetic.Holds Captures.KeccakChi5.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.KeccakChi5.imported.circuit physical row.assignment →
    NativeMemory.Holds Captures.KeccakChi5.imported.circuit challenges physical values →
    NativeMemory.RamProducts Captures.KeccakChi5.imported.circuit challenges values
      (row.assignment row.columns.execute) (NativeMemory.splitReads row) (NativeMemory.splitWrites row)

/-- A cached chi5 row with native base and extension values meets the memory premises. -/
def KeccakChi5CachedMemorySatisfiableClaim : Prop :=
  ∃ (challenges : NativeMemory.Challenges NativeArithmetic.F) (physical : GKRAddress → NativeArithmetic.F)
    (values : GKRAddress → NativeArithmetic.F) (row : Keccak.Split.Native.Row babyBearModulus),
    row.kind = .chi5 ∧
    NativeArithmetic.Holds Captures.KeccakChi5.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.KeccakChi5.imported.circuit physical row.assignment ∧
    NativeMemory.Holds Captures.KeccakChi5.imported.circuit challenges physical values

end Airbender.Compiler
