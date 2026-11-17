module
public import Human.Compiler.NativeMemory
public import Human.Compiler.Captures.Bigint
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

end Airbender.Compiler
