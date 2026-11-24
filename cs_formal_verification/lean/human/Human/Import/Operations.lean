module
public import Human.Import.Columns
public import Human.Import.Coefficients
public import Human.Helpers.Tables.Range
public import Human.Helpers.Tables.Lookups
public import Human.Helpers.Tables.Bytes
public import Human.Circuits.JumpBranchSlt.Tables.Control

@[expose] public section

/-! # What the circuit JSON's equations and lookups mean

The imported operations of a circuit, as pure functions of the decoded artifact (`Circuit`): its structured
equations, then its 16-bit range queries, then (delegation workers) the pointer-alignment timestamp queries, then
its family's fixed-table queries. Each artifact's `ArtifactImportClaim` (in its `Artifact.lean`) states that the
imported definitions are these functions applied to the transcribed artifact. -/

namespace Airbender
namespace Import

variable {p : Nat} [Fact p.Prime]

/-- The integer `n` as a field constant. -/
def constant (n : Int) : Expression (ZMod p) := .const (Int.cast n)

mutual
/-- A JSON expression as a Clean expression. Coefficients are the signed representatives of their canonical
    residues; a sum (product) adds (multiplies) its terms in order onto the constant 0 (1). -/
def expression : Expr → Expression (ZMod p)
  | .Constant c => constant (Artifact.signedCoefficient c)
  | .Var v => .var ⟨v⟩
  | .Sum ⟨terms⟩ => sum (constant 0) terms
  | .Product ⟨factors⟩ => product (constant 1) factors

/-- `acc + t₁ + … + tₙ`, left to right. -/
def sum (acc : Expression (ZMod p)) : List Expr → Expression (ZMod p)
  | [] => acc
  | t :: ts => sum (.add acc (expression t)) ts

/-- `acc · t₁ · … · tₙ`, left to right. -/
def product (acc : Expression (ZMod p)) : List Expr → Expression (ZMod p)
  | [] => acc
  | t :: ts => product (.mul acc (expression t)) ts
end

/-- `AssertZero e` asserts `e = 0`; `Define v e` asserts `v + (-1) · e = 0`. -/
def statement : StructuredStatement → FlatOperation (ZMod p)
  | .AssertZero e _ _ => .assert (expression e)
  | .Define v _ e _ => .assert (.add (.var ⟨v⟩) (.mul (constant (-1)) (expression e)))

/-- The circuit families, by their lookup profile (`Columns.lean`). -/
inductive Family where
  | addSub | comparison | mulDiv | shiftBinop
  | wordMemory | subwordMemory | unifiedReduced
  | blakeG | blakeRound | bigint | keccak | keccakColumnParity | keccakThetaRho | keccakChi5
  deriving DecidableEq

/-- The delegation workers: their pointer-alignment queries are imported. -/
def Family.delegation : Family → Bool
  | .blakeG | .blakeRound | .bigint | .keccak | .keccakColumnParity | .keccakThetaRho | .keccakChi5 => true
  | _ => false

/-- The split Keccak workers whose memory ports share grouped read timestamps. -/
def Family.split : Family → Bool
  | .keccakThetaRho | .keccakChi5 => true
  | _ => false

/-- The fixed-table queries of a family whose queries use the setup table (all columns, tag included). -/
def Family.tableQueries : Family → Circuit → Except String (Array (Array Expr))
  | .wordMemory, c => c.wordMemoryQueries
  | .subwordMemory, c => c.subwordMemoryQueries
  | .unifiedReduced, c => c.unifiedReducedQueries
  | .blakeG, c => c.blakeGQueries
  | .blakeRound, c => c.blakeRoundQueries
  | .bigint, c => c.bigintQueries
  | .keccak, c => c.keccakQueries
  | .keccakColumnParity, c => c.keccakColumnParityQueries
  | .keccakThetaRho, c => c.keccakThetaRhoQueries
  | .keccakChi5, c => c.keccakChi5Queries
  | _, _ => throw "family has no setup-table queries"

end Import

namespace Circuit
open Import

variable {p : Nat} [Fact p.Prime]

/-- The structured equations. -/
def equations (c : Circuit) : List (FlatOperation (ZMod p)) :=
  c.structured_statements.toList.map statement

/-- The 16-bit range queries. -/
def rangeOperations (c : Circuit) : Except String (List (FlatOperation (ZMod p))) := do
  return (← c.range16Expressions).toList.map fun e => .lookup (Verification.range16 (expression e))

/-- Every timestamp range query, in order. -/
def timestampOperations (c : Circuit) : Except String (List (FlatOperation (ZMod p))) := do
  return (← c.timestampExpressions).toList.map fun e => .lookup (Trace.timestampLookup (expression e))

/-- A delegation worker's pointer-alignment queries: its timestamp queries after the invocation query and (unless
    the ports share grouped timestamps, `split`) the two comparison queries of each memory port. The worker's
    clock metadata must import. -/
def alignmentOperations (c : Circuit) (split : Bool) : Except String (List (FlatOperation (ZMod p))) := do
  let _ ← if split then c.splitDelegationColumns else c.delegationColumns
  let queries ← c.timestampExpressions
  let comparisons := if split then 0 else 2 * c.memory_layout.ram_access_sets.size
  return (queries.toList.drop (1 + comparisons)).map fun e => .lookup (Trace.timestampLookup (expression e))

/-- One comparison/mul-div query: table `id` applied to its key, its value (0 if absent) and, for the jump
    cleanup table, its result. -/
def pairQuery (id : Nat) (entries : Array Expr) : Except String (FlatOperation (ZMod p)) := do
  let some keyExpr := entries[0]? | throw "comparison lookup is missing its key"
  let key := expression keyExpr
  let value := match entries[1]? with
    | some e => expression e
    | none => constant 0
  let query ← match id with
    | 1 => pure (Verification.pairLookup Verification.regIsZeroTable key value)
    | 5 => pure (Verification.pairLookup Verification.u16SignTable key value)
    | 31 => pure (Verification.pairLookup Verification.conditionalTable key value)
    | 41 => pure (Verification.pairLookup Verification.u16LowByteTable key value)
    | 26 => pure (Verification.range13 key)
    | 2 => do
      let some cleaned := entries[2]? | throw "cleanup lookup is missing its result"
      pure (Verification.jumpCleanup key value (expression cleaned))
    | _ => throw "unsupported comparison table"
  return .lookup query

/-- A query of all `entries` against the native setup table. -/
def tableQuery {w : Nat} (table : Table (ZMod p) (fields w)) (entries : Array Expr) :
    Except String (FlatOperation (ZMod p)) := do
  let row := (entries.toList.map expression).toArray
  if h : row.size = table.toRaw.arity then return .lookup ⟨table.toRaw, ⟨row, h⟩⟩
  else throw "setup query width differs from the table"

/-- The imported operations of a family without a setup table: equations, range queries, then the family's
    fixed-table queries (none for ADD/SUB). -/
def operations (c : Circuit) (f : Family) : Except String (List (FlatOperation (ZMod p))) := do
  let fixed ← match f with
    | .comparison => do (← c.comparisonQueries).toList.mapM fun (id, entries) => pairQuery id entries
    | .mulDiv => do (← c.mulDivQueries).toList.mapM fun (id, entries) => pairQuery id entries
    | .shiftBinop => do
      (← c.shiftBinopQueries).toList.mapM fun entries => do
        let row := (entries.toList.map expression).toArray
        if h : row.size = 10 then return .lookup (Verification.shiftBinopLookup ⟨row, h⟩)
        else throw "shift/binop query width is not ten"
    | .addSub => pure []
    | _ => throw "family uses the setup table"
  return c.equations ++ (← c.rangeOperations) ++ fixed

/-- The imported operations of a family whose queries use the native setup table `table`: equations, range
    queries, the pointer-alignment queries of delegation workers, then the setup-table queries. -/
def tableOperations (c : Circuit) (f : Family) {w : Nat} (table : Table (ZMod p) (fields w)) :
    Except String (List (FlatOperation (ZMod p))) := do
  let alignments ← if f.delegation then c.alignmentOperations f.split else pure []
  let queries ← (← f.tableQueries c).toList.mapM (tableQuery table)
  return c.equations ++ (← c.rangeOperations) ++ alignments ++ queries

end Circuit

end Airbender
