module
public import Slop.Trace.OfflineMemory
public import Slop.Trace.Values
public import Slop.Trace.PC
public import Slop.Trace.Program
public import Slop.Trace.Addresses
public import Slop.Trace.MemoryHistory
public import Slop.Trace.ROMView
public import Slop.Trace.OracleConsumption
public import Slop.Trace.PooledOracleConsumption
public import Human.Helpers.Memory.ValueBoundary
public import Slop.Trace.Family.History
public import Human.Circuits.WordMemory.Output
public import Human.Helpers.Core.BabyBearPrime
public import Slop.Trace.CompositionCore
public import Slop.Trace.Family.Values
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Circuits.SubwordMemory.Output
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.JumpBranchSlt.PortReads
public import Slop.MulDiv.PortReads
public import Slop.MulDiv.Soundness
public import Slop.MulDiv.Values
public import Slop.ShiftBinop.PortReads
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.PortReads

@[expose] public section

namespace Airbender.Trace


theorem NonDeterminism.native_consumption {trace : Data babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {stream : List (BitVec 32)} (ports : NonDeterminism.StreamPorts trace stream) :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      ∃ rest, stream = NonDeterminism.consumed rows ++ rest :=
  NonDeterminism.Proofs.native_consumption (by decide) (by decide) accepted clocks ports


theorem NonDeterminism.Pooled.native_consumption {trace : PooledTrace babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {stream : List (BitVec 32)} (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      ∃ rest, stream = NonDeterminism.Pooled.consumed rows ++ rest :=
  NonDeterminism.Pooled.Proofs.native_consumption (by decide) (by decide) accepted clocks ports


theorem clocks {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ row ∈ trace.rows, ClockEffects row.columns row.assignment :=
  Proofs.trace_clocks (by decide) (by decide) accepted boundary


theorem terminal_clock {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    (timeOfPair trace.terminal.timestamp).value =
      (timeOfPair trace.initial.timestamp).value + 4 * trace.rows.length :=
  Proofs.trace_terminal_clock (by decide) (by decide) accepted boundary


theorem state_path {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∃ path, StatePath trace path :=
  Proofs.native_state_path (by decide) (by decide) accepted boundary


theorem unique_access_times {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) : trace.accessTimes.Nodup :=
  Proofs.access_times_unique (by decide) (by decide) accepted boundary


theorem initialized_addresses {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      port.address.code row.assignment ∈ trace.initialMemory.map MemoryToken.address :=
  Proofs.initialized_addresses (by decide) (by decide) accepted boundary


theorem memory_paths {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ source ∈ trace.initialMemory, ∃ path, MemoryPath trace source path :=
  Proofs.native_memory_paths (by decide) (by decide) accepted boundary unique


theorem latest_reads {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, LatestRead trace row port :=
  Proofs.latest_reads (by decide) (by decide) accepted boundary unique


theorem cell_histories {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ source ∈ trace.initialMemory, ∃ history, CellHistory trace source history :=
  Proofs.native_cell_histories (by decide) (by decide) accepted boundary unique


theorem memory_history {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∃ history, MemoryHistory trace history :=
  Proofs.native_memory_history (by decide) (by decide) accepted boundary unique


theorem read_bounds {trace : Data babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) (values : ValueBoundary trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded :=
  Proofs.read_bounds (by decide) (by decide) accepted clocks values


theorem terminal_bounds {trace : Data babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) (values : ValueBoundary trace) :
    ∀ token ∈ trace.terminalMemory, token.word.Bounded :=
  Proofs.terminal_bounds (by decide) (by decide) accepted clocks values


end Airbender.Trace
