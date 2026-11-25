module
public import Human.Circuits.UnifiedReduced.Proth120Input
public import Human.Helpers.Core.ExternalStream
public import Human.Trace.RVExecution

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Arithmetic

inductive Kind where | machine

noncomputable instance : CircuitLayout Kind where
  columns _ := importedConstraintsTraceColumns
  ports _ := importedConstraintsMemoryPorts
  decoderColumns _ := importedConstraintsDecoderColumns
  Setup p _ := Table (ZMod p) (fields 10)
  constraints _ setup := importedConstraints setup ++ importedConstraintsTimestampLookups

abbrev WrapTrace := Data proth120Modulus Kind

abbrev run := RV.runAt romEnd

noncomputable def isRead (row : Row proth120Modulus Kind) : Bool :=
  row.assignment importedConstraintsDecoderColumns.flags[8] == 1

def PublicDecode (s : RV.State) (read : Bool) (q : Vector (ZMod proth120Modulus) 9) : Prop :=
  (read = false ∧ Decoded s q) ∨ CSRDecoded s q read

/-- The decoder query at the native row's starting PC matches the public instruction bytes. -/
def Fetched (initial : RV.State) (row : Row proth120Modulus Kind) : Prop :=
  let pc := row.start.word.toBitVec
  pc.toNat % 4 = 0 ∧ pc.toNat + 4 ≤ romEnd ∧
    PublicDecode {initial with pc} (isRead row) (nativeDecoderQuery row.columns row.decoderColumns row.assignment)

structure TraceBoundary (trace : WrapTrace) (initial : RV.State) (cells : List Cell) : Prop where
  image : initialImageRV initial cells = some trace.initialMemory
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  pc : initial.pc = trace.initial.word.toBitVec
  clocks : ClockBoundary trace
  setup : trace.rom = tableWith (ROM.wordsRV initial)
  stream : ExternalStream.Ports Row.clock isRead (fun r => (wordAt r.assignment 50).toBitVec) trace.rows initial.input

structure TraceInputs (trace : WrapTrace) (initial : RV.State) (cells : List Cell) : Prop
    extends TraceBoundary trace initial cells where
  decoded : ∀ row ∈ trace.rows, Fetched initial row

def TraceResult (trace : WrapTrace) (initial : RV.State) (cells : List Cell) : Prop :=
  RealizesRun trace initial cells (ExternalStream.count isRead trace.rows) (run trace.rows.length initial)

/-- The unordered accepted rows execute from the public state to the native terminal PC and
    the final register and RAM values, consuming one independent stream word per CSR read. -/
def TraceSoundnessClaim : Prop :=
  ∀ (trace : WrapTrace) initial cells, TraceInputs trace initial cells → Accepted trace → TraceResult trace initial cells

def TraceSoundnessSatisfiableClaim : Prop :=
  ∃ (trace : WrapTrace) (initial : RV.State) (cells : List Cell),
    TraceInputs trace initial cells ∧ Accepted trace ∧ 0 < ExternalStream.count isRead trace.rows

end Airbender.UnifiedReduced.Proth120
