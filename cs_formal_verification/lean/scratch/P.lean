import Tests.TraceMemory
open Airbender Trace
def showAddr : MemoryAddress → String
  | .constantRegister i => s!"creg {i}" | .register c => s!"reg col {c}" | .mixed s b cs => s!"mixed {s} {b} {cs.toList}" | .indirect _ => "ind"
def showW : WordColumns → String
  | .zero => "zero" | .u16 c => s!"u16 {c.toList}" | .u8 c => s!"u8 {c.toList}"
#eval AddSub.importedConstraintsMemoryPorts.toList.map fun p => (p.clock.offset, p.clock.previous.toList, p.clock.borrow, showAddr p.address, showW p.readValue, p.writeValue.map showW)
