import Airbender.Review.Helpers.Properties

namespace Airbender.Blake2Worker

/-- Native logical variable coordinates. A descriptor observes an access; it
    does not establish shuffle-memory matching or an issued worker request. -/
structure Access where
  offset : Nat
  readTime : Vector Nat 2
  readValue : Vector Nat 2
  writeValue : Option (Vector Nat 2)
  deriving DecidableEq, Inhabited

structure RegisterAccess where
  register : Nat
  access : Access
  indirects : Array Access
  deriving DecidableEq, Inhabited

/-- Same-read native processor/ABI metadata; the 43 accesses retain both
    readonly refreshes and old reads. No architectural memory values are supplied. -/
structure ABI where
  multiplicity : Nat
  offsetHigh : Nat
  writeTime : Vector Nat 2
  registers : Array RegisterAccess
  booleanColumns : Array Nat
  traceLength : Nat
  witnessWidth : Nat
  memoryWidth : Nat
  setupWidth : Nat
  genericRows : Nat
  processingAux : Nat
  deriving DecidableEq, Inhabited

end Airbender.Blake2Worker
