import Airbender.Review.Circuits.ReducedMachine.UnifiedDecoder
import Airbender.Review.Helpers.Memory.ReducedMachineWordMemoryHistory

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail
set_option autoImplicit false

/-- Observable architectural projection for the actual three native ports.
    A separate proof derives these domains from original decoding/native fields. -/
def unifiedPortDomains (w : Nat → ZMod mersenne31Modulus) (entry : UnifiedProgramEntry) : Vector Bool 3 :=
  match entry.data.family with
  | .inl _ => #v[true,true,true]
  | .inr store => #v[true,if store then true else decide (64 ≤ (wordMemoryAddressWord w).hi),true]

/-- Common projected original Sail states/segments, ROM-byte/CSR frames and
    stateful source replay. All native shadow tokens stay in full matching.
    Per-profile retained instruction execution is a later connection. -/
def UnifiedProjectedHistory (trace : Data mersenne31Modulus NativeReducedFamily)
    (setup : SparseDecoderSetup UnifiedMode) (initial : State) (cells : List Cell) : Prop :=
  ∃ (history : TimestampSortedMemoryAccessList)
    (rows : List (Row mersenne31Modulus NativeReducedFamily)) (after : State),
    MemoryHistory trace history ∧ rows.Perm trace.rows ∧
    rows.Pairwise (fun a b => b.clock < a.clock) ∧
    SailHistory cells
      ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
        fun event => architecturalAddress event.2.1) initial after ∧
    SailStateMatches cells history after ∧
    (∀ key < 4194304, after.mem[key]? = initial.mem[key]?) ∧
    after.regs.get? .misa = initial.regs.get? .misa ∧
    ∀ newer row older, rows = newer ++ row :: older →
      ∃ entry ∈ setup.program, ∃ rowBefore rowAfter,
        entry.SourceWith initial unifiedDecoderFields ∧ entry.SourceWith rowBefore unifiedDecoderFields ∧
        row.decoderQuery = entry.query ∧
        SailHistory cells ((older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) initial rowBefore ∧
        SailHistory cells ((rowEvents trace.memoryEpoch row).reverse.filter
          fun event => architecturalAddress event.2.1) rowBefore rowAfter ∧
        SailHistory cells ((newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) rowAfter after


end Airbender.ReducedMachine.Native
