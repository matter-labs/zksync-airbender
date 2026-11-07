import Airbender.Review.Helpers.Memory.ReducedMachineShadowImage
import Airbender.Review.Helpers.Decoder.ReducedMachineWordMemory

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail
set_option autoImplicit false

/-- Actual port-domain observables. Only a ROM-region LW shadow is filtered;
    both readonly refreshes and every store OLDREAD/write remain native events. -/
def wordMemoryPortDomains (w : Nat → ZMod mersenne31Modulus) (entry : WordMemoryProgramEntry) : Vector Bool 3 :=
  #v[true,if entry.data.family then true else decide (64 ≤ (wordMemoryAddressWord w).hi),true]

/-- Projected architectural Sail realization of the full accepted native memory
    history. States/order/final matching/code bytes/CSR frames and decoder replay
    are conclusions, not inputs. Retained instruction execution is separate. -/
def WordMemoryProjectedHistory (trace : Data mersenne31Modulus NativeReducedFamily)
    (setup : SparseDecoderSetup WordMemoryMode) (initial : State) (cells : List Cell) : Prop :=
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
        entry.SourceWith initial wordMemoryDecoderFields ∧ entry.SourceWith rowBefore wordMemoryDecoderFields ∧
        row.decoderQuery = entry.query ∧
        SailHistory cells ((older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) initial rowBefore ∧
        SailHistory cells ((rowEvents trace.memoryEpoch row).reverse.filter
          fun event => architecturalAddress event.2.1) rowBefore rowAfter ∧
        SailHistory cells ((newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) rowAfter after

end Airbender.ReducedMachine.Native
