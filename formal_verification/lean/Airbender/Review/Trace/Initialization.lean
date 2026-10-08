import Airbender.Review.Trace.ROM

namespace Airbender.Trace
open Reference.RiscV.Sail Reference.Sail

/-- The pinned profile's initial data, restricted to the public cell domain:
    PC=0, all base GPRs=0 and non-ROM RAM=0. These concern only the initial
    state, not instruction reads. RAM outside this domain is not accessed by
    the checked native trace. ROM retains its actual public program bytes.
    Source: `vendor/airbender/00-master.md`, Architectural state/Initial state. -/
structure InitialProfile (before : State) (cells : List Cell) : Prop where
  pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before
  registers : ∀ index, (Cell.register index).read before = .ok 0 before
  ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat →
    (Cell.ram address).read before = .ok 0 before

/-- Modeled boot seed, independent of circuit witnesses: zero GPR/RAM,
    actual public ROM bytes, and initialization timestamps zero. Missing ROM
    bytes fail. `InitialProfile` connects this seed to the actual Sail state.
    Native ROM permutation slots initialize to zero in Rust; binding those
    slots separately from public ROM bytes remains open. -/
def bootImage {p : Nat} (before : State) (cells : List Cell) :
    Option (List (MemoryToken p)) :=
  cells.mapM fun cell =>
    match cell with
    | .register _ => some (cell.initialToken 0)
    | .ram address =>
      if address.toNat < ROM.limit then
        match cell.read before with
        | .ok value _ => some (cell.initialToken value)
        | .error _ _ => none
      else some (cell.initialToken 0)

end Airbender.Trace
