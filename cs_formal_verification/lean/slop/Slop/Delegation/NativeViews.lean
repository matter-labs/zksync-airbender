module
public import Slop.Arithmetic.Word
public import Slop.Delegation.CallGroups

@[expose] public section

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true

theorem indirect_cell {p : Nat} {w : Nat → ZMod p} {port : Verification.IndirectPort} {cell : Cell}
    (code : cell.addressCode = (MemoryAddress.indirect port).code w) :
    cell = .ram (port.address w) := by
  cases cell with
  | register index => simp [Cell.addressCode, MemoryAddress.code, Nat.pair_eq_pair] at code
  | ram address =>
    have word := address_word code.symm
    have bits := congrArg Word.toBitVec word
    have same : port.address w = address := by
      simpa only [MemoryAddress.word, Verification.IndirectPort.rawAddress,
        Verification.IndirectPort.address, Cell.addressWord, Word.ofBitVec_roundtrip] using bits
    exact congrArg Cell.ram same.symm

end Airbender.Delegation.Proofs
