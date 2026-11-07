import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowHistory
import Airbender.Proofs.Trace.CodeHistory
import Airbender.Proofs.Trace.ControlFlowCSR
import Airbender.Proofs.ReducedMachine.NativeROMImage

namespace Airbender.ReducedMachine.NativeWordMemoryHistoryProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Public architectural cells exclude the entire native ROM-shadow prefix.
    This is derived from the input constructor's actual address predicate. -/
theorem architectural_ram_domain {cells : List Cell}
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    (address : BitVec 32) (member : Cell.ram address ∈ cells) :
    4194304 ≤ address.toNat := by
  have selected := kept (Cell.ram address) member
  rw [NativeShadowProofs.architectural_ram] at selected
  exact of_decide_eq_true selected

/-- Actual projected Sail writes preserve every ROM byte, including missing
    bytes and untracked code. SW OLDREAD/write remains in this history. -/
theorem projected_history_rom_bytes {cells : List Cell}
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    {events : List MemoryAccess} {before after : State}
    (history : SailHistory cells events before after) :
    ∀ key < 4194304, after.mem[key]? = before.mem[key]? :=
  Trace.Proofs.history_byte_frame_of_domain history (architectural_ram_domain kept)

/-- Actual original indexed public construction and a meaningful ROM capacity
    bound place each full four-byte instruction window below native RAM. -/
theorem setup_rom_pc {before : State} {count logCapacity : Nat}
    {setup : SparseDecoderSetup WordMemoryMode}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (capacity : count ≤ 1048576) {entry : WordMemoryProgramEntry} (member : entry ∈ setup.program) :
    entry.pc.toNat+4 ≤ 4194304 := by
  obtain ⟨i,bound,built⟩ := Trace.Proofs.run_sparse_setup_selected image member
  have pc := (Trace.Proofs.run_entry_source built).1
  rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

/-- Preserved bytes and original control-CSR frames replay the retained stateful
    decoder in each derived pre-state. No later instruction read is supplied. -/
theorem entry_source_after_history {cells : List Cell}
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    {events : List MemoryAccess} {before after : State}
    (history : SailHistory cells events before after)
    {count logCapacity : Nat} {setup : SparseDecoderSetup WordMemoryMode}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (capacity : count ≤ 1048576) {entry : WordMemoryProgramEntry} (member : entry ∈ setup.program) :
    entry.SourceWith after wordMemoryDecoderFields := by
  have source := (Trace.Proofs.run_sparse_setup_sources image member).1
  exact ⟨Trace.Proofs.word_read_byte_frame (projected_history_rom_bytes kept history)
      (setup_rom_pc image capacity member) source.bytes,
    (Reference.Sail.decoded_misa_frame _ source.decoded).2 after
      (Trace.Proofs.sail_history_control_flow_csrs history).1,source.fields⟩

/-- The exact native fixture/padding byte constructor survives actual projected
    history. Every later ROM word read follows without an expected read premise. -/
theorem constructed_rom_read_after_history {cells : List Cell}
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    {events : List MemoryAccess} {initial after : State}
    (history : SailHistory cells events (NativeROM.state initial) after) (i : Fin 1048576) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read after =
      .ok (wordMemoryROMWord i.val).toBitVec after := by
  apply Trace.Proofs.word_read_byte_frame (projected_history_rom_bytes kept history)
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    have := i.isLt
    omega
  · exact NativeROMProofs.numerical_read initial i

end Airbender.ReducedMachine.NativeWordMemoryHistoryProofs
