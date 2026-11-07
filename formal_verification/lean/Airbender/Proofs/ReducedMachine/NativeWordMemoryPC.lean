import Airbender.Proofs.ReducedMachine.NativePC
import Airbender.Proofs.ReducedMachine.NativeWordMemoryPorts

namespace Airbender.ReducedMachine.NativeWordMemoryPCProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The original wordMemory profile selects the actual native default PC.
    Its bounds and RV32 rollover follow from the checked increment equations. -/
theorem selected_pc_successor {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (aligned : (initialPCWord w).lo % 4 = 0) :
    (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec = (initialPCWord w).toBitVec + 4 := by
  have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
  have pc := NativeWordMemoryAccessProofs.pc native entry.data.family decoded.mask
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) pc
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) pc
  change w 13 = w 49 at low
  change w 14 = w 50 at high
  apply NativePCProofs.default_pc_successor (by decide : 196608 < mersenne31Modulus) native
    (initial := initialPCWord w) (final := finalPCWord w)
    ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,
      congrArg ZMod.val low,congrArg ZMod.val high⟩
    (by
      have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
      change initialPCWord w = Word.ofBitVec entry.pc at canonical
      rw [canonical]
      exact Word.ofBitVec_bound _) aligned

/-- Public original decoding derives all incoming PC inputs and native successor
    bounds. No local PC, range, carry or successor answer is supplied. -/
theorem decoded_pc_successor {w : Nat → ZMod mersenne31Modulus}
    {setup : Trace.SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat} (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    (initialPCWord w).Bounded ∧ (initialPCWord w).lo % 4 = 0 ∧
      (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec = (initialPCWord w).toBitVec + 4 := by
  obtain ⟨entry,present,source,query⟩ := NativeWordMemoryDecoderProofs.fetched_sources image native member
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  have aligned : (initialPCWord w).lo % 4 = 0 := by
    rw [canonical]
    exact (Trace.Proofs.run_sparse_setup_sources image present).2
  exact ⟨by rw [canonical]; exact Word.ofBitVec_bound _,aligned,
    selected_pc_successor native source.fields query aligned⟩

end Airbender.ReducedMachine.NativeWordMemoryPCProofs
