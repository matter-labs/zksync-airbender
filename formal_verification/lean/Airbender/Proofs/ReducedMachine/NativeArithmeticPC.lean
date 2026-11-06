import Airbender.Proofs.ReducedMachine.NativePC
import Airbender.Proofs.ReducedMachine.NativeArithmeticDecodedResult

namespace Airbender.ReducedMachine.NativeArithmeticPCProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The original arithmetic profile selects the actual native default PC.
    Its bounds and RV32 rollover follow from the checked increment equations. -/
theorem selected_pc_successor {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : ArithmeticProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : arithmeticDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (aligned : (initialPCWord w).lo % 4 = 0) :
    (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec = (initialPCWord w).toBitVec + 4 := by
  have decoded := NativeArithmeticDecoderProofs.decoded_fields fields query
  have pc := NativeArithmeticFieldProofs.pc native entry.data.family decoded.mask
  unfold finalPC at pc
  rw [NativePortProofs.final_pc_columns] at pc
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) pc
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) pc
  simp [defaultPC] at low high
  apply NativePCProofs.default_pc_successor (by decide : 196608 < mersenne31Modulus) native
    (initial := initialPCWord w) (final := finalPCWord w)
    ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,
      congrArg ZMod.val low,congrArg ZMod.val high⟩
    (NativeArithmeticResultProofs.decoded_pc_bound query) aligned

/-- Public original decoding derives all incoming PC inputs and native successor
    bounds. No local PC, range, carry or successor answer is supplied. -/
theorem decoded_pc_successor {w : Nat → ZMod mersenne31Modulus}
    {setup : Trace.SparseDecoderSetup ArithmeticMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat} {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    (image : arithmeticDecoderSetupImage before count logCapacity = some setup)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    (initialPCWord w).Bounded ∧ (initialPCWord w).lo % 4 = 0 ∧
      (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec = (initialPCWord w).toBitVec + 4 := by
  obtain ⟨entry,present,source,query⟩ := NativeArithmeticDecoderProofs.fetched_sources image native member
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  have aligned : (initialPCWord w).lo % 4 = 0 := by
    rw [canonical]
    exact (Trace.Proofs.run_sparse_setup_sources image present).2
  exact ⟨NativeArithmeticResultProofs.decoded_pc_bound query,aligned,
    selected_pc_successor native source.fields query aligned⟩

end Airbender.ReducedMachine.NativeArithmeticPCProofs
