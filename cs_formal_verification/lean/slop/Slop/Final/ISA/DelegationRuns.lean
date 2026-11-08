module
public import Slop.Deleg.BlakeRun
public import Slop.Deleg.BlakeG
public import Slop.Deleg.KeccakRun
public import Slop.Deleg.KeccakF1600Run

@[expose] public section

/-! The runs of delegation calls (`Human/ISA/DelegationRuns.lean`). -/

namespace RV

theorem calls_run : CallsRun := Deleg.calls_run
theorem blake_compress_run : BlakeCompressRun := Deleg.blake_compress_run
theorem blake_hash_run : BlakeHashRun := Deleg.blake_hash_run
theorem blake_compress_run10 : BlakeCompressRun10 := Deleg.blake_compress_run10
theorem blake_hash_run10 : BlakeHashRun10 := Deleg.blake_hash_run10
theorem blake_g_run : BlakeGRun := Deleg.blake_g_run
theorem blake_g_run10 : BlakeGRun10 := Deleg.blake_g_run10
theorem keccak_special5_run : KeccakSpecial5Run := Deleg.keccak_special5_run
theorem keccak_f1600_run : KeccakF1600Run := Deleg.keccak_f1600_run

end RV
