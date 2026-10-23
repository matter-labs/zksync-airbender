import Tests.PathGLoopCPU.ProjectionLoopShared
set_option Elab.async false

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram

/- All actual BranchTaken certificates, elaborated serially without changing their assertions. -/

theorem cpu_loop_branchtaken_checked_i000_007_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i000_007_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i000_007_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i000_007_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i000_007_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i000_007_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i000_007_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i000_007_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i000_007_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 0 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i008_015_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i008_015_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i008_015_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i008_015_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i008_015_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i008_015_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i008_015_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i008_015_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i008_015_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 8 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i016_023_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i016_023_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i016_023_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i016_023_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i016_023_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i016_023_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i016_023_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i016_023_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i016_023_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 16 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i024_031_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i024_031_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i024_031_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i024_031_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i024_031_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i024_031_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i024_031_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i024_031_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i024_031_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 24 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i032_039_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i032_039_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i032_039_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i032_039_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i032_039_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i032_039_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i032_039_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i032_039_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i032_039_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 32 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i040_047_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i040_047_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i040_047_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i040_047_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i040_047_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i040_047_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i040_047_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i040_047_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i040_047_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 40 8
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i048_053_e000_015 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 48 6
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 0).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i048_053_e016_031 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 48 6
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 16).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i048_053_e032_047 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 48 6
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 32).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i048_053_e048_063 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 48 6
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 48).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i048_053_e064_079 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 48 6
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 64).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i048_053_e080_095 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 48 6
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 80).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i048_053_e096_111 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 48 6
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 96).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i048_053_e112_127 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 48 6
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 112).take 16) = true := by
  decide +kernel

theorem cpu_loop_branchtaken_checked_i048_053_e128_128 :
    gCpuProjectedLoopBatchCheck (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) 48 6
      (((gCpuPolynomials (UnifiedReduced.Setup.table (before .baseline))).drop 128).take 1) = true := by
  decide +kernel

private theorem cpu_loop_branchtaken_indices_000_007 (variant : Variant) (index : Fin 54)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 0 ≤ index.val) (indexStop : index.val < 8) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 0 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i000_007_e000_015 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 0 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i000_007_e016_031 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 0 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i000_007_e032_047 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 0 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i000_007_e048_063 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 0 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i000_007_e064_079 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 0 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i000_007_e080_095 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 0 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i000_007_e096_111 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 0 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i000_007_e112_127 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 0 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i000_007_e128_128 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)

private theorem cpu_loop_branchtaken_indices_008_015 (variant : Variant) (index : Fin 54)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 8 ≤ index.val) (indexStop : index.val < 16) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 8 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i008_015_e000_015 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 8 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i008_015_e016_031 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 8 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i008_015_e032_047 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 8 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i008_015_e048_063 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 8 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i008_015_e064_079 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 8 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i008_015_e080_095 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 8 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i008_015_e096_111 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 8 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i008_015_e112_127 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 8 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i008_015_e128_128 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)

private theorem cpu_loop_branchtaken_indices_016_023 (variant : Variant) (index : Fin 54)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 16 ≤ index.val) (indexStop : index.val < 24) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 16 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i016_023_e000_015 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 16 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i016_023_e016_031 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 16 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i016_023_e032_047 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 16 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i016_023_e048_063 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 16 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i016_023_e064_079 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 16 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i016_023_e080_095 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 16 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i016_023_e096_111 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 16 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i016_023_e112_127 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 16 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i016_023_e128_128 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)

private theorem cpu_loop_branchtaken_indices_024_031 (variant : Variant) (index : Fin 54)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 24 ≤ index.val) (indexStop : index.val < 32) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 24 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i024_031_e000_015 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 24 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i024_031_e016_031 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 24 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i024_031_e032_047 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 24 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i024_031_e048_063 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 24 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i024_031_e064_079 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 24 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i024_031_e080_095 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 24 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i024_031_e096_111 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 24 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i024_031_e112_127 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 24 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i024_031_e128_128 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)

private theorem cpu_loop_branchtaken_indices_032_039 (variant : Variant) (index : Fin 54)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 32 ≤ index.val) (indexStop : index.val < 40) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 32 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i032_039_e000_015 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 32 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i032_039_e016_031 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 32 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i032_039_e032_047 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 32 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i032_039_e048_063 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 32 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i032_039_e064_079 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 32 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i032_039_e080_095 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 32 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i032_039_e096_111 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 32 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i032_039_e112_127 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 32 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i032_039_e128_128 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)

private theorem cpu_loop_branchtaken_indices_040_047 (variant : Variant) (index : Fin 54)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 40 ≤ index.val) (indexStop : index.val < 48) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 40 8 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i040_047_e000_015 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 40 8 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i040_047_e016_031 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 40 8 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i040_047_e032_047 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 40 8 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i040_047_e048_063 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 40 8 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i040_047_e064_079 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 40 8 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i040_047_e080_095 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 40 8 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i040_047_e096_111 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 40 8 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i040_047_e112_127 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 40 8 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i040_047_e128_128 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)

private theorem cpu_loop_branchtaken_indices_048_053 (variant : Variant) (index : Fin 54)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat)
    (indexStart : 48 ≤ index.val) (indexStop : index.val < 54) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3))) = 0 := by
  by_cases piece0 : equation < 16
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 48 6 0 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i048_053_e000_015 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece16 : equation < 32
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 48 6 16 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i048_053_e016_031 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece32 : equation < 48
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 48 6 32 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i048_053_e032_047 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece48 : equation < 64
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 48 6 48 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i048_053_e048_063 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece64 : equation < 80
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 48 6 64 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i048_053_e064_079 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece80 : equation < 96
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 48 6 80 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i048_053_e080_095 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece96 : equation < 112
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 48 6 96 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i048_053_e096_111 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  by_cases piece112 : equation < 128
  · exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 48 6 112 16 equation
      indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i048_053_e112_127 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)
  exact g_cpu_projected_loop_equation_of_batch (fun index : Fin 54 => gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3) variant index setup 48 6 128 1 equation
    indexStart (by omega) (by omega) (by omega) bound cpu_loop_branchtaken_checked_i048_053_e128_128 (g_cpu_branch_ordinary variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)

theorem cpu_loop_branch_taken_equation (variant : Variant) (index : Fin 54)
    (setup : Table (ZMod babyBearModulus) (fields 10)) (equation : Nat) (bound : equation < 129) :
    ((gCpuPolynomials setup)[equation]'(by
      rw [g_cpu_polynomial_count]; exact bound)).eval
        (Verification.environment (machineAssignment variant (gapRow ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩ 3))) = 0 := by
  by_cases chunk0 : index.val < 8
  · exact cpu_loop_branchtaken_indices_000_007 variant index setup equation (by omega) chunk0 bound
  by_cases chunk8 : index.val < 16
  · exact cpu_loop_branchtaken_indices_008_015 variant index setup equation (by omega) chunk8 bound
  by_cases chunk16 : index.val < 24
  · exact cpu_loop_branchtaken_indices_016_023 variant index setup equation (by omega) chunk16 bound
  by_cases chunk24 : index.val < 32
  · exact cpu_loop_branchtaken_indices_024_031 variant index setup equation (by omega) chunk24 bound
  by_cases chunk32 : index.val < 40
  · exact cpu_loop_branchtaken_indices_032_039 variant index setup equation (by omega) chunk32 bound
  by_cases chunk40 : index.val < 48
  · exact cpu_loop_branchtaken_indices_040_047 variant index setup equation (by omega) chunk40 bound
  exact cpu_loop_branchtaken_indices_048_053 variant index setup equation (by omega) index.isLt bound

end Tests.PathGLoopNative
