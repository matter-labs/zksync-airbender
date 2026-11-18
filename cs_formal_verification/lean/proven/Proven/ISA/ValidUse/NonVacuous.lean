module
public import Human.ISA.ValidUse.Theorems
public import Proven.KernelRfl
@[expose] public section
namespace RV.ValidUse.NonVacuous
open Spec
set_option warningAsError true
set_option maxRecDepth 65536

def snapshot (left right control : Word) (memory : Word → BitVec 8) : State where
  pc := 0
  regFile index := if index = 10 then left else if index = 11 then right else if index = 12 then control else 0
  rom _ := 0
  mem := memory

theorem bigint : BigintReferenceSatisfiableClaim := by
  refine ⟨snapshot 0x400000 0x400100 1 (fun _ => 0), ?_⟩
  unfold Bigint RAMBuffer BigintControl Buffer Apart
  decide +kernel

theorem g : GReferenceSatisfiableClaim := by
  refine ⟨false, snapshot 0x400000 0x400100 0 (fun _ => 0), 0x400000, 0x400100, ?_⟩
  unfold G BlakeGAssumptions Buffer Apart
  decide +kernel

theorem round : RoundReferenceSatisfiableClaim := by
  refine ⟨false, snapshot 0x400000 0x400100 0x80000
    (RV.write (fun _ => 0) 0x400058 (IV 6) 4), 0x400000, 0x400100, IV 4, false, ?_⟩
  unfold Round BlakeCompressAssumptions Buffer Apart
  decide +kernel

theorem hash : HashReferenceSatisfiableClaim := by
  refine ⟨false, false, snapshot 0x400000 0x400100 0xc0000 (fun _ => 0), 0x400000, 0x400100, ?_⟩
  unfold Hash BlakeHashAssumptions Buffer Apart
  decide +kernel

theorem keccak : SplitKeccakReferenceSatisfiableClaim := by
  refine ⟨snapshot 0 0x400000 0 (fun _ => 0), 0x400000, ?_⟩
  unfold Keccak KeccakAssumptions Buffer
  decide +kernel
end RV.ValidUse.NonVacuous
