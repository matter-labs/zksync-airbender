import Airbender.Proofs.ReducedMachine.NativeRuntimePool

namespace Airbender.NativeRuntimeQueryTransportProofs
open Airbender.ReducedMachine NativePoolProofs NativeRuntimePoolProofs
abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Interval metadata only; stored rows stay unchanged. -/
private def start : NativePoolProofs.Region → Nat
  | .zero => 0 | .xor => 1 | .or => 65537 | .and => 131073 | .sign => 196609
  | .cleanup => 262145 | .memoryOffset => 327681 | .signFill => 393217 | .conditional => 393345
  | .separator => 393473 | .rom => 459009 | .csr => 1507585 | .shift => 1511681 | .truncate => 5705985

private def size : NativePoolProofs.Region → Nat
  | .zero => 1 | .xor | .or | .and | .sign | .cleanup | .memoryOffset | .separator | .truncate => 65536
  | .signFill | .conditional => 128 | .rom => 1048576 | .csr => 4096 | .shift => 4194304
private theorem data_length (region : NativePoolProofs.Region) : region.data.length = size region := by
  cases region <;> rfl

private theorem fits (region : NativePoolProofs.Region) (i : Fin region.data.length) :
    start region+i.val < 5771521 := by
  have bound : i.val < size region := by simpa only [data_length] using i.isLt
  cases region <;> dsimp [start,size] at *
  all_goals omega

private theorem index_same {A : Type} {n : Nat} (f : Fin n → A) (a b : Fin n)
    (same : a.val = b.val) : f a = f b := congrArg f (Fin.ext same)

private theorem row_zero (i : Fin 1) :
    NativeFixed.rowNat ⟨0+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT0.rowNat i := by
  have bound := i.isLt
  have h0 : 0+i.val < 1 := by omega
  rw [NativeFixed.rowNat,dif_pos h0]
  exact index_same NativeFixed.dataT0.rowNat _ _ (show 0+i.val-0 = i.val by omega)

private theorem row_xor (i : Fin 65536) :
    NativeFixed.rowNat ⟨1+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT4.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 1+i.val < 1 := by omega
  have h1 : 1+i.val < 65537 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_pos h1]
  exact index_same NativeFixed.dataT4.rowNat _ _ (show 1+i.val-1 = i.val by omega)

private theorem row_or (i : Fin 65536) :
    NativeFixed.rowNat ⟨65537+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT6.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 65537+i.val < 1 := by omega
  have h1 : ¬ 65537+i.val < 65537 := by omega
  have h2 : 65537+i.val < 131073 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_pos h2]
  exact index_same NativeFixed.dataT6.rowNat _ _ (show 65537+i.val-65537 = i.val by omega)

private theorem row_and (i : Fin 65536) :
    NativeFixed.rowNat ⟨131073+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT7.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 131073+i.val < 1 := by omega
  have h1 : ¬ 131073+i.val < 65537 := by omega
  have h2 : ¬ 131073+i.val < 131073 := by omega
  have h3 : 131073+i.val < 196609 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_pos h3]
  exact index_same NativeFixed.dataT7.rowNat _ _ (show 131073+i.val-131073 = i.val by omega)

private theorem row_sign (i : Fin 65536) :
    NativeFixed.rowNat ⟨196609+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT16.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 196609+i.val < 1 := by omega
  have h1 : ¬ 196609+i.val < 65537 := by omega
  have h2 : ¬ 196609+i.val < 131073 := by omega
  have h3 : ¬ 196609+i.val < 196609 := by omega
  have h4 : 196609+i.val < 262145 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_pos h4]
  exact index_same NativeFixed.dataT16.rowNat _ _ (show 196609+i.val-196609 = i.val by omega)

private theorem row_cleanup (i : Fin 65536) :
    NativeFixed.rowNat ⟨262145+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT17.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 262145+i.val < 1 := by omega
  have h1 : ¬ 262145+i.val < 65537 := by omega
  have h2 : ¬ 262145+i.val < 131073 := by omega
  have h3 : ¬ 262145+i.val < 196609 := by omega
  have h4 : ¬ 262145+i.val < 262145 := by omega
  have h5 : 262145+i.val < 327681 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_pos h5]
  exact index_same NativeFixed.dataT17.rowNat _ _ (show 262145+i.val-262145 = i.val by omega)

private theorem row_memoryOffset (i : Fin 65536) :
    NativeFixed.rowNat ⟨327681+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT18.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 327681+i.val < 1 := by omega
  have h1 : ¬ 327681+i.val < 65537 := by omega
  have h2 : ¬ 327681+i.val < 131073 := by omega
  have h3 : ¬ 327681+i.val < 196609 := by omega
  have h4 : ¬ 327681+i.val < 262145 := by omega
  have h5 : ¬ 327681+i.val < 327681 := by omega
  have h6 : 327681+i.val < 393217 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_pos h6]
  exact index_same NativeFixed.dataT18.rowNat _ _ (show 327681+i.val-327681 = i.val by omega)

private theorem row_signFill (i : Fin 128) :
    NativeFixed.rowNat ⟨393217+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT20.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 393217+i.val < 1 := by omega
  have h1 : ¬ 393217+i.val < 65537 := by omega
  have h2 : ¬ 393217+i.val < 131073 := by omega
  have h3 : ¬ 393217+i.val < 196609 := by omega
  have h4 : ¬ 393217+i.val < 262145 := by omega
  have h5 : ¬ 393217+i.val < 327681 := by omega
  have h6 : ¬ 393217+i.val < 393217 := by omega
  have h7 : 393217+i.val < 393345 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_pos h7]
  exact index_same NativeFixed.dataT20.rowNat _ _ (show 393217+i.val-393217 = i.val by omega)

private theorem row_conditional (i : Fin 128) :
    NativeFixed.rowNat ⟨393345+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT22.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 393345+i.val < 1 := by omega
  have h1 : ¬ 393345+i.val < 65537 := by omega
  have h2 : ¬ 393345+i.val < 131073 := by omega
  have h3 : ¬ 393345+i.val < 196609 := by omega
  have h4 : ¬ 393345+i.val < 262145 := by omega
  have h5 : ¬ 393345+i.val < 327681 := by omega
  have h6 : ¬ 393345+i.val < 393217 := by omega
  have h7 : ¬ 393345+i.val < 393345 := by omega
  have h8 : 393345+i.val < 393473 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_pos h8]
  exact index_same NativeFixed.dataT22.rowNat _ _ (show 393345+i.val-393345 = i.val by omega)

private theorem row_separator (i : Fin 65536) :
    NativeFixed.rowNat ⟨393473+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT23.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 393473+i.val < 1 := by omega
  have h1 : ¬ 393473+i.val < 65537 := by omega
  have h2 : ¬ 393473+i.val < 131073 := by omega
  have h3 : ¬ 393473+i.val < 196609 := by omega
  have h4 : ¬ 393473+i.val < 262145 := by omega
  have h5 : ¬ 393473+i.val < 327681 := by omega
  have h6 : ¬ 393473+i.val < 393217 := by omega
  have h7 : ¬ 393473+i.val < 393345 := by omega
  have h8 : ¬ 393473+i.val < 393473 := by omega
  have h9 : 393473+i.val < 459009 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_pos h9]
  exact index_same NativeFixed.dataT23.rowNat _ _ (show 393473+i.val-393473 = i.val by omega)

private theorem row_rom (i : Fin 1048576) :
    NativeFixed.rowNat ⟨459009+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT24.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 459009+i.val < 1 := by omega
  have h1 : ¬ 459009+i.val < 65537 := by omega
  have h2 : ¬ 459009+i.val < 131073 := by omega
  have h3 : ¬ 459009+i.val < 196609 := by omega
  have h4 : ¬ 459009+i.val < 262145 := by omega
  have h5 : ¬ 459009+i.val < 327681 := by omega
  have h6 : ¬ 459009+i.val < 393217 := by omega
  have h7 : ¬ 459009+i.val < 393345 := by omega
  have h8 : ¬ 459009+i.val < 393473 := by omega
  have h9 : ¬ 459009+i.val < 459009 := by omega
  have h10 : 459009+i.val < 1507585 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_neg h9,dif_pos h10]
  exact index_same NativeFixed.dataT24.rowNat _ _ (show 459009+i.val-459009 = i.val by omega)

private theorem row_csr (i : Fin 4096) :
    NativeFixed.rowNat ⟨1507585+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT25.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 1507585+i.val < 1 := by omega
  have h1 : ¬ 1507585+i.val < 65537 := by omega
  have h2 : ¬ 1507585+i.val < 131073 := by omega
  have h3 : ¬ 1507585+i.val < 196609 := by omega
  have h4 : ¬ 1507585+i.val < 262145 := by omega
  have h5 : ¬ 1507585+i.val < 327681 := by omega
  have h6 : ¬ 1507585+i.val < 393217 := by omega
  have h7 : ¬ 1507585+i.val < 393345 := by omega
  have h8 : ¬ 1507585+i.val < 393473 := by omega
  have h9 : ¬ 1507585+i.val < 459009 := by omega
  have h10 : ¬ 1507585+i.val < 1507585 := by omega
  have h11 : 1507585+i.val < 1511681 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_neg h9,dif_neg h10,dif_pos h11]
  exact index_same NativeFixed.dataT25.rowNat _ _ (show 1507585+i.val-1507585 = i.val by omega)

private theorem row_shift (i : Fin 4194304) :
    NativeFixed.rowNat ⟨1511681+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT37.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 1511681+i.val < 1 := by omega
  have h1 : ¬ 1511681+i.val < 65537 := by omega
  have h2 : ¬ 1511681+i.val < 131073 := by omega
  have h3 : ¬ 1511681+i.val < 196609 := by omega
  have h4 : ¬ 1511681+i.val < 262145 := by omega
  have h5 : ¬ 1511681+i.val < 327681 := by omega
  have h6 : ¬ 1511681+i.val < 393217 := by omega
  have h7 : ¬ 1511681+i.val < 393345 := by omega
  have h8 : ¬ 1511681+i.val < 393473 := by omega
  have h9 : ¬ 1511681+i.val < 459009 := by omega
  have h10 : ¬ 1511681+i.val < 1507585 := by omega
  have h11 : ¬ 1511681+i.val < 1511681 := by omega
  have h12 : 1511681+i.val < 5705985 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_neg h9,dif_neg h10,dif_neg h11,dif_pos h12]
  exact index_same NativeFixed.dataT37.rowNat _ _ (show 1511681+i.val-1511681 = i.val by omega)

private theorem row_truncate (i : Fin 65536) :
    NativeFixed.rowNat ⟨5705985+i.val,by have := i.isLt; omega⟩ = NativeFixed.dataT47.rowNat i := by
  have bound := i.isLt
  have h0 : ¬ 5705985+i.val < 1 := by omega
  have h1 : ¬ 5705985+i.val < 65537 := by omega
  have h2 : ¬ 5705985+i.val < 131073 := by omega
  have h3 : ¬ 5705985+i.val < 196609 := by omega
  have h4 : ¬ 5705985+i.val < 262145 := by omega
  have h5 : ¬ 5705985+i.val < 327681 := by omega
  have h6 : ¬ 5705985+i.val < 393217 := by omega
  have h7 : ¬ 5705985+i.val < 393345 := by omega
  have h8 : ¬ 5705985+i.val < 393473 := by omega
  have h9 : ¬ 5705985+i.val < 459009 := by omega
  have h10 : ¬ 5705985+i.val < 1507585 := by omega
  have h11 : ¬ 5705985+i.val < 1511681 := by omega
  have h12 : ¬ 5705985+i.val < 5705985 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_neg h9,dif_neg h10,dif_neg h11,dif_neg h12]
  exact index_same NativeFixed.dataT47.rowNat _ _ (show 5705985+i.val-5705985 = i.val by omega)

private theorem row_nat (region : NativePoolProofs.Region) (i : Fin region.data.length) :
    NativeFixed.rowNat ⟨start region+i.val,fits region i⟩ = region.data.rowNat i := by
  cases region with
  | zero => exact row_zero i
  | xor => exact row_xor i
  | or => exact row_or i
  | and => exact row_and i
  | sign => exact row_sign i
  | cleanup => exact row_cleanup i
  | memoryOffset => exact row_memoryOffset i
  | signFill => exact row_signFill i
  | conditional => exact row_conditional i
  | separator => exact row_separator i
  | rom => exact row_rom i
  | csr => exact row_csr i
  | shift => exact row_shift i
  | truncate => exact row_truncate i

private theorem fixed_region (region : NativePoolProofs.Region) (i : Fin region.data.length) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] (region.data.row i) := by
  refine ⟨⟨start region+i.val,fits region i⟩,?_⟩
  change region.data.row i = (NativeFixed.rowNat _).map Nat.cast
  rw [row_nat]
  rfl

/-- Exact unchanged stored regions derive this restricted query result.
    Tag25 is deliberately excluded; no whole-table or BODY equivalence follows. -/
theorem outside_csr (query : Vector F 4)
    (accepted : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] query)
    (other : query[3] ≠ 25) : (NativeFixed.table (p := mersenne31Modulus)).Contains #[] query := by
  obtain ⟨region,i,same⟩ := NativeRuntimePoolProofs.member_region query accepted
  have noncsr : region ≠ .csr := by
    intro eq
    subst region
    have tag := NativeRuntimePoolProofs.region_row_tag .csr i
    apply other
    rw [same,tag]
    rfl
  rw [same]
  cases region with
  | zero => exact fixed_region .zero i
  | xor => exact fixed_region .xor i
  | or => exact fixed_region .or i
  | and => exact fixed_region .and i
  | sign => exact fixed_region .sign i
  | cleanup => exact fixed_region .cleanup i
  | memoryOffset => exact fixed_region .memoryOffset i
  | signFill => exact fixed_region .signFill i
  | conditional => exact fixed_region .conditional i
  | separator => exact fixed_region .separator i
  | rom => exact fixed_region .rom i
  | csr => exact False.elim (noncsr rfl)
  | shift => exact fixed_region .shift i
  | truncate => exact fixed_region .truncate i
end Airbender.NativeRuntimeQueryTransportProofs
