import Airbender.Review.Circuits.ReducedMachine.WorkerWriteWords
import Airbender.Proofs.ReducedMachine.NativeWorkerWriteSlices

namespace Airbender.NativeWorkerWriteWordProofs
open Airbender.NativeWorkerWriteWords
open Airbender.NativeWorkerWriteSlices (WordBound PortEffect)
open Airbender.Blake2Worker.Native Airbender.Blake2Worker.QueryArtifact
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private theorem reconstruct256 {a b : F} (low : a.val < 256) (high : b.val < 256) :
    (a+256*b).val < 65536 := NativeWorkerWriteSliceProofs.reconstruct a b 256 (by omega)
private theorem reconstruct128 {a b : F} (low : a.val < 128) (high : b.val < 512) :
    (a+128*b).val < 65536 := NativeWorkerWriteSliceProofs.reconstruct a b 128 (by omega)

@[simp] private theorem coefficient_2147483647 : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient_34359738352 : (34359738352 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient_274877906816 : (274877906816 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient_4294967294 : (4294967294 : F) = 0 := by decide +kernel

private theorem block4 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock4 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock4 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup) := by
    exact List.sublist_append_right _ _
  exact ((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))


private def lowColumns : Vector Nat 16 := #v[482,483,526,527,570,571,614,615,578,579,622,623,490,491,534,535]
private def queryColumns : Vector Nat 16 := #v[82,84,100,102,118,120,136,138,122,124,140,142,86,88,104,106]
private def highExpressions : Vector (Expression F) 16 := #v[
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨155⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨171⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨236⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨238⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨252⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨254⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨290⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨293⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨294⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨296⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨297⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨357⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨358⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨452⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨453⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨472⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨475⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨476⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨478⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨479⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨482⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨157⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨173⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨237⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨239⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨253⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨255⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨270⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨271⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨288⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨289⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨295⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨296⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨297⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨298⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨299⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨356⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨359⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨452⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨453⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨454⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨455⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨470⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨471⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨477⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨478⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨479⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨480⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨481⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨483⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨159⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨175⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨240⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨242⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨256⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨258⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨336⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨339⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨340⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨342⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨343⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨403⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨404⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨496⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨497⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨516⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨519⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨520⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨522⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨523⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨526⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨161⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨177⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨241⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨243⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨257⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨259⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨316⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨317⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨334⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨335⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨341⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨342⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨343⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨344⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨345⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨402⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨405⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨496⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨497⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨498⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨499⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨514⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨515⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨521⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨522⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨523⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨524⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨525⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨527⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨163⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨179⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨244⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨246⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨260⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨262⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨382⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨385⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨386⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨388⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨389⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨449⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨450⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨540⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨541⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨560⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨563⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨564⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨566⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨567⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨570⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨165⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨181⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨245⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨247⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨261⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨263⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨362⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨363⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨380⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨381⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨387⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨388⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨389⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨390⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨391⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨448⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨451⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨540⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨541⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨542⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨543⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨558⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨559⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨565⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨566⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨567⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨568⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨569⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨571⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨167⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨183⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨248⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨250⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨264⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨266⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨311⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨312⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨428⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨431⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨432⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨434⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨435⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨584⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨585⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨604⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨607⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨608⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨610⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨611⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨614⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨169⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨185⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨249⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨251⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨265⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨267⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨310⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨313⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨408⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨409⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨426⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨427⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨433⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨434⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨435⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨436⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨437⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨584⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨585⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨586⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨587⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨602⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨603⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨609⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨610⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨611⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨612⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨613⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨615⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨186⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨278⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨279⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨303⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨304⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨306⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨548⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨549⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨550⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨573⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨574⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨576⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨578⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨187⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨275⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨276⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨281⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨302⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨305⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨306⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨307⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨546⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨547⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨550⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨551⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨572⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨575⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨576⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨577⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨579⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨188⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨324⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨325⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨349⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨350⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨352⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨592⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨593⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨594⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨617⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨618⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨620⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨622⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨189⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨321⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨322⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨327⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨348⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨351⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨352⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨353⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨590⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨591⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨594⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨595⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨616⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨619⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨620⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨621⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨623⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨190⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨370⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨371⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨395⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨396⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨398⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨460⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨461⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨462⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨485⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨486⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨488⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨490⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨191⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨367⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨368⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨373⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨394⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨397⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨398⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨399⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨458⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨459⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨462⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨463⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨484⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨487⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨488⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨489⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨491⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨192⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨416⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨417⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨441⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨442⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨444⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨504⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨505⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨506⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨529⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨530⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨532⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨534⟩))),
(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨193⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨413⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨414⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨419⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨440⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨443⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨444⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨445⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨502⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨503⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨506⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨507⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨528⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨531⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨532⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨533⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨535⟩)))]

private def lowQuery (limb : Fin 16) : Fin 208 :=
  ⟨queryColumns[limb],by fin_cases limb <;> decide +kernel⟩
private def highQuery (limb : Fin 16) : Fin 208 :=
  ⟨queryColumns[limb]+1,by fin_cases limb <;> decide +kernel⟩
private def writeColumn (limb : Fin 16) : Nat :=
  if limb.val < 8 then 38+4*(limb.val/2)+limb.val%2 else 70+4*((limb.val-8)/2)+limb.val%2
private theorem low_shape (limb : Fin 16) :
    (fixedExpressions (lowQuery limb) : Vector (Expression F) 4)[1] = .var ⟨lowColumns[limb]⟩ := by
  fin_cases limb <;> rfl
private theorem high_shape (limb : Fin 16) :
    (fixedExpressions (highQuery limb) : Vector (Expression F) 4)[1] = highExpressions[limb] := by
  fin_cases limb <;> rfl
private theorem low_value (w : Nat → F) (limb : Fin 16) :
    (fixedQuery w (lowQuery limb))[1] = w lowColumns[limb] := by
  simpa [fixedQuery,Expression.eval,environment] using
    congrArg (Expression.eval (environment w)) (low_shape limb)
private theorem high_value (w : Nat → F) (limb : Fin 16) :
    (fixedQuery w (highQuery limb))[1] = Expression.eval (environment w) highExpressions[limb] := by
  simpa [fixedQuery] using congrArg (Expression.eval (environment w)) (high_shape limb)

private theorem arithmetic_first {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (limb : Fin 8) :
    w (writeColumn (⟨limb.val,by have := limb.isLt; omega⟩ : Fin 16)) =
      w lowColumns[(⟨limb.val,by have := limb.isLt; omega⟩ : Fin 16)] +
      256*(fixedQuery w (highQuery (⟨limb.val,by have := limb.isLt; omega⟩ : Fin 16)))[1] := by
  have eq := assertion_of_holds (block4 holds)
    ⟨48+limb.val,by change 48+limb.val < 64; have := limb.isLt; omega⟩
  rw [high_value]
  fin_cases limb
  all_goals
    simp [writeColumn,lowColumns,highExpressions,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] at eq ⊢
    linear_combination (norm := skip) -eq
    ring_nf
    simp

private theorem arithmetic_second {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (limb : Fin 8) :
    w (writeColumn (⟨8+limb.val,by have := limb.isLt; omega⟩ : Fin 16)) =
      w lowColumns[(⟨8+limb.val,by have := limb.isLt; omega⟩ : Fin 16)] +
      128*(fixedQuery w (highQuery (⟨8+limb.val,by have := limb.isLt; omega⟩ : Fin 16)))[1] := by
  have eq := assertion_of_holds (Airbender.Blake2Worker.QueryProofs.block5 holds)
    ⟨limb.val,by change limb.val < 32; have := limb.isLt; omega⟩
  rw [high_value]
  fin_cases limb
  all_goals
    simp [writeColumn,lowColumns,highExpressions,constraintsBlock5,FlatOperation.constraints,Expression.eval,environment] at eq ⊢
    linear_combination (norm := skip) -eq
    ring_nf
    simp

private theorem first_bounds {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (limb : Fin 8) : (w (writeColumn (⟨limb.val,by have := limb.isLt; omega⟩ : Fin 16))).val < 65536 := by
  let index : Fin 16 := ⟨limb.val,by have := limb.isLt; omega⟩
  have lookups := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have low := lookups.rightBounds (lowQuery index)
  have high := lookups.rightBounds (highQuery index)
  rw [low_value] at low
  rw [arithmetic_first holds limb]
  fin_cases limb
  all_goals
    simp [index,lowQuery,highQuery,queryColumns,fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound] at low high ⊢
    exact reconstruct256 low high

private theorem second_bounds {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (limb : Fin 8) : (w (writeColumn (⟨8+limb.val,by have := limb.isLt; omega⟩ : Fin 16))).val < 65536 := by
  let index : Fin 16 := ⟨8+limb.val,by have := limb.isLt; omega⟩
  have lookups := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have low := lookups.rightBounds (lowQuery index)
  have high := lookups.rightBounds (highQuery index)
  rw [low_value] at low
  rw [arithmetic_second holds limb]
  fin_cases limb
  all_goals
    simp [index,lowQuery,highQuery,queryColumns,fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound] at low high ⊢
    exact reconstruct128 low high

theorem arithmetic_words {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (limb : Fin 16) : (w (writeColumn limb)).val < 65536 := by
  by_cases first : limb.val < 8
  · exact first_bounds holds ⟨limb.val,first⟩
  · have bounded := second_bounds holds ⟨limb.val-8,by have := limb.isLt; omega⟩
    have index : 8+(limb.val-8) = limb.val := by omega
    have same : (⟨8+(limb.val-8),by have := limb.isLt; omega⟩ : Fin 16) = limb := Fin.ext index
    simpa only [index,same] using bounded

private def arithmeticSlot (word : Fin 8) : Fin 43 :=
  ⟨if word.val < 4 then 9+word.val else 13+word.val,by have := word.isLt; split <;> omega⟩
private def pairLimb (word : Fin 8) (limb : Fin 2) : Fin 16 :=
  ⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩

/-- Pure actual descriptors are bound before witness maps. -/
private theorem arithmetic_columns (word : Fin 8) :
    (memoryAccess (arithmeticSlot word)).writeValue = some #v[
      writeColumn (pairLimb word 0),writeColumn (pairLimb word 1)] := by
  fin_cases word <;> decide +kernel
private theorem arithmetic_value (w : Nat → F) (word : Fin 8) (limb : Fin 2) :
    (keyValue w (arithmeticSlot word) true)[limb] = w (writeColumn (pairLimb word limb)) := by
  have columns := arithmetic_columns word
  fin_cases limb <;> simp [keyValue,columns]

theorem arithmetic_ports {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (word : Fin 8) : WordBound (keyValue w (arithmeticSlot word) true) := by
  intro limb
  rw [arithmetic_value]
  exact arithmetic_words holds (pairLimb word limb)

/-- Reuse the35 closed ports and add the eight arithmetic ports. Every actual
    port remains present; no input word bound, schedule or result is assumed. -/
theorem local_effects {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    LocalEffects w := by
  have slices := NativeWorkerWriteSliceProofs.local_effects holds
  refine ⟨slices,?_⟩
  intro slot
  by_cases covered : Airbender.NativeWorkerWriteSlices.Covered slot
  · exact slices.ports slot covered
  · left
    fin_cases slot <;> simp [Airbender.NativeWorkerWriteSlices.Covered] at covered
    · exact arithmetic_ports holds ⟨0,by decide +kernel⟩
    · exact arithmetic_ports holds ⟨1,by decide +kernel⟩
    · exact arithmetic_ports holds ⟨2,by decide +kernel⟩
    · exact arithmetic_ports holds ⟨3,by decide +kernel⟩
    · exact arithmetic_ports holds ⟨4,by decide +kernel⟩
    · exact arithmetic_ports holds ⟨5,by decide +kernel⟩
    · exact arithmetic_ports holds ⟨6,by decide +kernel⟩
    · exact arithmetic_ports holds ⟨7,by decide +kernel⟩

/-- Internal preservation rule for an eventual initialized induction. This is
    a consequence of bounded-or-copy, not a new acceptance/history premise. -/
theorem preserves {w : Nat → F} (effects : LocalEffects w)
    (reads : ∀ slot, WordBound (keyValue w slot false)) :
    ∀ slot, WordBound (keyValue w slot true) := by
  intro slot
  rcases effects.ports slot with bounded | copy
  · exact bounded
  · rw [copy]
    exact reads slot

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch inputs := by
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted
  exact ⟨NativeWorkerWriteSliceProofs.effects embed memory ch pc gamma config accepted identity,
    fun w member => local_effects (processing w member).body⟩

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩

end Airbender.NativeWorkerWriteWordProofs
