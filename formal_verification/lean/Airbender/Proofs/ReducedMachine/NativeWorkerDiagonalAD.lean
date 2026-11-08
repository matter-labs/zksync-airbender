import Airbender.Review.Circuits.Blake2Worker.DiagonalAD
import Airbender.Proofs.ReducedMachine.NativeWorkerDiagonalCB

namespace Airbender.NativeWorkerDiagonalADProofs
open Airbender.Verification Airbender.NativeWorkerDiagonalAD Airbender.NativeWorkerInitial Airbender.NativeWorkerSchedule
open Airbender.Blake2Worker.Native
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
@[simp] private theorem coefficient : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient_one : (2147483648 : F) = 1 := by decide +kernel
@[simp] private theorem coefficient_two : (4294967296 : F) = 2 := by decide +kernel
@[simp] private theorem scale256 : (549755813888 : F) = 256 := by decide +kernel
@[simp] private theorem scale16 : (34359738368 : F) = 16 := by decide +kernel
@[simp] private theorem scale128 : (274877906688 : F) = -128 := by decide +kernel
@[simp] private theorem scale512 : (1099511627776 : F) = 512 := by decide +kernel
private def sourceExpressions : Vector (Vector (Expression F) 3) 16 := #v[
#v[(.var ⟨460⟩),(.var ⟨482⟩),(.var ⟨484⟩)],
#v[(.var ⟨461⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨155⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨171⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨236⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨238⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨252⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨254⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨290⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨293⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨294⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨296⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨297⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨357⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨358⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨452⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨453⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨472⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨475⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨476⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨478⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨479⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨482⟩))),(.var ⟨485⟩)],
#v[(.var ⟨458⟩),(.var ⟨483⟩),(.var ⟨486⟩)],
#v[(.var ⟨459⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨157⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨173⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨237⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨239⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨253⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨255⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨270⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨271⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨288⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨289⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨295⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨296⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨297⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨298⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨299⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨356⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨359⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨452⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨453⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨454⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨455⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨470⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨471⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨477⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨478⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨479⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨480⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨481⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨483⟩))),(.var ⟨487⟩)],
#v[(.var ⟨504⟩),(.var ⟨526⟩),(.var ⟨528⟩)],
#v[(.var ⟨505⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨159⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨175⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨240⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨242⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨256⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨258⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨336⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨339⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨340⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨342⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨343⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨403⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨404⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨496⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨497⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨516⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨519⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨520⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨522⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨523⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨526⟩))),(.var ⟨529⟩)],
#v[(.var ⟨502⟩),(.var ⟨527⟩),(.var ⟨530⟩)],
#v[(.var ⟨503⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨161⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨177⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨241⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨243⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨257⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨259⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨316⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨317⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨334⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨335⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨341⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨342⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨343⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨344⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨345⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨402⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨405⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨496⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨497⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨498⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨499⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨514⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨515⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨521⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨522⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨523⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨524⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨525⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨527⟩))),(.var ⟨531⟩)],
#v[(.var ⟨548⟩),(.var ⟨570⟩),(.var ⟨572⟩)],
#v[(.var ⟨549⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨163⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨179⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨244⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨246⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨260⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨262⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨382⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨385⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨386⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨388⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨389⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨449⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨450⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨540⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨541⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨560⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨563⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨564⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨566⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨567⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨570⟩))),(.var ⟨573⟩)],
#v[(.var ⟨546⟩),(.var ⟨571⟩),(.var ⟨574⟩)],
#v[(.var ⟨547⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨165⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨181⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨245⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨247⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨261⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨263⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨362⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨363⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨380⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨381⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨387⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨388⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨389⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨390⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨391⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨448⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨451⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨540⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨541⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨542⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨543⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨558⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨559⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨565⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨566⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨567⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨568⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨569⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨571⟩))),(.var ⟨575⟩)],
#v[(.var ⟨592⟩),(.var ⟨614⟩),(.var ⟨616⟩)],
#v[(.var ⟨593⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨167⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨183⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨248⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨250⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨264⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨266⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨311⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨312⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨428⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨431⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨432⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨434⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨435⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨584⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨585⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨604⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨607⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨608⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨610⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨611⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨614⟩))),(.var ⟨617⟩)],
#v[(.var ⟨590⟩),(.var ⟨615⟩),(.var ⟨618⟩)],
#v[(.var ⟨591⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨169⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨185⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨249⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨251⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨265⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨267⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨310⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨313⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨408⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨409⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨426⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨427⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨433⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨434⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨435⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨436⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨437⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨584⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨585⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨586⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨587⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨602⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨603⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨609⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨610⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨611⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨612⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨613⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨615⟩))),(.var ⟨619⟩)]]

/-- Exact actual query syntax is bound BEFORE witness evaluation. -/
private theorem shape (diagonal : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (fixedExpressions ⟨82+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[(⟨entry.val,by have := entry.isLt; omega⟩ : Fin 4)] =
    sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][entry] := by
  fin_cases diagonal <;> fin_cases piece <;> fin_cases entry <;> rfl
private theorem value (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (query w diagonal piece)[entry.val]'(by have := entry.isLt; omega) =
    Expression.eval (environment w) sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][entry] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece entry)

private theorem value0 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[0] = Expression.eval (environment w)
      sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][0] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 0)

private theorem value1 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[1] = Expression.eval (environment w)
      sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][1] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 1)

private theorem value2 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[2] = Expression.eval (environment w)
      sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][2] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 2)

private theorem sum_reconstruction (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) :
    sumLimb w diagonal limb = (query w diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩)[1] +
      256*(query w diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[1] := by
  rw [value1 w diagonal _,value1 w diagonal _]
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [sumLimb,bInput,carry,Airbender.NativeWorkerDiagonalFirst.sumLimb,Airbender.NativeWorkerDiagonalFirst.carry,Airbender.NativeWorkerDiagonalFirst.inputLimb,
      Airbender.NativeWorkerDiagonalFirst.columnLimb,Airbender.NativeWorkerDiagonalFirst.sourceColumn,Airbender.NativeWorkerDiagonalFirst.bLimb,
      Airbender.NativeWorkerSecondAD.sumLimb,Airbender.NativeWorkerSecondAD.bInput,Airbender.NativeWorkerSecondAD.carry,
      Airbender.NativeWorkerFirstG.sumLimb,Airbender.NativeWorkerFirstG.carry,observed,initialColumns,selected,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
private theorem d_reconstruction (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) :
    dInput w diagonal limb = (query w diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩)[0] +
      256*(query w diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[0] := by
  rw [value0 w diagonal _,value0 w diagonal _]
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [dInput,Airbender.NativeWorkerDiagonalCB.dLimb,Airbender.NativeWorkerDiagonalCB.dByte,sourceExpressions,Expression.eval,environment]
private theorem block1 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock1 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock1 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup) := List.sublist_append_right _ _
  exact (((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private def booleanSyntax (column : Nat) : Expression F :=
  .add (.add (.const 0) (.add (.add (.const 0) (.const 0))
    (.mul (.mul (.const 1) (.const (-1))) (.var ⟨column⟩))))
    (.mul (.mul (.mul (.const 1) (.const 1)) (.var ⟨column⟩)) (.var ⟨column⟩))
private theorem bit_shape (setup : Table F (fields 4)) (diagonal : Fin 4) (slot : Fin 4) :
    (FlatOperation.constraints (constraintsBlock1 setup)).get
      ⟨3+12*diagonal.val+slot.val,by change 3+12*diagonal.val+slot.val < 64; have := diagonal.isLt; have := slot.isLt; omega⟩ =
      booleanSyntax (478+44*diagonal.val+slot.val) := by
  fin_cases diagonal <;> fin_cases slot <;> rfl

theorem carry_bits {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (diagonal : Fin 4) (slot : Fin 4) : (carryBit w diagonal slot).val ≤ 1 := by
  have bit := assertion_of_holds (block1 holds)
    ⟨3+12*diagonal.val+slot.val,by change 3+12*diagonal.val+slot.val < 64; have := diagonal.isLt; have := slot.isLt; omega⟩
  rw [bit_shape] at bit
  simp [booleanSyntax,Expression.eval,environment] at bit
  obtain ⟨n,bound,same⟩ := Airbender.Arithmetic.boolean_nat (by linear_combination bit)
  change (w (478+44*diagonal.val+slot.val)).val ≤ 1
  rw [same]
  simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

private theorem byte_effects {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[0].val < 256 ∧ (query w diagonal piece)[1].val < 256 ∧
    (query w diagonal piece)[2].val < 256 ∧
    (query w diagonal piece)[2].val = (query w diagonal piece)[0].val ^^^ (query w diagonal piece)[1].val := by
  let slot : Fin 208 := ⟨82+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩
  have kind : fixedKind slot = .byte := by
    dsimp only [slot]
    fin_cases diagonal <;> fin_cases piece <;> norm_num [fixedKind]
  exact ⟨by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.leftBounds slot,
    by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.rightBounds slot,
    by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.outputBounds slot,
    effects.results slot⟩

private theorem output_value (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[2] = w (484+44*diagonal.val+piece.val) := by
  rw [value2 w diagonal piece]
  fin_cases diagonal <;> fin_cases piece <;> simp [sourceExpressions,Expression.eval,environment]

theorem limb_bounds {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (sumLimb w diagonal limb).val < 65536 ∧ (dInput w diagonal limb).val < 65536 := by
  have low := byte_effects effects diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩
  have high := byte_effects effects diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  constructor
  · rw [sum_reconstruction]
    exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 256 (by omega)
  · rw [d_reconstruction]
    exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 256 (by omega)

private theorem xor_bytes (a b c d : BitVec 8) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem xor_halves (a b c d : BitVec 16) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append

private theorem half_xor {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (BitVec.ofNat 16 (dInput w diagonal limb).val ^^^ BitVec.ofNat 16 (sumLimb w diagonal limb).val) =
    BitVec.append (byte w diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩)
      (byte w diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩) := by
  let low : Fin 4 := ⟨2*limb.val,by have := limb.isLt; omega⟩
  let high : Fin 4 := ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  have l := byte_effects effects diagonal low
  have h := byte_effects effects diagonal high
  have d := Airbender.NativeWorkerFirstGProofs.pair_bytes (dInput w diagonal limb) _ _ l.1 h.1 (d_reconstruction w diagonal limb)
  have a := Airbender.NativeWorkerFirstGProofs.pair_bytes (sumLimb w diagonal limb) _ _ l.2.1 h.2.1 (sum_reconstruction w diagonal limb)
  have out0 := Airbender.NativeWorkerFirstGProofs.byte_xor _ _ _ l.1 l.2.1 l.2.2.1 l.2.2.2
  have out1 := Airbender.NativeWorkerFirstGProofs.byte_xor _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2
  rw [output_value] at out0 out1
  rw [d,a,xor_bytes,← out0,← out1]
  rfl

theorem rotated {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) :
    dAfter w diagonal = (Airbender.NativeWorkerFirstG.pack (dInput w diagonal 0) (dInput w diagonal 1) ^^^
      Airbender.NativeWorkerFirstG.pack (sumLimb w diagonal 0) (sumLimb w diagonal 1)).rotateRight 8 := by
  unfold dAfter Airbender.NativeWorkerFirstG.pack
  rw [xor_halves,half_xor effects,half_xor effects,← Airbender.NativeWorkerSecondADProofs.rotate8]
  rfl



/-- Specific original B-output syntax, bound before sampling any witness. -/
private theorem b_shape (diagonal : Fin 4) (limb : Fin 2) (piece : Fin 3) :
    (fixedExpressions ⟨76+18*diagonal.val+(3*limb.val+piece.val),by have := diagonal.isLt; have := limb.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[2] =
      .var ⟨470+44*diagonal.val+5*limb.val+piece.val⟩ := by
  fin_cases diagonal <;> fin_cases limb <;> fin_cases piece <;> rfl
private theorem b_output_bounds {w : Nat → F} (effects : LookupEffects w)
    (diagonal : Fin 4) (limb : Fin 2) (piece : Fin 3) :
    (w (470+44*diagonal.val+5*limb.val+piece.val)).val < (#v[8,512,16] : Vector Nat 3)[piece] := by
  let slot : Fin 208 := ⟨76+18*diagonal.val+(3*limb.val+piece.val),by have := diagonal.isLt; have := limb.isLt; have := piece.isLt; omega⟩
  have bound : (fixedKind slot).bound = (#v[8,512,16] : Vector Nat 3)[piece] := by
    dsimp only [slot]
    fin_cases diagonal <;> fin_cases limb <;> fin_cases piece <;> norm_num [fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound]
  have same : (fixedQuery w slot)[2] = w (470+44*diagonal.val+5*limb.val+piece.val) := by
    simpa [fixedQuery,slot,Expression.eval,environment] using congrArg (Expression.eval (environment w)) (b_shape diagonal limb piece)
  have h := effects.outputBounds slot
  rw [same,bound] at h
  exact h

theorem b_halves {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) :
    (bInput w diagonal 0).val < 65536 ∧ (bInput w diagonal 1).val < 65536 ∧
      Airbender.NativeWorkerFirstG.pack (bInput w diagonal 0) (bInput w diagonal 1) = Airbender.NativeWorkerDiagonalCB.bAfter w diagonal := by
  have l0 := b_output_bounds effects diagonal 0 0
  have l1 := b_output_bounds effects diagonal 0 1
  have l2 := b_output_bounds effects diagonal 0 2
  have h0 := b_output_bounds effects diagonal 1 0
  have h1 := b_output_bounds effects diagonal 1 1
  have h2 := b_output_bounds effects diagonal 1 2
  change (w (470+44*diagonal.val)).val < 8 at l0
  change (w (470+44*diagonal.val+1)).val < 512 at l1
  change (w (470+44*diagonal.val+2)).val < 16 at l2
  change (w (470+44*diagonal.val+5)).val < 8 at h0
  change (w (470+44*diagonal.val+6)).val < 512 at h1
  change (w (470+44*diagonal.val+7)).val < 16 at h2
  have c1 : 470+44*diagonal.val+1 = 471+44*diagonal.val := by omega
  have c2 : 470+44*diagonal.val+2 = 472+44*diagonal.val := by omega
  have c5 : 470+44*diagonal.val+5 = 475+44*diagonal.val := by omega
  have c6 : 470+44*diagonal.val+6 = 476+44*diagonal.val := by omega
  have c7 : 470+44*diagonal.val+7 = 477+44*diagonal.val := by omega
  rw [c1] at l1
  rw [c2] at l2
  rw [c5] at h0
  rw [c6] at h1
  rw [c7] at h2
  have low := Airbender.NativeWorkerSecondADProofs.rotated_half _ _ _ l2 h0 h1
  have high := Airbender.NativeWorkerSecondADProofs.rotated_half _ _ _ h2 l0 l1
  refine ⟨low.1,high.1,?_⟩
  change BitVec.append (BitVec.ofNat 16 (w (477+44*diagonal.val)+16*w (470+44*diagonal.val)+128*w (471+44*diagonal.val)).val)
    (BitVec.ofNat 16 (w (472+44*diagonal.val)+16*w (475+44*diagonal.val)+128*w (476+44*diagonal.val)).val) = _
  rw [low.2,high.2]
  simp only [Airbender.NativeWorkerDiagonalCB.bAfter,Airbender.NativeWorkerDiagonalCB.chunk9,
    Airbender.NativeWorkerDiagonalCB.chunk3,Airbender.NativeWorkerDiagonalCB.chunk4]
  have d6 : 471+44*diagonal.val+5 = 476+44*diagonal.val := by omega
  have d7 : 472+44*diagonal.val+5 = 477+44*diagonal.val := by omega
  change _ = BitVec.append
    (BitVec.append (BitVec.append (BitVec.ofNat 9 (w (471+44*diagonal.val)).val) (BitVec.ofNat 3 (w (470+44*diagonal.val)).val)) (BitVec.ofNat 4 (w (472+44*diagonal.val+5)).val))
    (BitVec.append (BitVec.append (BitVec.ofNat 9 (w (471+44*diagonal.val+5)).val) (BitVec.ofNat 3 (w (470+44*diagonal.val+5)).val)) (BitVec.ofNat 4 (w (472+44*diagonal.val)).val))
  rw [c5,d6,d7]

theorem mixing {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  exact ⟨carry_bits holds,limb_bounds effects,rotated effects⟩

theorem carry_bounds {w : Nat → F} (effects : LocalEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (carry w diagonal limb).val ≤ 3 := by
  have low := effects.carries diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩
  have high := effects.carries diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  dsimp [carryBit] at low high
  have high' : (w (479+44*diagonal.val+2*limb.val)).val ≤ 1 := by
    rw [show 479+44*diagonal.val+2*limb.val = 478+44*diagonal.val+(2*limb.val+1) by omega]
    exact high
  exact (Airbender.NativeWorkerAdditionProofs.carry_value _ _ low high').2

theorem addition {w : Nat → F} (prior : Airbender.NativeWorkerDiagonalCB.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (diagonal : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (sumLimb w diagonal 0) (sumLimb w diagonal 1) =
      Airbender.NativeWorkerDiagonalFirst.aAfter w diagonal + Airbender.NativeWorkerDiagonalCB.bAfter w diagonal +
        Airbender.NativeWorkerAddition.messageWord w ⟨9+2*diagonal.val,by have := diagonal.isLt; omega⟩ := by
  let m : Fin 16 := ⟨9+2*diagonal.val,by have := diagonal.isLt; omega⟩
  have ab (limb : Fin 2) := prior.prior.mixing.bounds diagonal limb
  have bb := b_halves effects diagonal
  have mb (limb : Fin 2) : (selected w m limb).val < 655360 := by
    rw [(prior.prior.prior.prior.prior.prior.selected m limb).1]
    exact (prior.prior.prior.prior.prior.prior.selected m limb).2
  have field (limb : Fin 2) :
      Airbender.NativeWorkerDiagonalFirst.sumLimb w diagonal limb + bInput w diagonal limb + selected w m limb +
        (if limb.val = 0 then 0 else carry w diagonal 0) = sumLimb w diagonal limb+65536*carry w diagonal limb := by
    dsimp [sumLimb,m]
    ring
  have low := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ _ (0 : F) _ _
    (ab 0) bb.1 (mb 0) (by decide +kernel) (carry_bounds localEffects diagonal 0)
    (localEffects.bounds diagonal 0).1 (by simpa using field 0)
  have high := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ _ _ _ _
    (ab 1) bb.2.1 (mb 1) (carry_bounds localEffects diagonal 0) (carry_bounds localEffects diagonal 1)
    (localEffects.bounds diagonal 1).1 (by simpa using field 1)
  simp only [ZMod.val_zero,Nat.add_zero] at low
  rw [← bb.2.2]
  change Airbender.NativeWorkerFirstG.pack (sumLimb w diagonal 0) (sumLimb w diagonal 1) =
    Airbender.NativeWorkerFirstG.pack (Airbender.NativeWorkerDiagonalFirst.sumLimb w diagonal 0) (Airbender.NativeWorkerDiagonalFirst.sumLimb w diagonal 1) +
      Airbender.NativeWorkerFirstG.pack (bInput w diagonal 0) (bInput w diagonal 1) + BitVec.ofNat 32 ((selected w m 0).val+65536*(selected w m 1).val)
  rw [Airbender.NativeWorkerAdditionProofs.pack_value _ _ (localEffects.bounds diagonal 0).1 (localEffects.bounds diagonal 1).1,
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (ab 0) (ab 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ bb.1 bb.2.1]
  exact Airbender.NativeWorkerAdditionProofs.wide_add _ _ _ _ _ _ _ _ _ _ low high

theorem chained_rotated {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) :
    dAfter w diagonal = (Airbender.NativeWorkerDiagonalFirst.dAfter w diagonal ^^^
      Airbender.NativeWorkerFirstG.pack (sumLimb w diagonal 0) (sumLimb w diagonal 1)).rotateRight 8 := by
  rw [← Airbender.NativeWorkerDiagonalCBProofs.d_pack effects diagonal]
  exact rotated effects diagonal

theorem row {w : Nat → F} (prior : Airbender.NativeWorkerDiagonalCB.RowEffects w)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerDiagonalAD.RowEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have localEffects := mixing holds
  refine ⟨prior,localEffects,?_,carry_bounds localEffects,chained_rotated effects,addition prior effects localEffects⟩
  intro diagonal limb
  have h := b_halves effects diagonal
  fin_cases limb
  · exact h.1
  · exact h.2.1
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary
theorem counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeMixedReplay.Effects batch workers inputs ∧
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerDiagonalAD.RowEffects w := by
  have prior := Airbender.NativeWorkerDiagonalCBProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior.1,fun w member => row (prior.2 w member) (processing w member).body⟩
end Airbender.NativeWorkerDiagonalADProofs
