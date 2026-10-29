import Airbender.Proofs.GKRProtocol.WindowedNative.UnifiedCachedFoundation
import Airbender.Proofs.GKRProtocol.BaseAffine

namespace Airbender.Compiler.WindowedNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem stepHolds0
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step0).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step0) (List.mem_cons_self)

theorem stepHolds1
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step1).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step1) (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem stepHolds2
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step2).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step2) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem stepHolds3
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step3).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step3) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))

theorem stepHolds4
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step4).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step4) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))

theorem stepHolds5
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step5).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step5) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))

theorem stepHolds6
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step6).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step6) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))

theorem stepHolds7
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step7).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step7) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))

theorem stepHolds8
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step8).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step8) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))

theorem stepHolds9
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step9).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step9) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))

theorem stepHolds10
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step10).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step10) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))

theorem stepHolds11
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step11).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step11) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))

theorem stepHolds12
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step12).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step12) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))

theorem stepHolds13
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step13).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step13) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))

theorem stepHolds14
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step14).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step14) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))

theorem stepHolds15
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step15).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step15) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))

theorem stepHolds16
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step16).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step16) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))

theorem stepHolds17
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step17).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step17) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))

theorem stepHolds18
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step18).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step18) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))

theorem stepHolds19
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    ((nativeGate0 publicTops).functional).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical ((nativeGate0 publicTops).functional) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))

theorem stepHolds20
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    ((nativeGate1 publicTops).functional).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical ((nativeGate1 publicTops).functional) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))

theorem stepHolds21
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step21).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step21) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))

theorem stepHolds22
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step22).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step22) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))

theorem stepHolds23
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step23).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step23) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))

theorem stepHolds24
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step24).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step24) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))

theorem stepHolds25
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step25).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step25) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))

theorem stepHolds26
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step26).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step26) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))

theorem stepHolds27
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step27).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step27) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))

theorem stepHolds28
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step28).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step28) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))

theorem stepHolds29
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step29).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step29) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))

theorem stepHolds30
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step30).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step30) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))

theorem stepHolds31
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step31).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step31) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))

theorem stepHolds32
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step32).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step32) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))

theorem stepHolds33
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step33).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step33) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))

theorem stepHolds34
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step34).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step34) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))

theorem stepHolds35
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step35).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step35) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))

theorem stepHolds36
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step36).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step36) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))

theorem stepHolds37
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step37).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step37) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))

theorem stepHolds38
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step38).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step38) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))

theorem stepHolds39
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step39).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step39) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))

theorem stepHolds40
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step40).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step40) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))

theorem stepHolds41
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step41).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step41) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds42
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step42).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step42) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds43
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step43).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step43) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds44
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step44).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step44) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds45
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step45).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step45) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds46
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step46).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step46) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds47
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step47).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step47) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds48
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step48).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step48) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds49
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step49).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step49) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds50
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step50).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step50) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds51
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step51).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step51) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds52
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step52).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step52) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds53
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step53).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step53) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds54
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step54).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step54) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds55
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step55).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step55) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds56
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step56).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step56) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds57
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step57).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step57) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds58
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step58).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step58) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds59
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step59).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step59) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds60
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step60).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step60) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds61
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step61).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step61) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds62
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step62).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step62) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds63
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step63).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step63) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds64
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step64).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step64) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds65
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step65).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedCached.native.step65) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem canonical_base
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) (address : GKRAddress) (role : Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase address = true) :
    canonical publicTops hom challenges gamma physical address = hom (physical address) := by
  change (if Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase address then _ else _) = _
  exact if_pos role

theorem lookupHolds0
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate0.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate0.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds21 publicTops hom challenges gamma physical)

theorem lookupHolds1
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate1.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate1.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds22 publicTops hom challenges gamma physical)

theorem lookupHolds2
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate2.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate2.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds23 publicTops hom challenges gamma physical)

theorem lookupHolds3
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate3.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate3.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds24 publicTops hom challenges gamma physical)

theorem lookupHolds4
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate4.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate4.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds25 publicTops hom challenges gamma physical)

theorem lookupHolds5
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate5.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate5.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds26 publicTops hom challenges gamma physical)

theorem lookupHolds6
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate6.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate6.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds27 publicTops hom challenges gamma physical)

theorem lookupHolds7
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate7.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate7.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds28 publicTops hom challenges gamma physical)

theorem lookupHolds8
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate8.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate8.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds29 publicTops hom challenges gamma physical)

theorem lookupHolds9
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate9.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate9.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds30 publicTops hom challenges gamma physical)

theorem lookupHolds10
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate10.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate10.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds31 publicTops hom challenges gamma physical)

theorem lookupHolds11
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate11.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate11.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds34 publicTops hom challenges gamma physical)

theorem lookupHolds12
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate12.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate12.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds35 publicTops hom challenges gamma physical)

theorem lookupHolds13
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate13.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate13.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds36 publicTops hom challenges gamma physical)

theorem lookupHolds14
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate14.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate14.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds37 publicTops hom challenges gamma physical)

theorem lookupHolds15
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate15.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate15.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds38 publicTops hom challenges gamma physical)

theorem lookupHolds16
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate16.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate16.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds39 publicTops hom challenges gamma physical)

theorem lookupHolds17
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate17.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate17.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds40 publicTops hom challenges gamma physical)

theorem lookupHolds18
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate18.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate18.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds41 publicTops hom challenges gamma physical)

theorem lookupHolds19
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate19.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate19.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds42 publicTops hom challenges gamma physical)

theorem lookupHolds20
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate20.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate20.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds43 publicTops hom challenges gamma physical)

theorem lookupHolds21
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate21.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate21.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds44 publicTops hom challenges gamma physical)

theorem lookupHolds22
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate22.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate22.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds45 publicTops hom challenges gamma physical)

theorem lookupHolds23
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate23.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate23.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds46 publicTops hom challenges gamma physical)

theorem lookupHolds24
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate24.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate24.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds49 publicTops hom challenges gamma physical)

theorem lookupHolds25
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate25.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate25.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds50 publicTops hom challenges gamma physical)

theorem lookupHolds26
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate26.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate26.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds51 publicTops hom challenges gamma physical)

theorem lookupHolds27
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate27.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate27.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds52 publicTops hom challenges gamma physical)

theorem lookupHolds28
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate28.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate28.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds53 publicTops hom challenges gamma physical)

theorem lookupHolds29
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate29.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate29.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds54 publicTops hom challenges gamma physical)

theorem lookupHolds30
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate30.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate30.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds55 publicTops hom challenges gamma physical)

theorem lookupHolds31
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate31.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate31.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds56 publicTops hom challenges gamma physical)

theorem lookupHolds32
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate32.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate32.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds57 publicTops hom challenges gamma physical)

theorem lookupHolds33
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate33.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate33.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds58 publicTops hom challenges gamma physical)

theorem lookupHolds34
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate34.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate34.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds59 publicTops hom challenges gamma physical)

theorem lookupHolds35
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate35.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate35.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds60 publicTops hom challenges gamma physical)

theorem lookupHolds36
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate36.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate36.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds61 publicTops hom challenges gamma physical)

theorem lookupHolds37
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate37.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate37.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds62 publicTops hom challenges gamma physical)

theorem lookupHolds38
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate38.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate38.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds63 publicTops hom challenges gamma physical)

theorem lookupHolds39
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate39.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate39.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds64 publicTops hom challenges gamma physical)

theorem lookupHolds40
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedCached.native.gate40.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedCached.native.gate40.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds65 publicTops hom challenges gamma physical)

theorem productHolds0
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate0.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedCached.native.gate0.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds15 publicTops hom challenges gamma physical)

theorem productHolds1
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate1.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedCached.native.gate1.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds16 publicTops hom challenges gamma physical)

theorem productHolds2
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate2.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedCached.native.gate2.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds17 publicTops hom challenges gamma physical)

theorem productHolds3
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate3.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedCached.native.gate3.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds18 publicTops hom challenges gamma physical)

theorem productHolds4
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (nativeGate0 publicTops).Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  (nativeGate0 publicTops).functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds19 publicTops hom challenges gamma physical)

theorem productHolds5
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (nativeGate1 publicTops).Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  (nativeGate1 publicTops).functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds20 publicTops hom challenges gamma physical)

theorem productHolds6
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate6.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedCached.native.gate6.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds32 publicTops hom challenges gamma physical)

theorem productHolds7
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate7.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedCached.native.gate7.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds33 publicTops hom challenges gamma physical)

theorem productHolds8
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate8.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds40 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds9
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate9.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds41 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds10
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate10.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds45 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds11
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate11.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds46 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds12
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate12.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedCached.native.gate12.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds47 publicTops hom challenges gamma physical)

theorem productHolds13
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate13.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedCached.native.gate13.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds48 publicTops hom challenges gamma physical)

theorem productHolds14
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate14.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds52 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds15
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate15.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds53 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds16
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate16.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds55 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds17
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate17.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds56 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds18
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate18.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds57 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds19
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate19.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds58 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds20
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate20.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds62 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds21
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate21.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds63 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds22
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate22.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds64 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds23
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedCached.native.gate23.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds65 publicTops hom challenges gamma physical) _ List.mem_cons_self

noncomputable def productGates (publicTops : Nat → Nat) : List NativeProductGate := [Airbender.Compiler.ProductNative.UnifiedCached.native.gate0, Airbender.Compiler.ProductNative.UnifiedCached.native.gate1, Airbender.Compiler.ProductNative.UnifiedCached.native.gate2, Airbender.Compiler.ProductNative.UnifiedCached.native.gate3, (nativeGate0 publicTops), (nativeGate1 publicTops), Airbender.Compiler.ProductNative.UnifiedCached.native.gate6, Airbender.Compiler.ProductNative.UnifiedCached.native.gate7, Airbender.Compiler.ProductNative.UnifiedCached.native.gate8, Airbender.Compiler.ProductNative.UnifiedCached.native.gate9, Airbender.Compiler.ProductNative.UnifiedCached.native.gate10, Airbender.Compiler.ProductNative.UnifiedCached.native.gate11, Airbender.Compiler.ProductNative.UnifiedCached.native.gate12, Airbender.Compiler.ProductNative.UnifiedCached.native.gate13, Airbender.Compiler.ProductNative.UnifiedCached.native.gate14, Airbender.Compiler.ProductNative.UnifiedCached.native.gate15, Airbender.Compiler.ProductNative.UnifiedCached.native.gate16, Airbender.Compiler.ProductNative.UnifiedCached.native.gate17, Airbender.Compiler.ProductNative.UnifiedCached.native.gate18, Airbender.Compiler.ProductNative.UnifiedCached.native.gate19, Airbender.Compiler.ProductNative.UnifiedCached.native.gate20, Airbender.Compiler.ProductNative.UnifiedCached.native.gate21, Airbender.Compiler.ProductNative.UnifiedCached.native.gate22, Airbender.Compiler.ProductNative.UnifiedCached.native.gate23]

theorem canonical_lookups
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    ∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedCached.native.gates, gate.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  PredicateChecks.all (PredicateChecks.cons (lookupHolds0 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds1 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds2 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds3 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds4 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds5 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds6 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds7 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds8 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds9 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds10 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds11 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds12 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds13 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds14 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds15 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds16 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds17 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds18 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds19 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds20 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds21 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds22 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds23 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds24 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds25 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds26 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds27 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds28 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds29 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds30 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds31 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds32 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds33 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds34 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds35 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds36 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds37 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds38 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds39 publicTops hom challenges gamma physical) (PredicateChecks.cons (lookupHolds40 publicTops hom challenges gamma physical) (PredicateChecks.nil))))))))))))))))))))))))))))))))))))))))))

theorem canonical_products
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    ∀ gate ∈ productGates publicTops, gate.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  PredicateChecks.all (PredicateChecks.cons (productHolds0 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds1 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds2 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds3 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds4 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds5 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds6 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds7 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds8 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds9 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds10 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds11 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds12 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds13 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds14 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds15 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds16 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds17 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds18 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds19 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds20 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds21 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds22 publicTops hom challenges gamma physical) (PredicateChecks.cons (productHolds23 publicTops hom challenges gamma physical) (PredicateChecks.nil)))))))))))))))))))))))))

theorem affineHolds0
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine0.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step0.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine0.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step0).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step0 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds0 publicTops hom challenges gamma physical)

theorem affineHolds1
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine1.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step1.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine1.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step1).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step1 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds1 publicTops hom challenges gamma physical)

theorem affineHolds2
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine2.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step2.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine2.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step2).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step2 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds2 publicTops hom challenges gamma physical)

theorem affineHolds3
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine3.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step3.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine3.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step3).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step3 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds3 publicTops hom challenges gamma physical)

theorem affineHolds4
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine4.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step4.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine4.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step4).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step4 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds4 publicTops hom challenges gamma physical)

theorem affineHolds5
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine5.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step5.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine5.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step5).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step5 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds5 publicTops hom challenges gamma physical)

theorem affineHolds6
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine6.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step6.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine6.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step6).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step6 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds6 publicTops hom challenges gamma physical)

theorem affineHolds7
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine7.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step7.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine7.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step7).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step7 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds7 publicTops hom challenges gamma physical)

theorem affineHolds8
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine8.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe0 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate0 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked0 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked0 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked0 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨0, by decide +kernel⟩))

theorem affineHolds9
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine9.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe1 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate1 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked1 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked1 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked1 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨1, by decide +kernel⟩))

theorem affineHolds10
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine10.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe2 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate2 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked2 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked2 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked2 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨2, by decide +kernel⟩))

theorem affineHolds11
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine11.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe3 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate3 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked3 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked3 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked3 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨3, by decide +kernel⟩))

theorem affineHolds12
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine12.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe4 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate4 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked4 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked4 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked4 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨4, by decide +kernel⟩))

theorem affineHolds13
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine13.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe5 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate5 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked5 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked5 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked5 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨5, by decide +kernel⟩))

theorem affineHolds14
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine14.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step8.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine14.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step8).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step8 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds8 publicTops hom challenges gamma physical)

theorem affineHolds15
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine15.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step9.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine15.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step9).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step9 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds9 publicTops hom challenges gamma physical)

theorem affineHolds16
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine16.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step10.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine16.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step10).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step10 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds10 publicTops hom challenges gamma physical)

theorem affineHolds17
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine17.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step11.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine17.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step11).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step11 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds11 publicTops hom challenges gamma physical)

theorem affineHolds18
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine18.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step12.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine18.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step12).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step12 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds12 publicTops hom challenges gamma physical)

theorem affineHolds19
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine19.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step13.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine19.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step13).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step13 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds13 publicTops hom challenges gamma physical)

theorem affineHolds20
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine20.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step14.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine20.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step14).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step14 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds14 publicTops hom challenges gamma physical)

theorem affineHolds21
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine21.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe6 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate6 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked6 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked6 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked6 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨6, by decide +kernel⟩))

theorem affineHolds22
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine22.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe7 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate48 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked7 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked7 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked48 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨48, by decide +kernel⟩))

theorem affineHolds23
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine23.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe8 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput8 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate49 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked8 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked8 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked49 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨49, by decide +kernel⟩))

theorem affineHolds24
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine24.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRecipe9 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseOutput9 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate129 Airbender.Compiler.FunctionalNative.UnifiedCached.native.basePortsChecked9 Airbender.Compiler.FunctionalNative.UnifiedCached.native.baseRelationChecked9 Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gateChecked129 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates ⟨129, by decide +kernel⟩))

theorem affineHolds25
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine25.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step40.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine25.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step40).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step40 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds40 publicTops hom challenges gamma physical)

theorem affineHolds26
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine26.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step41.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine26.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step41).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step41 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds41 publicTops hom challenges gamma physical)

theorem affineHolds27
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine27.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step45.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine27.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step45).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step45 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds45 publicTops hom challenges gamma physical)

theorem affineHolds28
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine28.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step46.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine28.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step46).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step46 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds46 publicTops hom challenges gamma physical)

theorem affineHolds29
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine29.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step52.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine29.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step52).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step52 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds52 publicTops hom challenges gamma physical)

theorem affineHolds30
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine30.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step53.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine30.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step53).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step53 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds53 publicTops hom challenges gamma physical)

theorem affineHolds31
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine31.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step55.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine31.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step55).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step55 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds55 publicTops hom challenges gamma physical)

theorem affineHolds32
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine32.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step56.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine32.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step56).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step56 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds56 publicTops hom challenges gamma physical)

theorem affineHolds33
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine33.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step57.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine33.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step57).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step57 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds57 publicTops hom challenges gamma physical)

theorem affineHolds34
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine34.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step58.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine34.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step58).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step58 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds58 publicTops hom challenges gamma physical)

theorem affineHolds35
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine35.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step62.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine35.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step62).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step62 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds62 publicTops hom challenges gamma physical)

theorem affineHolds36
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine36.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step63.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine36.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step63).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step63 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds63 publicTops hom challenges gamma physical)

theorem affineHolds37
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine37.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step64.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine37.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step64).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step64 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds64 publicTops hom challenges gamma physical)

theorem affineHolds38
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine38.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedCached.native.step65.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedCached.native.affine38.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedCached.native.step65).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedCached.native.step65 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds65 publicTops hom challenges gamma physical)

theorem canonical_affines
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    ∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedCached.native.definitions, definition.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  PredicateChecks.all (PredicateChecks.cons (affineHolds0 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds1 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds2 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds3 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds4 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds5 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds6 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds7 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds8 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds9 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds10 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds11 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds12 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds13 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds14 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds15 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds16 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds17 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds18 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds19 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds20 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds21 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds22 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds23 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds24 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds25 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds26 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds27 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds28 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds29 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds30 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds31 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds32 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds33 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds34 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds35 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds36 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds37 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds38 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.nil))))))))))))))))))))))))))))))))))))))))

end Airbender.Compiler.WindowedNative.UnifiedCached
