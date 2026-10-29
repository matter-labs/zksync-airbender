import Airbender.Proofs.GKRProtocol.WindowedNative.UnifiedUncachedFoundation
import Airbender.Proofs.GKRProtocol.BaseAffine

namespace Airbender.Compiler.WindowedNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem stepHolds0
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step0).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step0) (List.mem_cons_self)

theorem stepHolds1
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step1).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step1) (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem stepHolds2
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step2).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step2) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem stepHolds3
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step3).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step3) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))

theorem stepHolds4
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    ((nativeGate0 publicTops).functional).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical ((nativeGate0 publicTops).functional) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))

theorem stepHolds5
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    ((nativeGate1 publicTops).functional).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical ((nativeGate1 publicTops).functional) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))

theorem stepHolds6
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step6).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step6) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))

theorem stepHolds7
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step7).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step7) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))

theorem stepHolds8
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step8).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step8) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))

theorem stepHolds9
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step9).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step9) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))

theorem stepHolds10
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step10).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step10) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))

theorem stepHolds11
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step11).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step11) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))

theorem stepHolds12
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step12).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step12) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))

theorem stepHolds13
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step13).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step13) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))

theorem stepHolds14
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step14).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step14) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))

theorem stepHolds15
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step15).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step15) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))

theorem stepHolds16
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step16).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step16) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))

theorem stepHolds17
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step17).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step17) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))

theorem stepHolds18
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step18).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step18) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))

theorem stepHolds19
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step19).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step19) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))

theorem stepHolds20
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step20).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step20) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))

theorem stepHolds21
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step21).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step21) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))

theorem stepHolds22
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step22).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step22) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))

theorem stepHolds23
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step23).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step23) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))

theorem stepHolds24
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step24).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step24) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))

theorem stepHolds25
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step25).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step25) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))

theorem stepHolds26
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step26).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step26) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))

theorem stepHolds27
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step27).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step27) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))

theorem stepHolds28
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step28).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step28) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))

theorem stepHolds29
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step29).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step29) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))

theorem stepHolds30
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step30).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step30) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))

theorem stepHolds31
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step31).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step31) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))

theorem stepHolds32
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step32).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step32) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))

theorem stepHolds33
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step33).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step33) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))

theorem stepHolds34
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step34).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step34) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))

theorem stepHolds35
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step35).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step35) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))

theorem stepHolds36
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step36).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step36) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))

theorem stepHolds37
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step37).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step37) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))

theorem stepHolds38
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step38).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step38) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))

theorem stepHolds39
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step39).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step39) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))

theorem stepHolds40
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step40).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step40) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))

theorem stepHolds41
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step41).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step41) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds42
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step42).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step42) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds43
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step43).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step43) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds44
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step44).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step44) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds45
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step45).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step45) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds46
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step46).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step46) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds47
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step47).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step47) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds48
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step48).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step48) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds49
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step49).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step49) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))

theorem stepHolds50
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step50).Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  canonical_steps publicTops hom challenges gamma physical (Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step50) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem canonical_base
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) (address : GKRAddress) (role : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true) :
    canonical publicTops hom challenges gamma physical address = hom (physical address) := by
  change (if Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address then _ else _) = _
  exact if_pos role

theorem lookupHolds0
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate0.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate0.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds6 publicTops hom challenges gamma physical)

theorem lookupHolds1
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate1.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate1.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds7 publicTops hom challenges gamma physical)

theorem lookupHolds2
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate2.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate2.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds8 publicTops hom challenges gamma physical)

theorem lookupHolds3
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate3.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate3.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds9 publicTops hom challenges gamma physical)

theorem lookupHolds4
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate4.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate4.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds10 publicTops hom challenges gamma physical)

theorem lookupHolds5
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate5.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate5.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds11 publicTops hom challenges gamma physical)

theorem lookupHolds6
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate6.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate6.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds12 publicTops hom challenges gamma physical)

theorem lookupHolds7
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate7.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate7.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds13 publicTops hom challenges gamma physical)

theorem lookupHolds8
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate8.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate8.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds14 publicTops hom challenges gamma physical)

theorem lookupHolds9
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate9.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate9.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds15 publicTops hom challenges gamma physical)

theorem lookupHolds10
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate10.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate10.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds16 publicTops hom challenges gamma physical)

theorem lookupHolds11
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate11.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate11.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds19 publicTops hom challenges gamma physical)

theorem lookupHolds12
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate12.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate12.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds20 publicTops hom challenges gamma physical)

theorem lookupHolds13
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate13.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate13.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds21 publicTops hom challenges gamma physical)

theorem lookupHolds14
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate14.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate14.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds22 publicTops hom challenges gamma physical)

theorem lookupHolds15
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate15.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate15.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds23 publicTops hom challenges gamma physical)

theorem lookupHolds16
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate16.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate16.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds24 publicTops hom challenges gamma physical)

theorem lookupHolds17
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate17.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate17.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds25 publicTops hom challenges gamma physical)

theorem lookupHolds18
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate18.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate18.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds26 publicTops hom challenges gamma physical)

theorem lookupHolds19
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate19.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate19.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds27 publicTops hom challenges gamma physical)

theorem lookupHolds20
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate20.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate20.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds28 publicTops hom challenges gamma physical)

theorem lookupHolds21
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate21.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate21.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds29 publicTops hom challenges gamma physical)

theorem lookupHolds22
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate22.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate22.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds30 publicTops hom challenges gamma physical)

theorem lookupHolds23
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate23.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate23.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds31 publicTops hom challenges gamma physical)

theorem lookupHolds24
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate24.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate24.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds34 publicTops hom challenges gamma physical)

theorem lookupHolds25
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate25.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate25.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds35 publicTops hom challenges gamma physical)

theorem lookupHolds26
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate26.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate26.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds36 publicTops hom challenges gamma physical)

theorem lookupHolds27
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate27.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate27.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds37 publicTops hom challenges gamma physical)

theorem lookupHolds28
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate28.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate28.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds38 publicTops hom challenges gamma physical)

theorem lookupHolds29
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate29.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate29.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds39 publicTops hom challenges gamma physical)

theorem lookupHolds30
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate30.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate30.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds40 publicTops hom challenges gamma physical)

theorem lookupHolds31
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate31.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate31.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds41 publicTops hom challenges gamma physical)

theorem lookupHolds32
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate32.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate32.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds42 publicTops hom challenges gamma physical)

theorem lookupHolds33
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate33.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate33.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds43 publicTops hom challenges gamma physical)

theorem lookupHolds34
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate34.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate34.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds44 publicTops hom challenges gamma physical)

theorem lookupHolds35
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate35.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate35.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds45 publicTops hom challenges gamma physical)

theorem lookupHolds36
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate36.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate36.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds46 publicTops hom challenges gamma physical)

theorem lookupHolds37
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate37.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate37.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds47 publicTops hom challenges gamma physical)

theorem lookupHolds38
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate38.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate38.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds48 publicTops hom challenges gamma physical)

theorem lookupHolds39
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate39.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate39.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds49 publicTops hom challenges gamma physical)

theorem lookupHolds40
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.LookupNative.UnifiedUncached.native.gate40.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.LookupNative.UnifiedUncached.native.gate40.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds50 publicTops hom challenges gamma physical)

theorem productHolds0
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate0.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedUncached.native.gate0.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds0 publicTops hom challenges gamma physical)

theorem productHolds1
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate1.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedUncached.native.gate1.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds1 publicTops hom challenges gamma physical)

theorem productHolds2
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate2.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedUncached.native.gate2.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds2 publicTops hom challenges gamma physical)

theorem productHolds3
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate3.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedUncached.native.gate3.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds3 publicTops hom challenges gamma physical)

theorem productHolds4
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (nativeGate0 publicTops).Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  (nativeGate0 publicTops).functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds4 publicTops hom challenges gamma physical)

theorem productHolds5
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    (nativeGate1 publicTops).Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  (nativeGate1 publicTops).functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds5 publicTops hom challenges gamma physical)

theorem productHolds6
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate6.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedUncached.native.gate6.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds17 publicTops hom challenges gamma physical)

theorem productHolds7
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate7.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedUncached.native.gate7.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds18 publicTops hom challenges gamma physical)

theorem productHolds8
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate8.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds25 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds9
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate9.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds26 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds10
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate10.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds30 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds11
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate11.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds31 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds12
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate12.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedUncached.native.gate12.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds32 publicTops hom challenges gamma physical)

theorem productHolds13
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate13.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  Airbender.Compiler.ProductNative.UnifiedUncached.native.gate13.functional_sound hom challenges gamma (canonical publicTops hom challenges gamma physical) (stepHolds33 publicTops hom challenges gamma physical)

theorem productHolds14
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate14.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds37 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds15
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate15.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds38 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds16
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate16.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds40 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds17
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate17.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds41 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds18
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate18.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds42 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds19
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate19.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds43 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds20
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate20.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds47 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds21
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate21.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds48 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds22
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate22.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds49 publicTops hom challenges gamma physical) _ List.mem_cons_self

theorem productHolds23
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.ProductNative.UnifiedUncached.native.gate23.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by exact (stepHolds50 publicTops hom challenges gamma physical) _ List.mem_cons_self

noncomputable def productGates (publicTops : Nat → Nat) : List NativeProductGate := [Airbender.Compiler.ProductNative.UnifiedUncached.native.gate0, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate1, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate2, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate3, (nativeGate0 publicTops), (nativeGate1 publicTops), Airbender.Compiler.ProductNative.UnifiedUncached.native.gate6, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate7, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate8, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate9, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate10, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate11, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate12, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate13, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate14, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate15, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate16, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate17, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate18, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate19, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate20, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate21, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate22, Airbender.Compiler.ProductNative.UnifiedUncached.native.gate23]

theorem canonical_lookups
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    ∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedUncached.native.gates, gate.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
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
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine0.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseRecipe0 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.gate0 Airbender.Compiler.FunctionalNative.UnifiedUncached.native.basePortsChecked0 Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseRelationChecked0 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.gateChecked0 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates ⟨0, by decide +kernel⟩))

theorem affineHolds1
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine1.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseRecipe1 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.gate42 Airbender.Compiler.FunctionalNative.UnifiedUncached.native.basePortsChecked1 Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseRelationChecked1 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.gateChecked42 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates ⟨42, by decide +kernel⟩))

theorem affineHolds2
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine2.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseRecipe2 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.gate43 Airbender.Compiler.FunctionalNative.UnifiedUncached.native.basePortsChecked2 Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseRelationChecked2 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.gateChecked43 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates ⟨43, by decide +kernel⟩))

theorem affineHolds3
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine3.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  NativeBaseRecipe.definition_of_gate Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseRecipe3 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.gate123 Airbender.Compiler.FunctionalNative.UnifiedUncached.native.basePortsChecked3 Airbender.Compiler.FunctionalNative.UnifiedUncached.native.baseRelationChecked3 Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.gateChecked123 hom challenges physical (canonical publicTops hom challenges gamma physical) (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates ⟨123, by decide +kernel⟩))

theorem affineHolds4
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine4.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step25.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine4.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step25).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step25 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds25 publicTops hom challenges gamma physical)

theorem affineHolds5
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine5.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step26.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine5.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step26).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step26 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds26 publicTops hom challenges gamma physical)

theorem affineHolds6
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine6.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step30.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine6.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step30).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step30 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds30 publicTops hom challenges gamma physical)

theorem affineHolds7
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine7.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step31.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine7.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step31).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step31 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds31 publicTops hom challenges gamma physical)

theorem affineHolds8
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine8.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step37.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine8.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step37).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step37 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds37 publicTops hom challenges gamma physical)

theorem affineHolds9
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine9.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step38.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine9.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step38).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step38 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds38 publicTops hom challenges gamma physical)

theorem affineHolds10
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine10.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step40.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine10.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step40).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step40 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds40 publicTops hom challenges gamma physical)

theorem affineHolds11
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine11.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step41.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine11.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step41).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step41 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds41 publicTops hom challenges gamma physical)

theorem affineHolds12
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine12.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step42.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine12.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step42).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step42 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds42 publicTops hom challenges gamma physical)

theorem affineHolds13
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine13.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step43.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine13.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step43).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step43 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds43 publicTops hom challenges gamma physical)

theorem affineHolds14
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine14.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step47.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine14.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step47).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step47 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds47 publicTops hom challenges gamma physical)

theorem affineHolds15
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine15.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step48.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine15.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step48).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step48 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds48 publicTops hom challenges gamma physical)

theorem affineHolds16
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine16.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step49.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine16.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step49).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step49 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds49 publicTops hom challenges gamma physical)

theorem affineHolds17
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (_arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine17.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  by
    have bridge (values : GKRAddress → R) (equation : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step50.Holds hom challenges gamma values) : Airbender.Compiler.FunctionalNative.UnifiedUncached.native.affine17.Holds hom challenges values := by
      exact equation ((Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step50).get ⟨0, by decide +kernel⟩) (List.get_mem Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step50 ⟨0, by decide +kernel⟩)
    exact bridge (canonical publicTops hom challenges gamma physical) (stepHolds50 publicTops hom challenges gamma physical)

theorem canonical_affines
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0) :
    ∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedUncached.native.definitions, definition.Holds hom challenges (canonical publicTops hom challenges gamma physical) :=
  PredicateChecks.all (PredicateChecks.cons (affineHolds0 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds1 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds2 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds3 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds4 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds5 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds6 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds7 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds8 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds9 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds10 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds11 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds12 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds13 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds14 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds15 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds16 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.cons (affineHolds17 publicTops hom challenges gamma physical arithmetic) (PredicateChecks.nil)))))))))))))))))))

end Airbender.Compiler.WindowedNative.UnifiedUncached
