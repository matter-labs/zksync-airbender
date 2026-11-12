module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def sharedExpression412 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.atom ⟨63, by decide⟩))
                    (Compiler.Expression.atom ⟨101, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨64, by decide⟩))
                  (Compiler.Expression.atom ⟨36, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨44, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
              (Compiler.Expression.atom ⟨52, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
            (Compiler.Expression.atom ⟨52, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
          (Compiler.Expression.atom ⟨28, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.atom ⟨20, by decide⟩)))

def sharedExpression413 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨201, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744970275 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.mul
                      (Compiler.Expression.mul (Compiler.Expression.constant 1)
                        (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
                      (Compiler.Expression.atom ⟨80, by decide⟩)))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨81, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((134217711 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨83, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1476394981 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨82, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830435 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨84, by decide⟩))))))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩))
          (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.atom ⟨83, by decide⟩))
      (Compiler.Expression.atom ⟨84, by decide⟩))

def sharedExpression414 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨212, by decide⟩)))
            (Compiler.Expression.mul (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨213, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨63, by decide⟩))
            (Compiler.Expression.atom ⟨52, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.atom ⟨97, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨65, by decide⟩))
        (Compiler.Expression.atom ⟨60, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.atom ⟨60, by decide⟩))

def sharedExpression415 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression414
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨68, by decide⟩))
                (Compiler.Expression.atom ⟨97, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨69, by decide⟩))
              (Compiler.Expression.atom ⟨44, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨212, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨213, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨81, by decide⟩))
        (Compiler.Expression.atom ⟨212, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨81, by decide⟩))
      (Compiler.Expression.atom ⟨213, by decide⟩))

def sharedExpression416 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression415
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨212, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨213, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨83, by decide⟩))
            (Compiler.Expression.atom ⟨212, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.atom ⟨213, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨212, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨84, by decide⟩))
      (Compiler.Expression.atom ⟨213, by decide⟩))

def sharedExpression417 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.mul
                      (Compiler.Expression.mul (Compiler.Expression.constant 1)
                        (Compiler.Expression.atom ⟨63, by decide⟩))
                      (Compiler.Expression.atom ⟨52, by decide⟩)))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.atom ⟨64, by decide⟩))
                    (Compiler.Expression.atom ⟨97, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨65, by decide⟩))
                  (Compiler.Expression.atom ⟨60, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
                (Compiler.Expression.atom ⟨60, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
              (Compiler.Expression.atom ⟨97, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
            (Compiler.Expression.atom ⟨44, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add (Compiler.Expression.constant 0)
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨81, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨212, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨213, by decide⟩))))

def sharedExpression418 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨220, by decide⟩)))
            (Compiler.Expression.mul (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨221, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨63, by decide⟩))
            (Compiler.Expression.atom ⟨62, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.atom ⟨38, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨65, by decide⟩))
        (Compiler.Expression.atom ⟨46, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.atom ⟨54, by decide⟩))

def sharedExpression419 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression418
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨67, by decide⟩))
                (Compiler.Expression.atom ⟨54, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨68, by decide⟩))
              (Compiler.Expression.atom ⟨30, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨69, by decide⟩))
            (Compiler.Expression.atom ⟨22, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨207, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨80, by decide⟩))
        (Compiler.Expression.atom ⟨216, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨80, by decide⟩))
      (Compiler.Expression.atom ⟨220, by decide⟩))

def sharedExpression420 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression419
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨80, by decide⟩))
                (Compiler.Expression.atom ⟨221, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨81, by decide⟩))
              (Compiler.Expression.atom ⟨208, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨217, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨81, by decide⟩))
          (Compiler.Expression.atom ⟨220, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨81, by decide⟩))
        (Compiler.Expression.atom ⟨221, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨82, by decide⟩))
      (Compiler.Expression.atom ⟨209, by decide⟩))

def sharedExpression421 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression420
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨214, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨220, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨221, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.atom ⟨209, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨214, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨83, by decide⟩))
      (Compiler.Expression.atom ⟨220, by decide⟩))

def sharedExpression422 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.atom ⟨63, by decide⟩))
                    (Compiler.Expression.atom ⟨62, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨64, by decide⟩))
                  (Compiler.Expression.atom ⟨38, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨46, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
              (Compiler.Expression.atom ⟨54, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
            (Compiler.Expression.atom ⟨54, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
          (Compiler.Expression.atom ⟨30, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.atom ⟨22, by decide⟩)))

def sharedExpression423 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.add (Compiler.Expression.constant 0) sharedExpression422)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨207, by decide⟩))
            (Compiler.Expression.atom ⟨216, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add
                      (Compiler.Expression.add (Compiler.Expression.constant 0)
                        (Compiler.Expression.atom ⟨80, by decide⟩))
                      (Compiler.Expression.atom ⟨81, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨83, by decide⟩))
                (Compiler.Expression.atom ⟨84, by decide⟩)))))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨220, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨221, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨81, by decide⟩))
          (Compiler.Expression.atom ⟨84, by decide⟩)))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨208, by decide⟩))
        (Compiler.Expression.atom ⟨217, by decide⟩)))

def native.originalProjection (index : Nat) : Fin 266 :=
  if bound : index < 222 then ⟨index, Nat.lt_of_lt_of_le bound (by decide)⟩ else ⟨0, by decide⟩

def native.readProjection : List (Fin 266 × Fin 266) :=
  [(⟨238, by decide⟩, ⟨239, by decide⟩), (⟨240, by decide⟩, ⟨241, by decide⟩), (⟨242, by decide⟩, ⟨243, by decide⟩),
    (⟨244, by decide⟩, ⟨245, by decide⟩), (⟨246, by decide⟩, ⟨247, by decide⟩), (⟨248, by decide⟩, ⟨249, by decide⟩),
    (⟨250, by decide⟩, ⟨251, by decide⟩), (⟨252, by decide⟩, ⟨253, by decide⟩), (⟨254, by decide⟩, ⟨255, by decide⟩),
    (⟨256, by decide⟩, ⟨257, by decide⟩), (⟨258, by decide⟩, ⟨259, by decide⟩), (⟨260, by decide⟩, ⟨261, by decide⟩),
    (⟨262, by decide⟩, ⟨263, by decide⟩), (⟨264, by decide⟩, ⟨265, by decide⟩)]

def native.borrowProjection : List (Fin 266) :=
  [⟨222, by decide⟩, ⟨223, by decide⟩, ⟨224, by decide⟩, ⟨225, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩,
    ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨231, by decide⟩, ⟨232, by decide⟩, ⟨233, by decide⟩,
    ⟨234, by decide⟩, ⟨235, by decide⟩]

def native.helperPlacement : Source.HelperPlacement 266 :=
  ⟨⟨native.originalProjection, fun query limb =>
      let places := ((native.readProjection)[query]?).getD (⟨0, by decide⟩, ⟨0, by decide⟩)
      if limb.val = 0 then places.1 else places.2,
      fun _ => ⟨0, by decide⟩, fun _ _ => ⟨0, by decide⟩, fun _ _ => ⟨0, by decide⟩⟩,
    fun index => ((native.borrowProjection)[index]?).getD ⟨0, by decide⟩⟩

noncomputable def native.helperAssertions : List Source.HelperAssertion :=
  [Source.HelperAssertion.boolean (Source.HelperField.borrow 0),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 1),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 2),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 3),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 4),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 5),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 6),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 7),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 8),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 9),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 10),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 11),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 12),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 13)]

theorem native.helperReferencesValid :
    (native.helperAssertions).all
        (fun assertion =>
          match assertion with
          | .zero field | .boolean field => field.referencesValid 222 14 0 14 false) =
      true :=
  by decide +kernel

def sharedExpression424 : Compiler.Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨65, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((805306362 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨66, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨67, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1342177270 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨68, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1610612724 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨69, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((134217711 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨71, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨72, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((805306362 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨73, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨74, by decide⟩))))

def sharedExpression425 : Compiler.Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add (Compiler.Expression.constant 0)
                      (Compiler.Expression.atom ⟨64, by decide⟩))
                    (Compiler.Expression.mul
                      (Compiler.Expression.mul (Compiler.Expression.constant 1)
                        (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
                      (Compiler.Expression.atom ⟨65, by decide⟩)))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((805306362 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨66, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨67, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1342177270 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨68, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1610612724 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨69, by decide⟩)))
          (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨65, by decide⟩))
      (Compiler.Expression.atom ⟨68, by decide⟩))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨63, by decide⟩))
            (Compiler.Expression.atom ⟨66, by decide⟩))
          (Compiler.Expression.atom ⟨67, by decide⟩)))
      (Compiler.Expression.atom ⟨74, by decide⟩))

def sharedExpression426 : Compiler.Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨71, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨72, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((805306362 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨73, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨74, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨63, by decide⟩))
              (Compiler.Expression.atom ⟨66, by decide⟩))
            (Compiler.Expression.atom ⟨67, by decide⟩))
          (Compiler.Expression.atom ⟨69, by decide⟩)))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((671088651 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨74, by decide⟩))))
end Airbender.Compiler.FullArithmeticNative.KeccakCached
