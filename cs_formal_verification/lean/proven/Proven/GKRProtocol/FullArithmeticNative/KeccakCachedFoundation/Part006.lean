module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part005
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def sharedExpression102 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression101
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((135196399 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨64, by decide⟩))
                (Compiler.Expression.atom ⟨82, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1880166674 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.atom ⟨83, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((671787691 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨64, by decide⟩))
            (Compiler.Expression.atom ⟨84, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.atom ⟨127, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨31, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨65, by decide⟩))
      (Compiler.Expression.atom ⟨47, by decide⟩))

def sharedExpression103 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression102
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨66, by decide⟩))
                (Compiler.Expression.atom ⟨23, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨67, by decide⟩))
              (Compiler.Expression.atom ⟨23, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨68, by decide⟩))
            (Compiler.Expression.atom ⟨23, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨69, by decide⟩))
          (Compiler.Expression.atom ⟨23, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((940083337 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨80, by decide⟩))
        (Compiler.Expression.atom ⟨80, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1747067427 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨80, by decide⟩))
      (Compiler.Expression.atom ⟨81, by decide⟩))

def sharedExpression104 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression103
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1343575382 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨80, by decide⟩))
                (Compiler.Expression.atom ⟨82, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1075279736 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨83, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1880166674 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨84, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨127, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((806984090 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨81, by decide⟩))
        (Compiler.Expression.atom ⟨81, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1210476135 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨81, by decide⟩))
      (Compiler.Expression.atom ⟨82, by decide⟩))

def sharedExpression105 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression104
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((942180489 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨81, by decide⟩))
                (Compiler.Expression.atom ⟨83, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1747067427 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨81, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨127, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((403492045 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨82, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((538688444 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.atom ⟨83, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1343575382 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨82, by decide⟩))
      (Compiler.Expression.atom ⟨84, by decide⟩))

def sharedExpression106 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression105
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨127, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((135196399 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨83, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1075279736 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨83, by decide⟩))
            (Compiler.Expression.atom ⟨84, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.atom ⟨127, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((940083337 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨84, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨84, by decide⟩))
      (Compiler.Expression.atom ⟨127, by decide⟩))

def sharedExpression107 : Compiler.Expression 301 Source.BaseField :=
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
                    (Compiler.Expression.atom ⟨17, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨64, by decide⟩))
                  (Compiler.Expression.atom ⟨31, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨47, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
              (Compiler.Expression.atom ⟨23, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
            (Compiler.Expression.atom ⟨23, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
          (Compiler.Expression.atom ⟨23, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.atom ⟨23, by decide⟩)))

def sharedExpression108 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.constant 1)
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨126, by decide⟩))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1744970275 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨64, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨80, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨84, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1610612724 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨82, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1879048178 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨83, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1207959527 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨81, by decide⟩)))))

def sharedExpression109 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.add (Compiler.Expression.constant 0) sharedExpression107)
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
                      (Compiler.Expression.add
                        (Compiler.Expression.add (Compiler.Expression.constant 0)
                          (Compiler.Expression.atom ⟨64, by decide⟩))
                        (Compiler.Expression.atom ⟨80, by decide⟩))
                      (Compiler.Expression.atom ⟨81, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨83, by decide⟩))
                (Compiler.Expression.atom ⟨84, by decide⟩)))))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨126, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨127, by decide⟩)))))
    (Compiler.Expression.mul sharedExpression108
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
                (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨84, by decide⟩)))

def sharedExpression110 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨134, by decide⟩)))
            (Compiler.Expression.mul (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨135, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨63, by decide⟩))
            (Compiler.Expression.atom ⟨23, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.atom ⟨134, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨135, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨65, by decide⟩))
      (Compiler.Expression.atom ⟨90, by decide⟩))

def sharedExpression111 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression110
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨66, by decide⟩))
                (Compiler.Expression.atom ⟨55, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨68, by decide⟩))
              (Compiler.Expression.atom ⟨31, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨69, by decide⟩))
            (Compiler.Expression.atom ⟨90, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨134, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨80, by decide⟩))
        (Compiler.Expression.atom ⟨135, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨81, by decide⟩))
      (Compiler.Expression.atom ⟨134, by decide⟩))

def sharedExpression112 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression111
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨81, by decide⟩))
                (Compiler.Expression.atom ⟨135, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨134, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨135, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.atom ⟨134, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨135, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨84, by decide⟩))
      (Compiler.Expression.atom ⟨134, by decide⟩))

def sharedExpression113 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.atom ⟨63, by decide⟩))
                    (Compiler.Expression.atom ⟨23, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨65, by decide⟩))
                  (Compiler.Expression.atom ⟨90, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
                (Compiler.Expression.atom ⟨55, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
              (Compiler.Expression.atom ⟨31, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
            (Compiler.Expression.atom ⟨90, by decide⟩)))))
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
                    (Compiler.Expression.add
                      (Compiler.Expression.add (Compiler.Expression.constant 0)
                        (Compiler.Expression.atom ⟨64, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨81, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨134, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨135, by decide⟩))))

def sharedExpression114 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨142, by decide⟩)))
            (Compiler.Expression.mul (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨143, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨63, by decide⟩))
            (Compiler.Expression.atom ⟨90, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.atom ⟨90, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨137, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨64, by decide⟩))
      (Compiler.Expression.atom ⟨143, by decide⟩))

def sharedExpression115 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression114
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨49, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨66, by decide⟩))
              (Compiler.Expression.atom ⟨25, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨67, by decide⟩))
            (Compiler.Expression.atom ⟨25, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨68, by decide⟩))
          (Compiler.Expression.atom ⟨90, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.atom ⟨25, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨80, by decide⟩))
      (Compiler.Expression.atom ⟨135, by decide⟩))

def sharedExpression116 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression115
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨80, by decide⟩))
                (Compiler.Expression.atom ⟨142, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨143, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨144, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨81, by decide⟩))
          (Compiler.Expression.atom ⟨135, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨81, by decide⟩))
        (Compiler.Expression.atom ⟨142, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨81, by decide⟩))
      (Compiler.Expression.atom ⟨143, by decide⟩))

def sharedExpression117 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression116
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨81, by decide⟩))
                (Compiler.Expression.atom ⟨144, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨137, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨143, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.atom ⟨134, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨142, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((544 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨83, by decide⟩))
      (Compiler.Expression.atom ⟨143, by decide⟩))

def sharedExpression118 : Compiler.Expression 301 Source.BaseField :=
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
                    (Compiler.Expression.atom ⟨90, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨64, by decide⟩))
                  (Compiler.Expression.atom ⟨90, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨49, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
              (Compiler.Expression.atom ⟨25, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
            (Compiler.Expression.atom ⟨25, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
          (Compiler.Expression.atom ⟨90, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.atom ⟨25, by decide⟩)))

def sharedExpression119 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.add (Compiler.Expression.constant 0) sharedExpression118)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨134, by decide⟩))
            (Compiler.Expression.atom ⟨143, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨136, by decide⟩))
          (Compiler.Expression.atom ⟨145, by decide⟩))))
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
                    (Compiler.Expression.add
                      (Compiler.Expression.add (Compiler.Expression.constant 0)
                        (Compiler.Expression.atom ⟨64, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨81, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨142, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨143, by decide⟩))))
end Airbender.Compiler.FullArithmeticNative.KeccakCached
