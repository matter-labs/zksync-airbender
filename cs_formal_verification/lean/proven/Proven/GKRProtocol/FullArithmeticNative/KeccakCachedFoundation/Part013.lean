module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part012
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def sharedExpression231 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression230
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨81, by decide⟩))
                (Compiler.Expression.atom ⟨152, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨81, by decide⟩))
              (Compiler.Expression.atom ⟨154, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨155, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1075279736 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨82, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((673884843 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.atom ⟨83, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1210476135 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨82, by decide⟩))
      (Compiler.Expression.atom ⟨84, by decide⟩))

def sharedExpression232 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression231
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨152, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨154, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨155, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1611871028 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.atom ⟨83, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1747067427 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨84, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨83, by decide⟩))
      (Compiler.Expression.atom ⟨152, by decide⟩))

def sharedExpression233 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression232
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨83, by decide⟩))
                (Compiler.Expression.atom ⟨154, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨155, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((135196399 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨84, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨152, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨154, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨84, by decide⟩))
      (Compiler.Expression.atom ⟨155, by decide⟩))

def sharedExpression234 : Compiler.Expression 301 Source.BaseField :=
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
                    (Compiler.Expression.atom ⟨92, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨64, by decide⟩))
                  (Compiler.Expression.atom ⟨19, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨43, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
              (Compiler.Expression.atom ⟨35, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
            (Compiler.Expression.atom ⟨35, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
          (Compiler.Expression.atom ⟨19, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.atom ⟨19, by decide⟩)))

def sharedExpression235 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.constant 1)
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨152, by decide⟩))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1744970275 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨65, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((805306362 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨80, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1879048178 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨84, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((402653165 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨83, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((671088619 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((939524073 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨82, by decide⟩)))))

def sharedExpression236 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.add (Compiler.Expression.constant 0) sharedExpression234)
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
                          (Compiler.Expression.atom ⟨65, by decide⟩))
                        (Compiler.Expression.atom ⟨80, by decide⟩))
                      (Compiler.Expression.atom ⟨81, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨83, by decide⟩))
                (Compiler.Expression.atom ⟨84, by decide⟩)))))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨154, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨155, by decide⟩)))))
    (Compiler.Expression.mul sharedExpression235
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨84, by decide⟩)))

def sharedExpression237 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨162, by decide⟩)))
            (Compiler.Expression.mul (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨163, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨63, by decide⟩))
            (Compiler.Expression.atom ⟨35, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.atom ⟨92, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨65, by decide⟩))
        (Compiler.Expression.atom ⟨162, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨65, by decide⟩))
      (Compiler.Expression.atom ⟨163, by decide⟩))

def sharedExpression238 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression237
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨66, by decide⟩))
                (Compiler.Expression.atom ⟨59, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨68, by decide⟩))
              (Compiler.Expression.atom ⟨92, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨69, by decide⟩))
            (Compiler.Expression.atom ⟨51, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨162, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨80, by decide⟩))
        (Compiler.Expression.atom ⟨163, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨81, by decide⟩))
      (Compiler.Expression.atom ⟨162, by decide⟩))

def sharedExpression239 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression238
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨81, by decide⟩))
                (Compiler.Expression.atom ⟨163, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨162, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨163, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.atom ⟨162, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨163, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨84, by decide⟩))
      (Compiler.Expression.atom ⟨162, by decide⟩))

def sharedExpression240 : Compiler.Expression 301 Source.BaseField :=
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
                    (Compiler.Expression.atom ⟨35, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨64, by decide⟩))
                  (Compiler.Expression.atom ⟨92, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
                (Compiler.Expression.atom ⟨59, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
              (Compiler.Expression.atom ⟨92, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
            (Compiler.Expression.atom ⟨51, by decide⟩)))))
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
                        (Compiler.Expression.atom ⟨65, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨81, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨162, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨163, by decide⟩))))

def sharedExpression241 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨170, by decide⟩)))
            (Compiler.Expression.mul (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨171, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨63, by decide⟩))
            (Compiler.Expression.atom ⟨96, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.atom ⟨21, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨65, by decide⟩))
        (Compiler.Expression.atom ⟨96, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨65, by decide⟩))
      (Compiler.Expression.atom ⟨159, by decide⟩))

def sharedExpression242 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression241
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨168, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨65, by decide⟩))
              (Compiler.Expression.atom ⟨170, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨171, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨66, by decide⟩))
          (Compiler.Expression.atom ⟨37, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨37, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨68, by decide⟩))
      (Compiler.Expression.atom ⟨21, by decide⟩))

def sharedExpression243 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression242
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨69, by decide⟩))
                (Compiler.Expression.atom ⟨96, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨159, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨168, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨170, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨80, by decide⟩))
        (Compiler.Expression.atom ⟨171, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨81, by decide⟩))
      (Compiler.Expression.atom ⟨159, by decide⟩))

def sharedExpression244 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression243
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨81, by decide⟩))
                (Compiler.Expression.atom ⟨168, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨81, by decide⟩))
              (Compiler.Expression.atom ⟨170, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨171, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨161, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.atom ⟨166, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨82, by decide⟩))
      (Compiler.Expression.atom ⟨170, by decide⟩))

def sharedExpression245 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression244
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨171, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨158, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨83, by decide⟩))
            (Compiler.Expression.atom ⟨167, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.atom ⟨170, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨171, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨84, by decide⟩))
      (Compiler.Expression.atom ⟨161, by decide⟩))

def sharedExpression246 : Compiler.Expression 301 Source.BaseField :=
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
                    (Compiler.Expression.atom ⟨96, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨64, by decide⟩))
                  (Compiler.Expression.atom ⟨21, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨96, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
              (Compiler.Expression.atom ⟨37, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
            (Compiler.Expression.atom ⟨37, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
          (Compiler.Expression.atom ⟨21, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.atom ⟨96, by decide⟩)))

def sharedExpression247 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.add (Compiler.Expression.constant 0) sharedExpression246)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨158, by decide⟩))
          (Compiler.Expression.atom ⟨167, by decide⟩))))
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
                        (Compiler.Expression.atom ⟨65, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨81, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨170, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨171, by decide⟩))))

def sharedExpression248 : Compiler.Expression 301 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨156, by decide⟩)))
            (Compiler.Expression.mul (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨157, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨63, by decide⟩))
            (Compiler.Expression.atom ⟨93, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.atom ⟨20, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744970275 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨65, by decide⟩))
        (Compiler.Expression.atom ⟨65, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((940083337 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨65, by decide⟩))
      (Compiler.Expression.atom ⟨80, by decide⟩))
end Airbender.Compiler.FullArithmeticNative.KeccakCached
