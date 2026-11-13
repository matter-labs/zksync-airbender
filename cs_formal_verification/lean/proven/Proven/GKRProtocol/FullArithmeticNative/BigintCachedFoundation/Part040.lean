module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def sharedExpression704 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨24, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨59, by decide⟩))
              (Compiler.Expression.atom ⟨76, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨60, by decide⟩))
            (Compiler.Expression.atom ⟨76, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨61, by decide⟩))
          (Compiler.Expression.atom ⟨76, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨62, by decide⟩))
        (Compiler.Expression.atom ⟨140, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨63, by decide⟩))
      (Compiler.Expression.atom ⟨156, by decide⟩))

def sharedExpression705 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨24, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨59, by decide⟩))
                  (Compiler.Expression.atom ⟨76, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨60, by decide⟩))
                (Compiler.Expression.atom ⟨76, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨61, by decide⟩))
              (Compiler.Expression.atom ⟨76, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨62, by decide⟩))
            (Compiler.Expression.atom ⟨140, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨63, by decide⟩))
          (Compiler.Expression.atom ⟨156, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨22, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.atom ⟨76, by decide⟩))

def sharedExpression706 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨27, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨59, by decide⟩))
              (Compiler.Expression.atom ⟨77, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨60, by decide⟩))
            (Compiler.Expression.atom ⟨77, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨61, by decide⟩))
          (Compiler.Expression.atom ⟨77, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨62, by decide⟩))
        (Compiler.Expression.atom ⟨141, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨63, by decide⟩))
      (Compiler.Expression.atom ⟨157, by decide⟩))

def sharedExpression707 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨27, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨59, by decide⟩))
                  (Compiler.Expression.atom ⟨77, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨60, by decide⟩))
                (Compiler.Expression.atom ⟨77, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨61, by decide⟩))
              (Compiler.Expression.atom ⟨77, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨62, by decide⟩))
            (Compiler.Expression.atom ⟨141, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨63, by decide⟩))
          (Compiler.Expression.atom ⟨157, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨25, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.atom ⟨77, by decide⟩))

def sharedExpression708 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨28, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨59, by decide⟩))
              (Compiler.Expression.atom ⟨78, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨60, by decide⟩))
            (Compiler.Expression.atom ⟨78, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨61, by decide⟩))
          (Compiler.Expression.atom ⟨78, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨62, by decide⟩))
        (Compiler.Expression.atom ⟨142, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨63, by decide⟩))
      (Compiler.Expression.atom ⟨158, by decide⟩))

def sharedExpression709 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨28, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨59, by decide⟩))
                  (Compiler.Expression.atom ⟨78, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨60, by decide⟩))
                (Compiler.Expression.atom ⟨78, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨61, by decide⟩))
              (Compiler.Expression.atom ⟨78, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨62, by decide⟩))
            (Compiler.Expression.atom ⟨142, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨63, by decide⟩))
          (Compiler.Expression.atom ⟨158, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨26, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.atom ⟨78, by decide⟩))

def sharedExpression710 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨31, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨59, by decide⟩))
              (Compiler.Expression.atom ⟨79, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨60, by decide⟩))
            (Compiler.Expression.atom ⟨79, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨61, by decide⟩))
          (Compiler.Expression.atom ⟨79, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨62, by decide⟩))
        (Compiler.Expression.atom ⟨143, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨63, by decide⟩))
      (Compiler.Expression.atom ⟨159, by decide⟩))

def sharedExpression711 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨31, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨59, by decide⟩))
                  (Compiler.Expression.atom ⟨79, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨60, by decide⟩))
                (Compiler.Expression.atom ⟨79, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨61, by decide⟩))
              (Compiler.Expression.atom ⟨79, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨62, by decide⟩))
            (Compiler.Expression.atom ⟨143, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨63, by decide⟩))
          (Compiler.Expression.atom ⟨159, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨29, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.atom ⟨79, by decide⟩))

def sharedExpression712 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨32, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨59, by decide⟩))
              (Compiler.Expression.atom ⟨80, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨60, by decide⟩))
            (Compiler.Expression.atom ⟨80, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨61, by decide⟩))
          (Compiler.Expression.atom ⟨80, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨62, by decide⟩))
        (Compiler.Expression.atom ⟨144, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨63, by decide⟩))
      (Compiler.Expression.atom ⟨160, by decide⟩))

def sharedExpression713 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨32, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨59, by decide⟩))
                  (Compiler.Expression.atom ⟨80, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨60, by decide⟩))
                (Compiler.Expression.atom ⟨80, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨61, by decide⟩))
              (Compiler.Expression.atom ⟨80, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨62, by decide⟩))
            (Compiler.Expression.atom ⟨144, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨63, by decide⟩))
          (Compiler.Expression.atom ⟨160, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨30, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.atom ⟨80, by decide⟩))

def sharedExpression714 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨35, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨59, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨60, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨61, by decide⟩))
          (Compiler.Expression.atom ⟨81, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨62, by decide⟩))
        (Compiler.Expression.atom ⟨145, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨63, by decide⟩))
      (Compiler.Expression.atom ⟨161, by decide⟩))

def sharedExpression715 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨35, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨59, by decide⟩))
                  (Compiler.Expression.atom ⟨81, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨60, by decide⟩))
                (Compiler.Expression.atom ⟨81, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨61, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨62, by decide⟩))
            (Compiler.Expression.atom ⟨145, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨63, by decide⟩))
          (Compiler.Expression.atom ⟨161, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨33, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.atom ⟨81, by decide⟩))

def sharedExpression716 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨36, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨59, by decide⟩))
              (Compiler.Expression.atom ⟨82, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨60, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨61, by decide⟩))
          (Compiler.Expression.atom ⟨82, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨62, by decide⟩))
        (Compiler.Expression.atom ⟨146, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨63, by decide⟩))
      (Compiler.Expression.atom ⟨162, by decide⟩))

def sharedExpression717 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨36, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨59, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨60, by decide⟩))
                (Compiler.Expression.atom ⟨82, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨61, by decide⟩))
              (Compiler.Expression.atom ⟨82, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨62, by decide⟩))
            (Compiler.Expression.atom ⟨146, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨63, by decide⟩))
          (Compiler.Expression.atom ⟨162, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨34, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.atom ⟨82, by decide⟩))

def sharedExpression718 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨62, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨57, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨59, by decide⟩))
            (Compiler.Expression.atom ⟨98, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨60, by decide⟩))
          (Compiler.Expression.atom ⟨98, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨61, by decide⟩))
        (Compiler.Expression.atom ⟨98, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨62, by decide⟩))
      (Compiler.Expression.atom ⟨212, by decide⟩))

def sharedExpression719 : Compiler.Expression 323 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨57, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨59, by decide⟩))
              (Compiler.Expression.atom ⟨98, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨60, by decide⟩))
            (Compiler.Expression.atom ⟨98, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨61, by decide⟩))
          (Compiler.Expression.atom ⟨98, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨62, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨212, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨64, by decide⟩))
      (Compiler.Expression.atom ⟨215, by decide⟩))

def native.originalProjection (index : Nat) : Fin 276 :=
  if bound : index < 216 then ⟨index, Nat.lt_of_lt_of_le bound (by decide)⟩ else ⟨0, by decide⟩

def native.readProjection : List (Fin 276 × Fin 276) :=
  [(⟨238, by decide⟩, ⟨239, by decide⟩), (⟨240, by decide⟩, ⟨241, by decide⟩), (⟨242, by decide⟩, ⟨243, by decide⟩),
    (⟨244, by decide⟩, ⟨245, by decide⟩), (⟨246, by decide⟩, ⟨247, by decide⟩), (⟨248, by decide⟩, ⟨249, by decide⟩),
    (⟨250, by decide⟩, ⟨251, by decide⟩), (⟨252, by decide⟩, ⟨253, by decide⟩), (⟨254, by decide⟩, ⟨255, by decide⟩),
    (⟨256, by decide⟩, ⟨257, by decide⟩), (⟨258, by decide⟩, ⟨259, by decide⟩), (⟨260, by decide⟩, ⟨261, by decide⟩),
    (⟨262, by decide⟩, ⟨263, by decide⟩), (⟨264, by decide⟩, ⟨265, by decide⟩), (⟨266, by decide⟩, ⟨267, by decide⟩),
    (⟨268, by decide⟩, ⟨269, by decide⟩), (⟨270, by decide⟩, ⟨271, by decide⟩), (⟨272, by decide⟩, ⟨273, by decide⟩),
    (⟨274, by decide⟩, ⟨275, by decide⟩)]

def native.borrowProjection : List (Fin 276) :=
  [⟨216, by decide⟩, ⟨217, by decide⟩, ⟨218, by decide⟩, ⟨219, by decide⟩, ⟨220, by decide⟩, ⟨221, by decide⟩,
    ⟨222, by decide⟩, ⟨223, by decide⟩, ⟨224, by decide⟩, ⟨225, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩,
    ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨231, by decide⟩, ⟨232, by decide⟩, ⟨233, by decide⟩,
    ⟨234, by decide⟩]

def native.helperPlacement : Source.HelperPlacement 276 :=
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
    Source.HelperAssertion.boolean (Source.HelperField.borrow 13),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 14),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 15),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 16),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 17),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 18)]

theorem native.helperReferencesValid :
    (native.helperAssertions).all
        (fun assertion =>
          match assertion with
          | .zero field | .boolean field => field.referencesValid 216 19 0 19 false) =
      true :=
  by decide +kernel

def sharedExpression720 : Compiler.Expression 276 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨59, by decide⟩))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨60, by decide⟩))
                  (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400))))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨61, by decide⟩))
                (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400))))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨62, by decide⟩))
              (Compiler.Expression.constant ((134217711 : ZMod babyBearModulus) * 943718400))))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨63, by decide⟩))
            (Compiler.Expression.constant ((268435422 : ZMod babyBearModulus) * 943718400))))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.constant ((536870844 : ZMod babyBearModulus) * 943718400))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
        (Compiler.Expression.constant ((1073741688 : ZMod babyBearModulus) * 943718400))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.constant ((134217455 : ZMod babyBearModulus) * 943718400)))
end Airbender.Compiler.FullArithmeticNative.BigintCached
