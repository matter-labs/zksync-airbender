module
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part040
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part041
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part042
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def sharedExpression1054 : Compiler.Expression 276 Source.BaseField :=
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
                      (Compiler.Expression.atom ⟨81, by decide⟩))
                    (Compiler.Expression.atom ⟨59, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨81, by decide⟩))
                  (Compiler.Expression.atom ⟨60, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨81, by decide⟩))
                (Compiler.Expression.atom ⟨61, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨33, by decide⟩))
              (Compiler.Expression.atom ⟨64, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨145, by decide⟩))
            (Compiler.Expression.atom ⟨62, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨161, by decide⟩))
          (Compiler.Expression.atom ⟨63, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨81, by decide⟩))
        (Compiler.Expression.atom ⟨66, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨35, by decide⟩))

def sharedExpression1055 : Compiler.Expression 276 Source.BaseField :=
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
                      (Compiler.Expression.atom ⟨82, by decide⟩))
                    (Compiler.Expression.atom ⟨59, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨60, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨82, by decide⟩))
                (Compiler.Expression.atom ⟨61, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨34, by decide⟩))
              (Compiler.Expression.atom ⟨64, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨146, by decide⟩))
            (Compiler.Expression.atom ⟨62, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨162, by decide⟩))
          (Compiler.Expression.atom ⟨63, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.atom ⟨66, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨36, by decide⟩))

def sharedExpression1056 : Compiler.Expression 276 Source.BaseField :=
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
                      (Compiler.Expression.atom ⟨67, by decide⟩))
                    (Compiler.Expression.atom ⟨64, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨147, by decide⟩))
                  (Compiler.Expression.atom ⟨62, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨68, by decide⟩))
                (Compiler.Expression.atom ⟨64, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨148, by decide⟩))
              (Compiler.Expression.atom ⟨62, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨69, by decide⟩))
            (Compiler.Expression.atom ⟨64, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨149, by decide⟩))
          (Compiler.Expression.atom ⟨62, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨70, by decide⟩))
        (Compiler.Expression.atom ⟨64, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨150, by decide⟩))
      (Compiler.Expression.atom ⟨62, by decide⟩))

def sharedExpression1057 : Compiler.Expression 276 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add sharedExpression1056
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.atom ⟨71, by decide⟩))
                    (Compiler.Expression.atom ⟨64, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨151, by decide⟩))
                  (Compiler.Expression.atom ⟨62, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨72, by decide⟩))
                (Compiler.Expression.atom ⟨64, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨152, by decide⟩))
              (Compiler.Expression.atom ⟨62, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨73, by decide⟩))
            (Compiler.Expression.atom ⟨64, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨153, by decide⟩))
          (Compiler.Expression.atom ⟨62, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨74, by decide⟩))
        (Compiler.Expression.atom ⟨64, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨154, by decide⟩))
      (Compiler.Expression.atom ⟨62, by decide⟩))

def sharedExpression1058 : Compiler.Expression 276 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add sharedExpression1057
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.atom ⟨75, by decide⟩))
                    (Compiler.Expression.atom ⟨64, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨155, by decide⟩))
                  (Compiler.Expression.atom ⟨62, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨76, by decide⟩))
                (Compiler.Expression.atom ⟨64, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨156, by decide⟩))
              (Compiler.Expression.atom ⟨62, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨77, by decide⟩))
            (Compiler.Expression.atom ⟨64, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨157, by decide⟩))
          (Compiler.Expression.atom ⟨62, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨78, by decide⟩))
        (Compiler.Expression.atom ⟨64, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨158, by decide⟩))
      (Compiler.Expression.atom ⟨62, by decide⟩))

def sharedExpression1059 : Compiler.Expression 276 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add sharedExpression1058
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.atom ⟨79, by decide⟩))
                    (Compiler.Expression.atom ⟨64, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨159, by decide⟩))
                  (Compiler.Expression.atom ⟨62, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨80, by decide⟩))
                (Compiler.Expression.atom ⟨64, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨160, by decide⟩))
              (Compiler.Expression.atom ⟨62, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨64, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨161, by decide⟩))
          (Compiler.Expression.atom ⟨62, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.atom ⟨64, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨162, by decide⟩))
      (Compiler.Expression.atom ⟨62, by decide⟩))

def sharedExpression1060 : Compiler.Expression 276 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0)
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨98, by decide⟩))
                  (Compiler.Expression.atom ⟨59, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨98, by decide⟩))
                (Compiler.Expression.atom ⟨60, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨98, by decide⟩))
              (Compiler.Expression.atom ⟨61, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨215, by decide⟩))
            (Compiler.Expression.atom ⟨64, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0)
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨212, by decide⟩))))
          (Compiler.Expression.atom ⟨62, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨98, by decide⟩))
        (Compiler.Expression.atom ⟨66, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨57, by decide⟩))

def native.originalExpression0 : Expression 276 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨0, by decide⟩))
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))))
    (Compiler.Expression.atom ⟨0, by decide⟩)

def native.originalExpression1 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression720
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨55, by decide⟩))

def native.originalExpression2 : Expression 276 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨59, by decide⟩))
                  (Compiler.Expression.atom ⟨60, by decide⟩))
                (Compiler.Expression.atom ⟨61, by decide⟩))
              (Compiler.Expression.atom ⟨62, by decide⟩))
            (Compiler.Expression.atom ⟨63, by decide⟩))
          (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨66, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨59, by decide⟩))
                  (Compiler.Expression.atom ⟨60, by decide⟩))
                (Compiler.Expression.atom ⟨61, by decide⟩))
              (Compiler.Expression.atom ⟨62, by decide⟩))
            (Compiler.Expression.atom ⟨63, by decide⟩))
          (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨66, by decide⟩))
      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))

def native.originalExpression3 : Expression 276 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression722
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨60, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
          (Compiler.Expression.atom ⟨61, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨65, by decide⟩))
        (Compiler.Expression.atom ⟨66, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744970275 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨83, by decide⟩))

def native.originalExpression4 : Expression 276 Source.BaseField :=
  sharedExpression724

def native.originalExpression5 : Expression 276 Source.BaseField :=
  sharedExpression726

def native.originalExpression6 : Expression 276 Source.BaseField :=
  sharedExpression728

def native.originalExpression7 : Expression 276 Source.BaseField :=
  sharedExpression730

def native.originalExpression8 : Expression 276 Source.BaseField :=
  sharedExpression732

def native.originalExpression9 : Expression 276 Source.BaseField :=
  sharedExpression734

def native.originalExpression10 : Expression 276 Source.BaseField :=
  sharedExpression736

def native.originalExpression11 : Expression 276 Source.BaseField :=
  sharedExpression738

def native.originalExpression12 : Expression 276 Source.BaseField :=
  sharedExpression740

def native.originalExpression13 : Expression 276 Source.BaseField :=
  sharedExpression742

def native.originalExpression14 : Expression 276 Source.BaseField :=
  sharedExpression744

def native.originalExpression15 : Expression 276 Source.BaseField :=
  sharedExpression746

def native.originalExpression16 : Expression 276 Source.BaseField :=
  sharedExpression748
end Airbender.Compiler.FullArithmeticNative.BigintCached
