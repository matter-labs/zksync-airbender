module
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part042
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part043
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part044
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part045
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part046
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part047
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part048
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part049
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part051
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part052
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part053
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part054
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part055
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part056
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part057
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression17 : Expression 276 Source.BaseField :=
  sharedExpression750

def native.originalExpression18 : Expression 276 Source.BaseField :=
  sharedExpression752

def native.originalExpression19 : Expression 276 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨99, by decide⟩))
            (Compiler.Expression.atom ⟨115, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨99, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨39, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨115, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨5, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨99, by decide⟩))))
        (Compiler.Expression.atom ⟨115, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨163, by decide⟩))

def native.originalExpression20 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression754
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨164, by decide⟩))

def native.originalExpression21 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression757
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨165, by decide⟩))

def native.originalExpression22 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression761
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨166, by decide⟩))

def native.originalExpression23 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression766
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨167, by decide⟩))

def native.originalExpression24 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression772
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨168, by decide⟩))

def native.originalExpression25 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression779
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨169, by decide⟩))

def native.originalExpression26 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression787
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨170, by decide⟩))

def native.originalExpression27 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression796
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨171, by decide⟩))

def native.originalExpression28 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression806
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨172, by decide⟩))

def native.originalExpression29 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression817
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨173, by decide⟩))

def native.originalExpression30 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression829
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨174, by decide⟩))

def native.originalExpression31 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression842
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨175, by decide⟩))

def native.originalExpression32 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression856
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨176, by decide⟩))

def native.originalExpression33 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression871
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨177, by decide⟩))

def native.originalExpression34 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression887
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨178, by decide⟩))

def native.originalExpression35 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression903
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨179, by decide⟩))

def native.originalExpression36 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression918
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨180, by decide⟩))

def native.originalExpression37 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression932
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨181, by decide⟩))

def native.originalExpression38 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression945
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨182, by decide⟩))

def native.originalExpression39 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression957
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨183, by decide⟩))

def native.originalExpression40 : Expression 276 Source.BaseField :=
  Compiler.Expression.add sharedExpression968
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨184, by decide⟩))
end Airbender.Compiler.FullArithmeticNative.BigintCached
