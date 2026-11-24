module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part003
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part008
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part017
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericData.Part018
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation
public import Proven.Import.GKRProtocol.NumericExpressionDataImport
public import Proven.GKRProtocol.FastNumericNormalization

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

open NumericPolynomialChecks

def numericSourceExpressions.part004 : List NumericExpressionChecks.Code := [NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 59))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 61))))
      (NumericExpressionChecks.Code.atom 65),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 60))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 62))))
      (NumericExpressionChecks.Code.atom 65),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 55))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 57))))
      (NumericExpressionChecks.Code.atom 66),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 56))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 58))))
      (NumericExpressionChecks.Code.atom 66),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 59))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 61))))
      (NumericExpressionChecks.Code.atom 66),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 60))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 62))))
      (NumericExpressionChecks.Code.atom 66),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 55))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 57))))
      (NumericExpressionChecks.Code.atom 67),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 56))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 58))))
      (NumericExpressionChecks.Code.atom 67),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 59))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 61))))
      (NumericExpressionChecks.Code.atom 67),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 60))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 62))))
      (NumericExpressionChecks.Code.atom 67),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 15))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 57))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 16))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 58))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 19))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 61))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 20))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 62))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 31))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 33))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 32))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 34))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 35))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 37))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 36))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 38))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 39))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 41))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 40))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 42))))
      (NumericExpressionChecks.Code.atom 68)]

def numericSourceExpressions.part005 : List NumericExpressionChecks.Code := [NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 43))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 45))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 44))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 46))))
      (NumericExpressionChecks.Code.atom 68),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 39))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 41))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 40))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 42))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 43))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 45))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 44))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 46))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 47))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 49))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 48))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 50))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 51))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 53))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 52))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 54))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 55))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 57))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 56))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 58))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 59))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 61))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul
      (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
        (NumericExpressionChecks.Code.add
          (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.constant 0)
            (NumericExpressionChecks.Code.atom 60))
          (NumericExpressionChecks.Code.mul
            (NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.constant 1)
              (NumericExpressionChecks.Code.constant 2013265920))
            (NumericExpressionChecks.Code.atom 62))))
      (NumericExpressionChecks.Code.atom 69),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 63)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 63)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 64)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 64)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 65)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 65)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 66)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 66)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 67)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 67)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 68)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 68)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 69)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 69)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 70)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 70)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 71)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 71)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 72)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 72)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 73)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 73)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 74)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 74)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 75)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 75)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 76)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 76)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 77)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 77)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 78)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 78)
        (NumericExpressionChecks.Code.constant 2013265920)),
NumericExpressionChecks.Code.mul (NumericExpressionChecks.Code.atom 79)
      (NumericExpressionChecks.Code.add (NumericExpressionChecks.Code.atom 79)
        (NumericExpressionChecks.Code.constant 2013265920))]

def numericSourceExpressions : List NumericExpressionChecks.Code := numericSourceExpressions.part000 ++ numericSourceExpressions.part001 ++ numericSourceExpressions.part002 ++ numericSourceExpressions.part003 ++ numericSourceExpressions.part004 ++ numericSourceExpressions.part005

def originalSourceExpressions : List (Expression 266 Source.BaseField) := [native.originalExpression0, native.originalExpression1, native.originalExpression2, native.originalExpression3, native.originalExpression4, native.originalExpression5, native.originalExpression6, native.originalExpression7, native.originalExpression8, native.originalExpression9, native.originalExpression10, native.originalExpression11, native.originalExpression12, native.originalExpression13, native.originalExpression14, native.originalExpression15, native.originalExpression16, native.originalExpression17, native.originalExpression18, native.originalExpression19, native.originalExpression20, native.originalExpression21, native.originalExpression22, native.originalExpression23, native.originalExpression24, native.originalExpression25, native.originalExpression26, native.originalExpression27, native.originalExpression28, native.originalExpression29, native.originalExpression30, native.originalExpression31, native.originalExpression32, native.originalExpression33, native.originalExpression34, native.originalExpression35, native.originalExpression36, native.originalExpression37, native.originalExpression38, native.originalExpression39, native.originalExpression40, native.originalExpression41, native.originalExpression42, native.originalExpression43, native.originalExpression44, native.originalExpression45, native.originalExpression46, native.originalExpression47, native.originalExpression48, native.originalExpression49, native.originalExpression50, native.originalExpression51, native.originalExpression52, native.originalExpression53, native.originalExpression54, native.originalExpression55, native.originalExpression56, native.originalExpression57, native.originalExpression58, native.originalExpression59, native.originalExpression60, native.originalExpression61, native.originalExpression62, native.originalExpression63, native.originalExpression64, native.originalExpression65, native.originalExpression66, native.originalExpression67, native.originalExpression68, native.originalExpression69, native.originalExpression70, native.originalExpression71, native.originalExpression72, native.originalExpression73, native.originalExpression74, native.originalExpression75, native.originalExpression76, native.originalExpression77, native.originalExpression78, native.originalExpression79, native.originalExpression80, native.originalExpression81, native.originalExpression82, native.originalExpression83, native.originalExpression84, native.originalExpression85, native.originalExpression86, native.originalExpression87, native.originalExpression88, native.originalExpression89, native.originalExpression90, native.originalExpression91, native.originalExpression92, native.originalExpression93, native.originalExpression94, native.originalExpression95, native.originalExpression96, native.originalExpression97, native.originalExpression98, native.originalExpression99, native.originalExpression100, native.originalExpression101, native.originalExpression102, native.originalExpression103, native.originalExpression104, native.originalExpression105, native.originalExpression106, native.originalExpression107, native.originalExpression108, native.originalExpression109, native.originalExpression110, native.originalExpression111, native.originalExpression112, native.originalExpression113, native.originalExpression114, native.originalExpression115, native.originalExpression116, native.originalExpression117, native.originalExpression118, native.originalExpression119, native.originalExpression120, native.originalExpression121, native.originalExpression122, native.originalExpression123, native.originalExpression124, native.originalExpression125, native.originalExpression126, native.originalExpression127, native.originalExpression128, native.originalExpression129, native.originalExpression130, native.originalExpression131, native.originalExpression132, native.originalExpression133, native.originalExpression134, native.originalExpression135, native.originalExpression136, native.originalExpression137, native.originalExpression138, native.originalExpression139, native.originalExpression140, native.originalExpression141, native.originalExpression142, native.originalExpression143, native.originalExpression144, native.originalExpression145, native.originalExpression146, native.originalExpression147, native.originalExpression148, native.originalExpression149, native.originalExpression150, native.originalExpression151, native.originalExpression152, native.originalExpression153, native.originalExpression154, native.originalExpression155, native.originalExpression156, native.originalExpression157, native.originalExpression158, native.originalExpression159, native.originalExpression160, native.originalExpression161, native.originalExpression162, native.originalExpression163, native.originalExpression164, native.originalExpression165, native.originalExpression166, native.originalExpression167, native.originalExpression168, native.originalExpression169, native.originalExpression170, native.originalExpression171, native.originalExpression172]

theorem sourceExpressionLayout :
    native.artifact.source =
      originalSourceExpressions.map Expression.polynomial ++
        native.helperAssertions.map (Source.HelperAssertion.polynomial native.helperPlacement) := by kernel_rfl

theorem numericSourceExpressions_binding :
    originalSourceExpressions.map NumericExpressionChecks.encode = numericSourceExpressions := by kernel_rfl

theorem numericSourceHelpers_binding :
    (native.helperAssertions.map (Source.HelperAssertion.polynomial native.helperPlacement)).map encode =
      numericSourceHelpers := by kernel_rfl

theorem numericSourceExpansion_binding :
    numericSourceExpressions.map (NumericExpressionChecks.Code.polynomial babyBearModulus) ++ numericSourceHelpers =
      numericSource := by kernel_rfl

def numericNormalizedSource.leaf0 : List NumericPolynomialChecks.Data :=
  [[((2013265920 : Nat), [0]), ((1 : Nat), [0, 0])], [((1 : Nat), [4])], [((1 : Nat), [6])],
    [((2013265920 : Nat), [3]), ((1 : Nat), [64]), ((2 : Nat), [65]), ((3 : Nat), [66]), ((4 : Nat), [67]),
      ((5 : Nat), [68]), ((6 : Nat), [69]), ((8 : Nat), [71]), ((16 : Nat), [72]), ((24 : Nat), [73]),
      ((32 : Nat), [74]), ((64 : Nat), [75]), ((128 : Nat), [76]), ((256 : Nat), [77]), ((512 : Nat), [78]),
      ((1024 : Nat), [79])],
    [((2013265920 : Nat), [0]), ((1 : Nat), [0, 63]), ((1 : Nat), [0, 64]), ((1 : Nat), [0, 65]),
      ((1 : Nat), [0, 66]), ((1 : Nat), [0, 67]), ((1 : Nat), [0, 68]), ((1 : Nat), [0, 69])],
    [((2013265920 : Nat), [0]), ((1 : Nat), [0, 70]), ((1 : Nat), [0, 71]), ((1 : Nat), [0, 72]),
      ((1 : Nat), [0, 73]), ((1 : Nat), [0, 74])],
    [((2013265920 : Nat), [0, 63]), ((2013265920 : Nat), [0, 64]), ((2013265920 : Nat), [0, 65]),
      ((2013265920 : Nat), [0, 66]), ((2013265920 : Nat), [0, 67]), ((2013265920 : Nat), [0, 68]),
      ((2013265920 : Nat), [0, 69]), ((1 : Nat), [63]), ((1 : Nat), [64]), ((1 : Nat), [65]), ((1 : Nat), [66]),
      ((1 : Nat), [67]), ((1 : Nat), [68]), ((1 : Nat), [69])],
    [((2013265920 : Nat), [0, 70]), ((2013265920 : Nat), [0, 71]), ((2013265920 : Nat), [0, 72]),
      ((2013265920 : Nat), [0, 73]), ((2013265920 : Nat), [0, 74]), ((1 : Nat), [70]), ((1 : Nat), [71]),
      ((1 : Nat), [72]), ((1 : Nat), [73]), ((1 : Nat), [74])],
    [((2013265920 : Nat), [5]), ((8 : Nat), [63]), ((2013265882 : Nat), [63, 74]), ((2 : Nat), [64]),
      ((3 : Nat), [65]), ((11 : Nat), [66]), ((2013265882 : Nat), [66, 74]), ((12 : Nat), [67]),
      ((2013265882 : Nat), [67, 74]), ((6 : Nat), [68]), ((13 : Nat), [69]), ((19 : Nat), [69, 74]),
      ((8 : Nat), [71]), ((16 : Nat), [72]), ((24 : Nat), [73]), ((32 : Nat), [74]), ((64 : Nat), [75]),
      ((128 : Nat), [76]), ((256 : Nat), [77]), ((512 : Nat), [78]), ((1024 : Nat), [79])],
    [((1 : Nat), [67, 70]), ((2013265920 : Nat), [80])], [((1 : Nat), [67, 71]), ((2013265920 : Nat), [81])],
    [((1 : Nat), [67, 72]), ((2013265920 : Nat), [82])], [((1 : Nat), [67, 73]), ((2013265920 : Nat), [83])],
    [((1 : Nat), [67, 74]), ((2013265920 : Nat), [84])],
    [((1 : Nat), [70, 75]), ((2 : Nat), [70, 76]), ((4 : Nat), [70, 77]), ((8 : Nat), [70, 78]),
      ((16 : Nat), [70, 79]), ((2013265920 : Nat), [85])],
    [((8192 : Nat), []), ((257 : Nat), [85]), ((2013265920 : Nat), [86])]]
end Airbender.Compiler.FullArithmeticNative.KeccakCached
