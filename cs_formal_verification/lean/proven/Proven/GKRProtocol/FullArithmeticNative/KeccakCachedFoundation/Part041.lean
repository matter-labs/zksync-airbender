module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part011
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part012
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part013
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part014
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part015
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part016
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part017
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part018
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part019
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.gate79 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression196
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨159, by decide⟩)))
    sharedExpression197

def native.gate80 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression201
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨166, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨167, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨168, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression203
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨159, by decide⟩))
            (Compiler.Expression.atom ⟨168, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨161, by decide⟩))
            (Compiler.Expression.atom ⟨166, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨81, by decide⟩))))

def native.gate81 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression211 sharedExpression214

def native.gate82 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression217
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨161, by decide⟩)))
    sharedExpression218

def native.gate83 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression223
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((544 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨169, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression225
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨160, by decide⟩))
            (Compiler.Expression.atom ⟨169, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨158, by decide⟩))
            (Compiler.Expression.atom ⟨167, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨81, by decide⟩))))

def native.gate84 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression233 sharedExpression236

def native.gate85 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression239
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨163, by decide⟩)))
    sharedExpression240

def native.gate86 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression245
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨166, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨170, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨171, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression247
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨161, by decide⟩))
            (Compiler.Expression.atom ⟨166, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨159, by decide⟩))
            (Compiler.Expression.atom ⟨168, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨81, by decide⟩))))

def native.gate87 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression255 sharedExpression258

def native.gate88 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression261
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨165, by decide⟩)))
    sharedExpression262

def native.gate89 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression267
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨167, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨172, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨173, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression269
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨158, by decide⟩))
            (Compiler.Expression.atom ⟨167, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨160, by decide⟩))
            (Compiler.Expression.atom ⟨169, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨81, by decide⟩))))

def native.gate90 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨67, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨80, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨82, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨83, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨84, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨67, by decide⟩))
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
          (Compiler.Expression.atom ⟨84, by decide⟩))))

def native.gate91 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression275 sharedExpression278

def native.gate92 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression281
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨183, by decide⟩)))
    sharedExpression282

def native.gate93 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression286
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨83, by decide⟩))
            (Compiler.Expression.atom ⟨193, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨185, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨191, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression288
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨183, by decide⟩))
            (Compiler.Expression.atom ⟨192, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨185, by decide⟩))
            (Compiler.Expression.atom ⟨190, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨84, by decide⟩))))

def native.gate94 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression296 sharedExpression299

def native.gate95 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression302
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨185, by decide⟩)))
    sharedExpression303

def native.gate96 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression308
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨193, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression310
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨184, by decide⟩))
            (Compiler.Expression.atom ⟨193, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨182, by decide⟩))
            (Compiler.Expression.atom ⟨191, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨84, by decide⟩))))

def native.gate97 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression318 sharedExpression321

def native.gate98 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression324
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨187, by decide⟩)))
    sharedExpression325

def native.gate99 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression330
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨192, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨194, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨195, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression332
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨185, by decide⟩))
            (Compiler.Expression.atom ⟨190, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨183, by decide⟩))
            (Compiler.Expression.atom ⟨192, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨84, by decide⟩))))

def native.gate100 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression340 sharedExpression343

def native.gate101 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression346
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨189, by decide⟩)))
    sharedExpression347

def native.gate102 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression352
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨193, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨196, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨197, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression354
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨182, by decide⟩))
            (Compiler.Expression.atom ⟨191, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨184, by decide⟩))
            (Compiler.Expression.atom ⟨193, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨84, by decide⟩))))
end Airbender.Compiler.FullArithmeticNative.KeccakCached
