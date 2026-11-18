module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part002
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part003
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part004
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part005
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part006
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part007
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part008
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part009
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part010
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.gate55 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression41
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨103, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨104, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨105, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.add (Compiler.Expression.constant 0) sharedExpression42)
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
                          (Compiler.Expression.add
                            (Compiler.Expression.add (Compiler.Expression.constant 0)
                              (Compiler.Expression.atom ⟨64, by decide⟩))
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨82, by decide⟩))
                    (Compiler.Expression.atom ⟨83, by decide⟩))
                  (Compiler.Expression.atom ⟨84, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨104, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨105, by decide⟩)))))
      sharedExpression43)

def native.gate56 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression46
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨112, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨113, by decide⟩)))
    sharedExpression47

def native.gate57 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression52
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨83, by decide⟩))
                (Compiler.Expression.atom ⟨121, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨84, by decide⟩))
              (Compiler.Expression.atom ⟨113, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨118, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨120, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨121, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression54
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨113, by decide⟩))
            (Compiler.Expression.atom ⟨118, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨110, by decide⟩))
            (Compiler.Expression.atom ⟨119, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨81, by decide⟩))))

def native.gate58 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression63
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨104, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨106, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨107, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.add (Compiler.Expression.constant 0) sharedExpression64)
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
                          (Compiler.Expression.add
                            (Compiler.Expression.add (Compiler.Expression.constant 0)
                              (Compiler.Expression.atom ⟨64, by decide⟩))
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨82, by decide⟩))
                    (Compiler.Expression.atom ⟨83, by decide⟩))
                  (Compiler.Expression.atom ⟨84, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨106, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨107, by decide⟩)))))
      sharedExpression65)

def native.gate59 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression68
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨114, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨115, by decide⟩)))
    sharedExpression69

def native.gate60 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression75
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨123, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression77
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨110, by decide⟩))
            (Compiler.Expression.atom ⟨119, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨111, by decide⟩))
            (Compiler.Expression.atom ⟨120, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨81, by decide⟩))))

def native.gate61 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression86
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨105, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨108, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨109, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.add (Compiler.Expression.constant 0) sharedExpression87)
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
                          (Compiler.Expression.add
                            (Compiler.Expression.add (Compiler.Expression.constant 0)
                              (Compiler.Expression.atom ⟨64, by decide⟩))
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨82, by decide⟩))
                    (Compiler.Expression.atom ⟨83, by decide⟩))
                  (Compiler.Expression.atom ⟨84, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨108, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨109, by decide⟩)))))
      sharedExpression88)

def native.gate62 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression91
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨116, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨117, by decide⟩)))
    sharedExpression92

def native.gate63 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression98
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨125, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression100
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨111, by decide⟩))
            (Compiler.Expression.atom ⟨120, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨112, by decide⟩))
            (Compiler.Expression.atom ⟨121, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨81, by decide⟩))))

def native.gate64 : ArithmeticGate 301 Source.BaseField :=
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

def native.gate65 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression106 sharedExpression109

def native.gate66 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression112
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨135, by decide⟩)))
    sharedExpression113

def native.gate67 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression117
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨84, by decide⟩))
              (Compiler.Expression.atom ⟨136, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨142, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨143, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨145, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression119
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.atom ⟨82, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨137, by decide⟩))
            (Compiler.Expression.atom ⟨142, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨135, by decide⟩))
          (Compiler.Expression.atom ⟨144, by decide⟩))))

def native.gate68 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression127 sharedExpression130

def native.gate69 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression133
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨137, by decide⟩)))
    sharedExpression134

def native.gate70 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression138
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨83, by decide⟩))
                (Compiler.Expression.atom ⟨145, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨84, by decide⟩))
              (Compiler.Expression.atom ⟨137, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨142, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨144, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨145, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression140
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.atom ⟨82, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨134, by decide⟩))
            (Compiler.Expression.atom ⟨143, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨136, by decide⟩))
          (Compiler.Expression.atom ⟨145, by decide⟩))))

def native.gate71 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression148 sharedExpression151

def native.gate72 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression154
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨139, by decide⟩)))
    sharedExpression155

def native.gate73 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression160
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨143, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨146, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨147, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression162
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.atom ⟨82, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨135, by decide⟩))
            (Compiler.Expression.atom ⟨144, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨137, by decide⟩))
          (Compiler.Expression.atom ⟨142, by decide⟩))))

def native.gate74 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression170 sharedExpression173

def native.gate75 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression176
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨141, by decide⟩)))
    sharedExpression177

def native.gate76 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression182
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨144, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨148, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨149, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression184
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.atom ⟨82, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨136, by decide⟩))
            (Compiler.Expression.atom ⟨145, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨134, by decide⟩))
          (Compiler.Expression.atom ⟨143, by decide⟩))))

def native.gate77 : ArithmeticGate 301 Source.BaseField :=
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
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨65, by decide⟩))
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
                    (Compiler.Expression.atom ⟨65, by decide⟩))
                  (Compiler.Expression.atom ⟨80, by decide⟩))
                (Compiler.Expression.atom ⟨81, by decide⟩))
              (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.atom ⟨84, by decide⟩))))

def native.gate78 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression190 sharedExpression193
end Airbender.Compiler.FullArithmeticNative.KeccakCached
