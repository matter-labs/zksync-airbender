module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part000
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part001
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part002
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.gate31 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨267, by decide⟩ ⟨268, by decide⟩

def native.gate32 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨0, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨0, by decide⟩))
        (Compiler.Expression.atom ⟨0, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨0, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨0, by decide⟩)))

def native.gate33 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨4, by decide⟩)))
    (Compiler.Expression.atom ⟨4, by decide⟩)

def native.gate34 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨6, by decide⟩)))
    (Compiler.Expression.atom ⟨6, by decide⟩)

def native.gate35 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression1
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression2
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1073741688 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨75, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨76, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨77, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((134217711 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨78, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268435422 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨79, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨3, by decide⟩)))

def native.gate36 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression3
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨68, by decide⟩))
          (Compiler.Expression.atom ⟨0, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.atom ⟨0, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨0, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add (Compiler.Expression.constant 0)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨63, by decide⟩))
                  (Compiler.Expression.atom ⟨64, by decide⟩))
                (Compiler.Expression.atom ⟨65, by decide⟩))
              (Compiler.Expression.atom ⟨66, by decide⟩))
            (Compiler.Expression.atom ⟨67, by decide⟩))
          (Compiler.Expression.atom ⟨68, by decide⟩))
        (Compiler.Expression.atom ⟨69, by decide⟩)))

def native.gate37 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression4
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨0, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨70, by decide⟩))
              (Compiler.Expression.atom ⟨71, by decide⟩))
            (Compiler.Expression.atom ⟨72, by decide⟩))
          (Compiler.Expression.atom ⟨73, by decide⟩))
        (Compiler.Expression.atom ⟨74, by decide⟩)))

def native.gate38 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression6
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨0, by decide⟩))))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨63, by decide⟩))
                  (Compiler.Expression.atom ⟨64, by decide⟩))
                (Compiler.Expression.atom ⟨65, by decide⟩))
              (Compiler.Expression.atom ⟨66, by decide⟩))
            (Compiler.Expression.atom ⟨67, by decide⟩))
          (Compiler.Expression.atom ⟨68, by decide⟩))
        (Compiler.Expression.atom ⟨69, by decide⟩)))

def native.gate39 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression7
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨72, by decide⟩))
            (Compiler.Expression.atom ⟨0, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨73, by decide⟩))
          (Compiler.Expression.atom ⟨0, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨74, by decide⟩))
        (Compiler.Expression.atom ⟨0, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨0, by decide⟩))))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨70, by decide⟩))
              (Compiler.Expression.atom ⟨71, by decide⟩))
            (Compiler.Expression.atom ⟨72, by decide⟩))
          (Compiler.Expression.atom ⟨73, by decide⟩))
        (Compiler.Expression.atom ⟨74, by decide⟩)))

def native.gate40 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression9
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨5, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1610612820 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨63, by decide⟩))
              (Compiler.Expression.atom ⟨74, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1610612820 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨66, by decide⟩))
            (Compiler.Expression.atom ⟨74, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1610612820 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨67, by decide⟩))
          (Compiler.Expression.atom ⟨74, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1073741784 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.atom ⟨74, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression12
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨74, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨63, by decide⟩))
              (Compiler.Expression.atom ⟨66, by decide⟩))
            (Compiler.Expression.atom ⟨67, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨69, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1342177270 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨74, by decide⟩)))))

def native.gate41 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨80, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨70, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨80, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨70, by decide⟩)))

def native.gate42 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨81, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨71, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨81, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨71, by decide⟩)))

def native.gate43 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨82, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨72, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨82, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨72, by decide⟩)))

def native.gate44 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨83, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨73, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨83, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨73, by decide⟩)))

def native.gate45 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨74, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨84, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨74, by decide⟩)))

def native.gate46 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero sharedExpression13
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨85, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨70, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨75, by decide⟩))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨76, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨77, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((134217711 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨78, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((268435422 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨79, by decide⟩)))))

def native.gate47 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((536853436 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((536870364 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨85, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨86, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨85, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((536870844 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨85, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨86, by decide⟩)))

def native.gate48 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((671036075 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((536870364 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨85, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨87, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((1073741688 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨85, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((1610612532 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨85, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨87, by decide⟩)))

def native.gate49 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((805218714 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((536870364 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨85, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨88, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((134217455 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨85, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((671088299 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨85, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨88, by decide⟩)))

def native.gate50 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((939401353 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((536870364 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨85, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨89, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((1207959143 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨85, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((1744829987 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨85, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨89, by decide⟩)))

def native.gate51 : ArithmeticGate 301 Source.BaseField :=
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
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
          (Compiler.Expression.atom ⟨65, by decide⟩))
        (Compiler.Expression.atom ⟨67, by decide⟩))
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
          (Compiler.Expression.atom ⟨84, by decide⟩))))

def native.gate52 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add sharedExpression20
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨103, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.add (Compiler.Expression.constant 0) sharedExpression21)
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
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨102, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨103, by decide⟩)))))
      sharedExpression22)

def native.gate53 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression25
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨110, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨111, by decide⟩)))
    sharedExpression26

def native.gate54 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression30
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨84, by decide⟩))
              (Compiler.Expression.atom ⟨112, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.atom ⟨118, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744831011 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨84, by decide⟩))
          (Compiler.Expression.atom ⟨119, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨84, by decide⟩))
        (Compiler.Expression.atom ⟨121, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression32
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨112, by decide⟩))
            (Compiler.Expression.atom ⟨121, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨113, by decide⟩))
            (Compiler.Expression.atom ⟨118, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
              (Compiler.Expression.atom ⟨65, by decide⟩))
            (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.atom ⟨81, by decide⟩))))
end Airbender.Compiler.FullArithmeticNative.KeccakCached
