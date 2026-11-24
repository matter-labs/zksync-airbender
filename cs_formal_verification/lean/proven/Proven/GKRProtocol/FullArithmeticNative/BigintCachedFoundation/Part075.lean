module
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part000
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part068
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part069
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part070
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part071
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part072
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part073
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part074
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.gate162 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨221, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨221, by decide⟩))
        (Compiler.Expression.atom ⟨221, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨221, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨221, by decide⟩)))

def native.gate163 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨222, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨222, by decide⟩))
        (Compiler.Expression.atom ⟨222, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨222, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨222, by decide⟩)))

def native.gate164 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨223, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨223, by decide⟩))
        (Compiler.Expression.atom ⟨223, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨223, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨223, by decide⟩)))

def native.gate165 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨224, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨224, by decide⟩))
        (Compiler.Expression.atom ⟨224, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨224, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨224, by decide⟩)))

def native.gate166 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨225, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨225, by decide⟩))
        (Compiler.Expression.atom ⟨225, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨225, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨225, by decide⟩)))

def native.gate167 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨226, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨226, by decide⟩))
        (Compiler.Expression.atom ⟨226, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨226, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨226, by decide⟩)))

def native.gate168 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨227, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨227, by decide⟩))
        (Compiler.Expression.atom ⟨227, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨227, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨227, by decide⟩)))

def native.gate169 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨228, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨228, by decide⟩))
        (Compiler.Expression.atom ⟨228, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨228, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨228, by decide⟩)))

def native.gate170 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨229, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨229, by decide⟩))
        (Compiler.Expression.atom ⟨229, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨229, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨229, by decide⟩)))

def native.gate171 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨230, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨230, by decide⟩))
        (Compiler.Expression.atom ⟨230, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨230, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨230, by decide⟩)))

def native.gate172 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨231, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨231, by decide⟩))
        (Compiler.Expression.atom ⟨231, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨231, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨231, by decide⟩)))

def native.gate173 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨232, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨232, by decide⟩))
        (Compiler.Expression.atom ⟨232, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨232, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨232, by decide⟩)))

def native.gate174 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨233, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨233, by decide⟩))
        (Compiler.Expression.atom ⟨233, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨233, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨233, by decide⟩)))

def native.gate175 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨234, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨234, by decide⟩))
        (Compiler.Expression.atom ⟨234, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨234, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨234, by decide⟩)))

def native.gate176 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨278, by decide⟩ ⟨276, by decide⟩

def native.gate177 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨210, by decide⟩))
        (Compiler.Expression.atom ⟨214, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨210, by decide⟩))
      (Compiler.Expression.atom ⟨214, by decide⟩))

def native.gate178 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨214, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨210, by decide⟩))
        (Compiler.Expression.atom ⟨213, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨214, by decide⟩))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨210, by decide⟩))
        (Compiler.Expression.atom ⟨213, by decide⟩)))

def native.gate179 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨279, by decide⟩ ⟨278, by decide⟩

def native.gate180 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨280, by decide⟩ ⟨279, by decide⟩

def native.gate181 : ArithmeticGate 323 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨281, by decide⟩ ⟨280, by decide⟩

def native.extensionData : Vector (Polynomial 276 Source.BaseField) 47 :=
  #v[[((1 : ZMod babyBearModulus), [⟨0, by decide⟩])], [((1 : ZMod babyBearModulus), [⟨162, by decide⟩])],
    [((1 : ZMod babyBearModulus), [⟨0, by decide⟩])], [((1 : ZMod babyBearModulus), [⟨0, by decide⟩])],
    [((1 : ZMod babyBearModulus), [⟨0, by decide⟩])], [((1 : ZMod babyBearModulus), [⟨0, by decide⟩])],
    [((503316480 : ZMod babyBearModulus), [⟨0, by decide⟩]),
      ((1509949441 : ZMod babyBearModulus), [⟨1, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨216, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨238, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨216, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨239, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨217, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨240, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨217, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨241, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨218, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨242, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨218, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨243, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨219, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨244, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨219, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨245, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨220, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨246, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨220, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨247, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨221, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨248, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨221, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨249, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨222, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨250, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨222, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨251, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨223, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨252, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨223, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨253, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨224, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨254, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨224, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨255, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨225, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨256, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨225, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨257, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨226, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨258, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨226, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨259, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨227, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨260, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨227, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨261, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨228, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨262, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨228, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨263, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨229, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨264, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨229, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨265, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨230, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨266, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨230, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨267, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨231, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨268, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨231, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨269, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨232, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨270, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨232, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨271, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨233, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨272, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨233, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨273, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨234, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨274, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨234, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨275, by decide⟩])],
    [((1950351361 : ZMod babyBearModulus), [⟨3, by decide⟩])],
    [((1950351361 : ZMod babyBearModulus), [⟨37, by decide⟩])]]

def native.extension (index : Fin 323) : Polynomial 276 Source.BaseField :=
  initialExtension (by decide : 276 ≤ 323) (fun coordinate => (native.extensionData)[coordinate]) index

noncomputable def native.artifact : ArithmeticExtension 276 323 Source.BaseField :=
  ⟨native.source,
    [native.gate0, native.gate1, native.gate2, native.gate3, native.gate4, native.gate5, native.gate6, native.gate7,
      native.gate8, native.gate9, native.gate10, native.gate11, native.gate12, native.gate13, native.gate14,
      native.gate15, native.gate16, native.gate17, native.gate18, native.gate19, native.gate20, native.gate21,
      native.gate22, native.gate23, native.gate24, native.gate25, native.gate26, native.gate27, native.gate28,
      native.gate29, native.gate30, native.gate31, native.gate32, native.gate33, native.gate34, native.gate35,
      native.gate36, native.gate37, native.gate38, native.gate39, native.gate40, native.gate41, native.gate42,
      native.gate43, native.gate44, native.gate45, native.gate46, native.gate47, native.gate48, native.gate49,
      native.gate50, native.gate51, native.gate52, native.gate53, native.gate54, native.gate55, native.gate56,
      native.gate57, native.gate58, native.gate59, native.gate60, native.gate61, native.gate62, native.gate63,
      native.gate64, native.gate65, native.gate66, native.gate67, native.gate68, native.gate69, native.gate70,
      native.gate71, native.gate72, native.gate73, native.gate74, native.gate75, native.gate76, native.gate77,
      native.gate78, native.gate79, native.gate80, native.gate81, native.gate82, native.gate83, native.gate84,
      native.gate85, native.gate86, native.gate87, native.gate88, native.gate89, native.gate90, native.gate91,
      native.gate92, native.gate93, native.gate94, native.gate95, native.gate96, native.gate97, native.gate98,
      native.gate99, native.gate100, native.gate101, native.gate102, native.gate103, native.gate104, native.gate105,
      native.gate106, native.gate107, native.gate108, native.gate109, native.gate110, native.gate111, native.gate112,
      native.gate113, native.gate114, native.gate115, native.gate116, native.gate117, native.gate118, native.gate119,
      native.gate120, native.gate121, native.gate122, native.gate123, native.gate124, native.gate125, native.gate126,
      native.gate127, native.gate128, native.gate129, native.gate130, native.gate131, native.gate132, native.gate133,
      native.gate134, native.gate135, native.gate136, native.gate137, native.gate138, native.gate139, native.gate140,
      native.gate141, native.gate142, native.gate143, native.gate144, native.gate145, native.gate146, native.gate147,
      native.gate148, native.gate149, native.gate150, native.gate151, native.gate152, native.gate153, native.gate154,
      native.gate155, native.gate156, native.gate157, native.gate158, native.gate159, native.gate160, native.gate161,
      native.gate162, native.gate163, native.gate164, native.gate165, native.gate166, native.gate167, native.gate168,
      native.gate169, native.gate170, native.gate171, native.gate172, native.gate173, native.gate174, native.gate175,
      native.gate176, native.gate177, native.gate178, native.gate179, native.gate180, native.gate181],
    (fun index : Fin 276 => index.castLE (by decide : 276 ≤ 323)), native.extension⟩

theorem native.inputCoordinates (wire : Fin 276) :
    (native.bank).address ((native.artifact).projection wire) = (native.inputBank).address wire :=
  WireBank.ofList_prefix native.addresses native.inputs (by decide) (by decide) (by decide) native.inputPrefix wire
end Airbender.Compiler.FullArithmeticNative.BigintCached
