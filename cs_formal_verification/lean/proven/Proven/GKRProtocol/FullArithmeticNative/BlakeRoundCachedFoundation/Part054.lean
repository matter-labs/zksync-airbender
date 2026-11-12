module
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part000
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part001
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part039
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part040
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part041
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part042
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part043
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part044
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part045
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part046
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part047
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part048
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part049
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part050
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part051
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part052
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part053
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.gate309 : ArithmeticGate 858 Source.BaseField :=
  Compiler.ArithmeticGate.assertZero
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨674, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨674, by decide⟩))
        (Compiler.Expression.atom ⟨674, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨674, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨674, by decide⟩)))

def native.gate310 : ArithmeticGate 858 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨764, by decide⟩ ⟨763, by decide⟩

def native.gate311 : ArithmeticGate 858 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨765, by decide⟩ ⟨764, by decide⟩

def native.gate312 : ArithmeticGate 858 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨766, by decide⟩ ⟨765, by decide⟩

def native.gate313 : ArithmeticGate 858 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨767, by decide⟩ ⟨766, by decide⟩

def native.gate314 : ArithmeticGate 858 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨768, by decide⟩ ⟨767, by decide⟩

def native.extensionData : Vector (Polynomial 763 Source.BaseField) 95 :=
  #v[[((1 : ZMod babyBearModulus), [⟨0, by decide⟩])], [((1 : ZMod babyBearModulus), [⟨0, by decide⟩])],
    [((1 : ZMod babyBearModulus), [⟨0, by decide⟩])], [((1 : ZMod babyBearModulus), [⟨0, by decide⟩])],
    [((1 : ZMod babyBearModulus), [⟨0, by decide⟩])], [((1 : ZMod babyBearModulus), [⟨0, by decide⟩])],
    [((503316480 : ZMod babyBearModulus), [⟨0, by decide⟩]),
      ((1509949441 : ZMod babyBearModulus), [⟨1, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨632, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨677, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨632, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨678, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨633, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨679, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨633, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨680, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨634, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨681, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨634, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨682, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨635, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨683, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨635, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨684, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨636, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨685, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨636, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨686, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨637, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨687, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨637, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨688, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨638, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨689, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨638, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨690, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨639, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨691, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨639, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨692, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨640, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨693, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨640, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨694, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨641, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨695, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨641, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨696, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨642, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨697, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨642, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨698, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨643, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨699, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨643, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨700, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨644, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨701, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨644, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨702, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨645, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨703, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨645, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨704, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨646, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨705, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨646, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨706, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨647, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨707, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨647, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨708, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨648, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨709, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨648, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨710, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨649, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨711, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨649, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨712, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨650, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨713, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨650, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨714, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨651, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨715, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨651, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨716, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨652, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨717, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨652, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨718, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨653, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨719, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨653, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨720, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨654, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨721, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨654, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨722, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨655, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨723, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨655, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨724, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨656, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨725, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨656, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨726, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨657, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨727, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨657, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨728, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨658, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨729, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨658, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨730, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨659, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨731, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨659, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨732, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨660, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨733, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨660, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨734, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨661, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨735, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨661, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨736, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨662, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨737, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨662, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨738, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨663, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨739, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨663, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨740, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨664, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨741, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨664, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨742, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨665, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨743, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨665, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨744, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨666, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨745, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨666, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨746, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨667, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨747, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨667, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨748, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨668, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨749, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨668, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨750, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨669, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨751, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨669, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨752, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨670, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨753, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨670, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨754, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨671, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨755, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨671, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨756, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨672, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨757, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨672, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨758, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨673, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨759, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨673, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨760, by decide⟩])],
    [((2013265919 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨1, by decide⟩]),
      ((524288 : ZMod babyBearModulus), [⟨674, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨761, by decide⟩])],
    [((524288 : ZMod babyBearModulus), []), ((2013265920 : ZMod babyBearModulus), [⟨2, by decide⟩]),
      ((2013265920 : ZMod babyBearModulus), [⟨674, by decide⟩]), ((1 : ZMod babyBearModulus), [⟨762, by decide⟩])],
    [((1997537281 : ZMod babyBearModulus), [⟨3, by decide⟩])],
    [((1981808641 : ZMod babyBearModulus), [⟨101, by decide⟩])]]

def native.extension (index : Fin 858) : Polynomial 763 Source.BaseField :=
  initialExtension (by decide : 763 ≤ 858) (fun coordinate => (native.extensionData)[coordinate]) index

noncomputable def native.artifact : ArithmeticExtension 763 858 Source.BaseField :=
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
      native.gate176, native.gate177, native.gate178, native.gate179, native.gate180, native.gate181, native.gate182,
      native.gate183, native.gate184, native.gate185, native.gate186, native.gate187, native.gate188, native.gate189,
      native.gate190, native.gate191, native.gate192, native.gate193, native.gate194, native.gate195, native.gate196,
      native.gate197, native.gate198, native.gate199, native.gate200, native.gate201, native.gate202, native.gate203,
      native.gate204, native.gate205, native.gate206, native.gate207, native.gate208, native.gate209, native.gate210,
      native.gate211, native.gate212, native.gate213, native.gate214, native.gate215, native.gate216, native.gate217,
      native.gate218, native.gate219, native.gate220, native.gate221, native.gate222, native.gate223, native.gate224,
      native.gate225, native.gate226, native.gate227, native.gate228, native.gate229, native.gate230, native.gate231,
      native.gate232, native.gate233, native.gate234, native.gate235, native.gate236, native.gate237, native.gate238,
      native.gate239, native.gate240, native.gate241, native.gate242, native.gate243, native.gate244, native.gate245,
      native.gate246, native.gate247, native.gate248, native.gate249, native.gate250, native.gate251, native.gate252,
      native.gate253, native.gate254, native.gate255, native.gate256, native.gate257, native.gate258, native.gate259,
      native.gate260, native.gate261, native.gate262, native.gate263, native.gate264, native.gate265, native.gate266,
      native.gate267, native.gate268, native.gate269, native.gate270, native.gate271, native.gate272, native.gate273,
      native.gate274, native.gate275, native.gate276, native.gate277, native.gate278, native.gate279, native.gate280,
      native.gate281, native.gate282, native.gate283, native.gate284, native.gate285, native.gate286, native.gate287,
      native.gate288, native.gate289, native.gate290, native.gate291, native.gate292, native.gate293, native.gate294,
      native.gate295, native.gate296, native.gate297, native.gate298, native.gate299, native.gate300, native.gate301,
      native.gate302, native.gate303, native.gate304, native.gate305, native.gate306, native.gate307, native.gate308,
      native.gate309, native.gate310, native.gate311, native.gate312, native.gate313, native.gate314],
    (fun index : Fin 763 => index.castLE (by decide : 763 ≤ 858)), native.extension⟩

theorem native.inputCoordinates (wire : Fin 763) :
    (native.bank).address ((native.artifact).projection wire) = (native.inputBank).address wire :=
  WireBank.ofList_prefix native.addresses native.inputs (by decide) (by decide) (by decide) native.inputPrefix wire
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
