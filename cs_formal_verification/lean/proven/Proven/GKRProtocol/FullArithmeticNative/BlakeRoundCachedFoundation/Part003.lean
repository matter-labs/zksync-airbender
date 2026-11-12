module
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part002
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def sharedExpression24 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression23
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨118, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨145, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨207, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨122, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨146, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨208, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨218, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨124, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨151, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨213, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨223, by decide⟩))))

def sharedExpression25 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression24
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨126, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨144, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨206, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨216, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨128, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨148, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨210, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨220, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨130, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨149, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨211, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨221, by decide⟩))))

def sharedExpression26 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨226, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨142, by decide⟩))
              (Compiler.Expression.atom ⟨105, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨143, by decide⟩))
            (Compiler.Expression.atom ⟨123, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨144, by decide⟩))
          (Compiler.Expression.atom ⟨119, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨145, by decide⟩))
        (Compiler.Expression.atom ⟨121, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨146, by decide⟩))
      (Compiler.Expression.atom ⟨103, by decide⟩))

def sharedExpression27 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression26
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨147, by decide⟩))
                (Compiler.Expression.atom ⟨127, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨148, by decide⟩))
              (Compiler.Expression.atom ⟨113, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨149, by decide⟩))
            (Compiler.Expression.atom ⟨125, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨150, by decide⟩))
          (Compiler.Expression.atom ⟨133, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨151, by decide⟩))
        (Compiler.Expression.atom ⟨107, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨204, by decide⟩))
      (Compiler.Expression.atom ⟨9, by decide⟩))

def sharedExpression28 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression27
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨204, by decide⟩))
                (Compiler.Expression.atom ⟨105, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨205, by decide⟩))
              (Compiler.Expression.atom ⟨107, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨205, by decide⟩))
            (Compiler.Expression.atom ⟨123, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨206, by decide⟩))
          (Compiler.Expression.atom ⟨103, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨206, by decide⟩))
        (Compiler.Expression.atom ⟨119, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨207, by decide⟩))
      (Compiler.Expression.atom ⟨105, by decide⟩))

def sharedExpression29 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression28
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨207, by decide⟩))
                (Compiler.Expression.atom ⟨121, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨208, by decide⟩))
              (Compiler.Expression.atom ⟨5, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨208, by decide⟩))
            (Compiler.Expression.atom ⟨103, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨209, by decide⟩))
          (Compiler.Expression.atom ⟨111, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨209, by decide⟩))
        (Compiler.Expression.atom ⟨127, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨210, by decide⟩))
      (Compiler.Expression.atom ⟨25, by decide⟩))

def sharedExpression30 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression29
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨210, by decide⟩))
                (Compiler.Expression.atom ⟨113, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨211, by decide⟩))
              (Compiler.Expression.atom ⟨109, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨211, by decide⟩))
            (Compiler.Expression.atom ⟨125, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨212, by decide⟩))
          (Compiler.Expression.atom ⟨117, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨212, by decide⟩))
        (Compiler.Expression.atom ⟨133, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨213, by decide⟩))
      (Compiler.Expression.atom ⟨13, by decide⟩))

def sharedExpression31 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression30
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨213, by decide⟩))
                (Compiler.Expression.atom ⟨107, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨215, by decide⟩))
              (Compiler.Expression.atom ⟨13, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨215, by decide⟩))
            (Compiler.Expression.atom ⟨123, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨216, by decide⟩))
          (Compiler.Expression.atom ⟨5, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨216, by decide⟩))
        (Compiler.Expression.atom ⟨119, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨217, by decide⟩))
      (Compiler.Expression.atom ⟨9, by decide⟩))

def sharedExpression32 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression31
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨217, by decide⟩))
                (Compiler.Expression.atom ⟨121, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨219, by decide⟩))
              (Compiler.Expression.atom ⟨21, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨219, by decide⟩))
            (Compiler.Expression.atom ⟨127, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨221, by decide⟩))
          (Compiler.Expression.atom ⟨17, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨221, by decide⟩))
        (Compiler.Expression.atom ⟨125, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨222, by decide⟩))
      (Compiler.Expression.atom ⟨33, by decide⟩))

def sharedExpression33 : Compiler.Expression 858 Source.BaseField :=
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
                    (Compiler.Expression.atom ⟨226, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨204, by decide⟩))
                  (Compiler.Expression.atom ⟨9, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.atom ⟨205, by decide⟩))
                (Compiler.Expression.atom ⟨107, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨206, by decide⟩))
              (Compiler.Expression.atom ⟨103, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨207, by decide⟩))
            (Compiler.Expression.atom ⟨105, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨208, by decide⟩))
          (Compiler.Expression.atom ⟨5, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨209, by decide⟩))
        (Compiler.Expression.atom ⟨111, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨210, by decide⟩))
      (Compiler.Expression.atom ⟨25, by decide⟩))

def sharedExpression34 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add sharedExpression33
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.atom ⟨211, by decide⟩))
                    (Compiler.Expression.atom ⟨109, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨212, by decide⟩))
                  (Compiler.Expression.atom ⟨117, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.atom ⟨213, by decide⟩))
                (Compiler.Expression.atom ⟨13, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨215, by decide⟩))
              (Compiler.Expression.atom ⟨13, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨216, by decide⟩))
            (Compiler.Expression.atom ⟨5, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨217, by decide⟩))
          (Compiler.Expression.atom ⟨9, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨219, by decide⟩))
        (Compiler.Expression.atom ⟨21, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨221, by decide⟩))
      (Compiler.Expression.atom ⟨17, by decide⟩))

def sharedExpression35 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression34
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨222, by decide⟩))
            (Compiler.Expression.atom ⟨33, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨103, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨146, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨208, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨105, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨142, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨204, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨107, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨151, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨213, by decide⟩))))

def sharedExpression36 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression35
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨113, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨148, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨210, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨119, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨144, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨206, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨216, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨121, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨145, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨207, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨217, by decide⟩))))

def sharedExpression37 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression36
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨123, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨143, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨205, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨215, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨125, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨149, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨211, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨221, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨127, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨147, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨209, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨219, by decide⟩))))

def sharedExpression38 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨227, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨142, by decide⟩))
              (Compiler.Expression.atom ⟨106, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨143, by decide⟩))
            (Compiler.Expression.atom ⟨124, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨144, by decide⟩))
          (Compiler.Expression.atom ⟨120, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨145, by decide⟩))
        (Compiler.Expression.atom ⟨122, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨146, by decide⟩))
      (Compiler.Expression.atom ⟨104, by decide⟩))

def sharedExpression39 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression38
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨147, by decide⟩))
                (Compiler.Expression.atom ⟨128, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨148, by decide⟩))
              (Compiler.Expression.atom ⟨114, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨149, by decide⟩))
            (Compiler.Expression.atom ⟨126, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨150, by decide⟩))
          (Compiler.Expression.atom ⟨134, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨151, by decide⟩))
        (Compiler.Expression.atom ⟨108, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨204, by decide⟩))
      (Compiler.Expression.atom ⟨10, by decide⟩))

def sharedExpression40 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression39
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨204, by decide⟩))
                (Compiler.Expression.atom ⟨106, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨205, by decide⟩))
              (Compiler.Expression.atom ⟨108, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨205, by decide⟩))
            (Compiler.Expression.atom ⟨124, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨206, by decide⟩))
          (Compiler.Expression.atom ⟨104, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨206, by decide⟩))
        (Compiler.Expression.atom ⟨120, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨207, by decide⟩))
      (Compiler.Expression.atom ⟨106, by decide⟩))

def sharedExpression41 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression40
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨207, by decide⟩))
                (Compiler.Expression.atom ⟨122, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨208, by decide⟩))
              (Compiler.Expression.atom ⟨6, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨208, by decide⟩))
            (Compiler.Expression.atom ⟨104, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨209, by decide⟩))
          (Compiler.Expression.atom ⟨112, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨209, by decide⟩))
        (Compiler.Expression.atom ⟨128, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨210, by decide⟩))
      (Compiler.Expression.atom ⟨26, by decide⟩))
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
