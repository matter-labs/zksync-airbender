module
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part020
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def sharedExpression342 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression341
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨113, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨150, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨212, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨119, by decide⟩))
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
            (Compiler.Expression.atom ⟨217, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨121, by decide⟩))
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

def sharedExpression343 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression342
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨123, by decide⟩))
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
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨125, by decide⟩))
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
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨129, by decide⟩))
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
          (Compiler.Expression.atom ⟨218, by decide⟩))))

def sharedExpression344 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨255, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨142, by decide⟩))
              (Compiler.Expression.atom ⟨134, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨143, by decide⟩))
            (Compiler.Expression.atom ⟨110, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨144, by decide⟩))
          (Compiler.Expression.atom ⟨112, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨145, by decide⟩))
        (Compiler.Expression.atom ⟨120, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨146, by decide⟩))
      (Compiler.Expression.atom ⟨130, by decide⟩))

def sharedExpression345 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression344
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨147, by decide⟩))
                (Compiler.Expression.atom ⟨122, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨148, by decide⟩))
              (Compiler.Expression.atom ⟨126, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨149, by decide⟩))
            (Compiler.Expression.atom ⟨124, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨150, by decide⟩))
          (Compiler.Expression.atom ⟨114, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨151, by decide⟩))
        (Compiler.Expression.atom ⟨104, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨204, by decide⟩))
      (Compiler.Expression.atom ⟨118, by decide⟩))

def sharedExpression346 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression345
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨204, by decide⟩))
                (Compiler.Expression.atom ⟨134, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨205, by decide⟩))
              (Compiler.Expression.atom ⟨18, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨205, by decide⟩))
            (Compiler.Expression.atom ⟨110, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨206, by decide⟩))
          (Compiler.Expression.atom ⟨22, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨206, by decide⟩))
        (Compiler.Expression.atom ⟨112, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨207, by decide⟩))
      (Compiler.Expression.atom ⟨104, by decide⟩))

def sharedExpression347 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression346
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨207, by decide⟩))
                (Compiler.Expression.atom ⟨120, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨208, by decide⟩))
              (Compiler.Expression.atom ⟨114, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨208, by decide⟩))
            (Compiler.Expression.atom ⟨130, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨209, by decide⟩))
          (Compiler.Expression.atom ⟨106, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨209, by decide⟩))
        (Compiler.Expression.atom ⟨122, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨210, by decide⟩))
      (Compiler.Expression.atom ⟨110, by decide⟩))

def sharedExpression348 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression347
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨210, by decide⟩))
                (Compiler.Expression.atom ⟨126, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨211, by decide⟩))
              (Compiler.Expression.atom ⟨108, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨211, by decide⟩))
            (Compiler.Expression.atom ⟨124, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨212, by decide⟩))
          (Compiler.Expression.atom ⟨26, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨212, by decide⟩))
        (Compiler.Expression.atom ⟨114, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨213, by decide⟩))
      (Compiler.Expression.atom ⟨6, by decide⟩))

def sharedExpression349 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression348
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨213, by decide⟩))
                (Compiler.Expression.atom ⟨104, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨214, by decide⟩))
              (Compiler.Expression.atom ⟨34, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨214, by decide⟩))
            (Compiler.Expression.atom ⟨134, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨217, by decide⟩))
          (Compiler.Expression.atom ⟨6, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨217, by decide⟩))
        (Compiler.Expression.atom ⟨120, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨218, by decide⟩))
      (Compiler.Expression.atom ⟨26, by decide⟩))

def sharedExpression350 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add sharedExpression349
              (Compiler.Expression.mul
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨218, by decide⟩))
                (Compiler.Expression.atom ⟨130, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨219, by decide⟩))
              (Compiler.Expression.atom ⟨10, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨219, by decide⟩))
            (Compiler.Expression.atom ⟨122, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨220, by decide⟩))
          (Compiler.Expression.atom ⟨18, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨220, by decide⟩))
        (Compiler.Expression.atom ⟨126, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨221, by decide⟩))
      (Compiler.Expression.atom ⟨14, by decide⟩))

def sharedExpression351 : Compiler.Expression 858 Source.BaseField :=
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
                    (Compiler.Expression.atom ⟨255, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨204, by decide⟩))
                  (Compiler.Expression.atom ⟨118, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.atom ⟨205, by decide⟩))
                (Compiler.Expression.atom ⟨18, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨206, by decide⟩))
              (Compiler.Expression.atom ⟨22, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨207, by decide⟩))
            (Compiler.Expression.atom ⟨104, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨208, by decide⟩))
          (Compiler.Expression.atom ⟨114, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨209, by decide⟩))
        (Compiler.Expression.atom ⟨106, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨210, by decide⟩))
      (Compiler.Expression.atom ⟨110, by decide⟩))

def sharedExpression352 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add sharedExpression351
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.atom ⟨211, by decide⟩))
                    (Compiler.Expression.atom ⟨108, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.atom ⟨212, by decide⟩))
                  (Compiler.Expression.atom ⟨26, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.atom ⟨213, by decide⟩))
                (Compiler.Expression.atom ⟨6, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨214, by decide⟩))
              (Compiler.Expression.atom ⟨34, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨217, by decide⟩))
            (Compiler.Expression.atom ⟨6, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨218, by decide⟩))
          (Compiler.Expression.atom ⟨26, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨219, by decide⟩))
        (Compiler.Expression.atom ⟨10, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨220, by decide⟩))
      (Compiler.Expression.atom ⟨18, by decide⟩))

def sharedExpression353 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression352
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨221, by decide⟩))
            (Compiler.Expression.atom ⟨14, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨104, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨151, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨213, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨110, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨143, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨205, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨112, by decide⟩))
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨144, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨206, by decide⟩))))

def sharedExpression354 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression353
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨114, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨150, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨212, by decide⟩)))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨120, by decide⟩))
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
            (Compiler.Expression.atom ⟨217, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨122, by decide⟩))
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

def sharedExpression355 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression354
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨124, by decide⟩))
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
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨126, by decide⟩))
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
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨146, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨208, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨218, by decide⟩))))

def sharedExpression356 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.mul
                    (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
                    (Compiler.Expression.atom ⟨139, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400))
                  (Compiler.Expression.atom ⟨140, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400))
                (Compiler.Expression.atom ⟨141, by decide⟩)))
            (Compiler.Expression.mul (Compiler.Expression.constant ((268435422 : ZMod babyBearModulus) * 943718400))
              (Compiler.Expression.atom ⟨142, by decide⟩)))
          (Compiler.Expression.mul (Compiler.Expression.constant ((536870844 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨143, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1073741688 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨144, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((134217455 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨145, by decide⟩)))
    (Compiler.Expression.mul (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400))
      (Compiler.Expression.atom ⟨146, by decide⟩))

def sharedExpression357 : Compiler.Expression 858 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.atom ⟨139, by decide⟩))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨140, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨141, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268435422 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨142, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((536870844 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨143, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1073741688 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨144, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((134217455 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.atom ⟨145, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨146, by decide⟩))

def native.originalProjection (index : Nat) : Fin 763 :=
  if bound : index < 632 then ⟨index, Nat.lt_of_lt_of_le bound (by decide)⟩ else ⟨0, by decide⟩

def native.readProjection : List (Fin 763 × Fin 763) :=
  [(⟨677, by decide⟩, ⟨678, by decide⟩), (⟨679, by decide⟩, ⟨680, by decide⟩), (⟨681, by decide⟩, ⟨682, by decide⟩),
    (⟨683, by decide⟩, ⟨684, by decide⟩), (⟨685, by decide⟩, ⟨686, by decide⟩), (⟨687, by decide⟩, ⟨688, by decide⟩),
    (⟨689, by decide⟩, ⟨690, by decide⟩), (⟨691, by decide⟩, ⟨692, by decide⟩), (⟨693, by decide⟩, ⟨694, by decide⟩),
    (⟨695, by decide⟩, ⟨696, by decide⟩), (⟨697, by decide⟩, ⟨698, by decide⟩), (⟨699, by decide⟩, ⟨700, by decide⟩),
    (⟨701, by decide⟩, ⟨702, by decide⟩), (⟨703, by decide⟩, ⟨704, by decide⟩), (⟨705, by decide⟩, ⟨706, by decide⟩),
    (⟨707, by decide⟩, ⟨708, by decide⟩), (⟨709, by decide⟩, ⟨710, by decide⟩), (⟨711, by decide⟩, ⟨712, by decide⟩),
    (⟨713, by decide⟩, ⟨714, by decide⟩), (⟨715, by decide⟩, ⟨716, by decide⟩), (⟨717, by decide⟩, ⟨718, by decide⟩),
    (⟨719, by decide⟩, ⟨720, by decide⟩), (⟨721, by decide⟩, ⟨722, by decide⟩), (⟨723, by decide⟩, ⟨724, by decide⟩),
    (⟨725, by decide⟩, ⟨726, by decide⟩), (⟨727, by decide⟩, ⟨728, by decide⟩), (⟨729, by decide⟩, ⟨730, by decide⟩),
    (⟨731, by decide⟩, ⟨732, by decide⟩), (⟨733, by decide⟩, ⟨734, by decide⟩), (⟨735, by decide⟩, ⟨736, by decide⟩),
    (⟨737, by decide⟩, ⟨738, by decide⟩), (⟨739, by decide⟩, ⟨740, by decide⟩), (⟨741, by decide⟩, ⟨742, by decide⟩),
    (⟨743, by decide⟩, ⟨744, by decide⟩), (⟨745, by decide⟩, ⟨746, by decide⟩), (⟨747, by decide⟩, ⟨748, by decide⟩),
    (⟨749, by decide⟩, ⟨750, by decide⟩), (⟨751, by decide⟩, ⟨752, by decide⟩), (⟨753, by decide⟩, ⟨754, by decide⟩),
    (⟨755, by decide⟩, ⟨756, by decide⟩), (⟨757, by decide⟩, ⟨758, by decide⟩), (⟨759, by decide⟩, ⟨760, by decide⟩),
    (⟨761, by decide⟩, ⟨762, by decide⟩)]

def native.borrowProjection : List (Fin 763) :=
  [⟨632, by decide⟩, ⟨633, by decide⟩, ⟨634, by decide⟩, ⟨635, by decide⟩, ⟨636, by decide⟩, ⟨637, by decide⟩,
    ⟨638, by decide⟩, ⟨639, by decide⟩, ⟨640, by decide⟩, ⟨641, by decide⟩, ⟨642, by decide⟩, ⟨643, by decide⟩,
    ⟨644, by decide⟩, ⟨645, by decide⟩, ⟨646, by decide⟩, ⟨647, by decide⟩, ⟨648, by decide⟩, ⟨649, by decide⟩,
    ⟨650, by decide⟩, ⟨651, by decide⟩, ⟨652, by decide⟩, ⟨653, by decide⟩, ⟨654, by decide⟩, ⟨655, by decide⟩,
    ⟨656, by decide⟩, ⟨657, by decide⟩, ⟨658, by decide⟩, ⟨659, by decide⟩, ⟨660, by decide⟩, ⟨661, by decide⟩,
    ⟨662, by decide⟩, ⟨663, by decide⟩, ⟨664, by decide⟩, ⟨665, by decide⟩, ⟨666, by decide⟩, ⟨667, by decide⟩,
    ⟨668, by decide⟩, ⟨669, by decide⟩, ⟨670, by decide⟩, ⟨671, by decide⟩, ⟨672, by decide⟩, ⟨673, by decide⟩,
    ⟨674, by decide⟩]

def native.helperPlacement : Source.HelperPlacement 763 :=
  ⟨⟨native.originalProjection, fun query limb =>
      let places := ((native.readProjection)[query]?).getD (⟨0, by decide⟩, ⟨0, by decide⟩)
      if limb.val = 0 then places.1 else places.2,
      fun _ => ⟨0, by decide⟩, fun _ _ => ⟨0, by decide⟩, fun _ _ => ⟨0, by decide⟩⟩,
    fun index => ((native.borrowProjection)[index]?).getD ⟨0, by decide⟩⟩
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
