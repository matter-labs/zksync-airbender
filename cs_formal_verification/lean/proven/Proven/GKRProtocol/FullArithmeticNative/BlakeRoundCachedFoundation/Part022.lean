module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

noncomputable def native.helperAssertions : List Source.HelperAssertion :=
  [Source.HelperAssertion.boolean (Source.HelperField.borrow 0),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 1),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 2),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 3),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 4),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 5),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 6),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 7),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 8),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 9),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 10),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 11),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 12),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 13),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 14),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 15),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 16),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 17),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 18),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 19),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 20),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 21),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 22),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 23),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 24),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 25),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 26),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 27),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 28),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 29),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 30),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 31),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 32),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 33),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 34),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 35),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 36),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 37),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 38),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 39),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 40),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 41),
    Source.HelperAssertion.boolean (Source.HelperField.borrow 42)]

theorem native.helperReferencesValid :
    (native.helperAssertions).all
        (fun assertion =>
          match assertion with
          | .zero field | .boolean field => field.referencesValid 632 43 0 43 false) =
      true :=
  by decide +kernel

def sharedExpression358 : Compiler.Expression 763 Source.BaseField :=
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
                    (Compiler.Expression.atom ⟨140, by decide⟩))
                  (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400))))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.atom ⟨141, by decide⟩))
                (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400))))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨142, by decide⟩))
              (Compiler.Expression.constant ((134217711 : ZMod babyBearModulus) * 943718400))))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨143, by decide⟩))
            (Compiler.Expression.constant ((268435422 : ZMod babyBearModulus) * 943718400))))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨144, by decide⟩))
          (Compiler.Expression.constant ((536870844 : ZMod babyBearModulus) * 943718400))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨145, by decide⟩))
        (Compiler.Expression.constant ((1073741688 : ZMod babyBearModulus) * 943718400))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨146, by decide⟩))
      (Compiler.Expression.constant ((134217455 : ZMod babyBearModulus) * 943718400)))

def sharedExpression359 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.atom ⟨142, by decide⟩))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨204, by decide⟩))))
            (Compiler.Expression.atom ⟨103, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨204, by decide⟩))
          (Compiler.Expression.atom ⟨5, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
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
              (Compiler.Expression.atom ⟨215, by decide⟩))))
        (Compiler.Expression.atom ⟨131, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨215, by decide⟩))
      (Compiler.Expression.atom ⟨29, by decide⟩))

def sharedExpression360 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression359
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨205, by decide⟩))
              (Compiler.Expression.atom ⟨115, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨144, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨206, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨216, by decide⟩))))
            (Compiler.Expression.atom ⟨125, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨216, by decide⟩))
          (Compiler.Expression.atom ⟨17, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨206, by decide⟩))
        (Compiler.Expression.atom ⟨109, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨145, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨207, by decide⟩))))
      (Compiler.Expression.atom ⟨117, by decide⟩))

def sharedExpression361 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression360
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨207, by decide⟩))
              (Compiler.Expression.atom ⟨33, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨146, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨208, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨218, by decide⟩))))
            (Compiler.Expression.atom ⟨121, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨218, by decide⟩))
          (Compiler.Expression.atom ⟨9, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨208, by decide⟩))
        (Compiler.Expression.atom ⟨105, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨147, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨209, by decide⟩))))
      (Compiler.Expression.atom ⟨107, by decide⟩))

def sharedExpression362 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression361
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨209, by decide⟩))
              (Compiler.Expression.atom ⟨13, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨148, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨210, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨220, by decide⟩))))
            (Compiler.Expression.atom ⟨127, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨220, by decide⟩))
          (Compiler.Expression.atom ⟨21, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨210, by decide⟩))
        (Compiler.Expression.atom ⟨111, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
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
      (Compiler.Expression.atom ⟨129, by decide⟩))

def sharedExpression363 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression362
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨221, by decide⟩))
              (Compiler.Expression.atom ⟨25, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨211, by decide⟩))
            (Compiler.Expression.atom ⟨113, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨150, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨212, by decide⟩))))
          (Compiler.Expression.atom ⟨115, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨212, by decide⟩))
        (Compiler.Expression.atom ⟨29, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
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
      (Compiler.Expression.atom ⟨123, by decide⟩))

def sharedExpression364 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.atom ⟨142, by decide⟩))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨204, by decide⟩))))
            (Compiler.Expression.atom ⟨104, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨204, by decide⟩))
          (Compiler.Expression.atom ⟨6, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
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
              (Compiler.Expression.atom ⟨215, by decide⟩))))
        (Compiler.Expression.atom ⟨132, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨215, by decide⟩))
      (Compiler.Expression.atom ⟨30, by decide⟩))

def sharedExpression365 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression364
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨205, by decide⟩))
              (Compiler.Expression.atom ⟨116, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨144, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨206, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨216, by decide⟩))))
            (Compiler.Expression.atom ⟨126, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨216, by decide⟩))
          (Compiler.Expression.atom ⟨18, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨206, by decide⟩))
        (Compiler.Expression.atom ⟨110, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨145, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨207, by decide⟩))))
      (Compiler.Expression.atom ⟨118, by decide⟩))

def sharedExpression366 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression365
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨207, by decide⟩))
              (Compiler.Expression.atom ⟨34, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨146, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨208, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨218, by decide⟩))))
            (Compiler.Expression.atom ⟨122, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨218, by decide⟩))
          (Compiler.Expression.atom ⟨10, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨208, by decide⟩))
        (Compiler.Expression.atom ⟨106, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨147, by decide⟩))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨209, by decide⟩))))
      (Compiler.Expression.atom ⟨108, by decide⟩))

def sharedExpression367 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression366
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨209, by decide⟩))
              (Compiler.Expression.atom ⟨14, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨148, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨210, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨220, by decide⟩))))
            (Compiler.Expression.atom ⟨128, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨220, by decide⟩))
          (Compiler.Expression.atom ⟨22, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨210, by decide⟩))
        (Compiler.Expression.atom ⟨112, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
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
      (Compiler.Expression.atom ⟨130, by decide⟩))

def sharedExpression368 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression367
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨221, by decide⟩))
              (Compiler.Expression.atom ⟨26, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨211, by decide⟩))
            (Compiler.Expression.atom ⟨114, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨150, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨212, by decide⟩))))
          (Compiler.Expression.atom ⟨116, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨212, by decide⟩))
        (Compiler.Expression.atom ⟨30, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
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
      (Compiler.Expression.atom ⟨124, by decide⟩))

def sharedExpression369 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.atom ⟨142, by decide⟩))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨204, by decide⟩))))
            (Compiler.Expression.atom ⟨105, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨204, by decide⟩))
          (Compiler.Expression.atom ⟨9, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
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
              (Compiler.Expression.atom ⟨215, by decide⟩))))
        (Compiler.Expression.atom ⟨123, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨215, by decide⟩))
      (Compiler.Expression.atom ⟨13, by decide⟩))

def sharedExpression370 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression369
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨205, by decide⟩))
              (Compiler.Expression.atom ⟨107, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨144, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨206, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨216, by decide⟩))))
            (Compiler.Expression.atom ⟨119, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨216, by decide⟩))
          (Compiler.Expression.atom ⟨5, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨206, by decide⟩))
        (Compiler.Expression.atom ⟨103, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
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
      (Compiler.Expression.atom ⟨121, by decide⟩))

def sharedExpression371 : Compiler.Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add sharedExpression370
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨217, by decide⟩))
              (Compiler.Expression.atom ⟨9, by decide⟩)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨207, by decide⟩))
            (Compiler.Expression.atom ⟨105, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨146, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨208, by decide⟩))))
          (Compiler.Expression.atom ⟨103, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨208, by decide⟩))
        (Compiler.Expression.atom ⟨5, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
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
      (Compiler.Expression.atom ⟨127, by decide⟩))
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
