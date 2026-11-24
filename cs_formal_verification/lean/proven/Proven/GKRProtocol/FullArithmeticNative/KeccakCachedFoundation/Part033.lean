module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part028
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part029
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part030
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression61 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression491
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨193, by decide⟩))
            (Compiler.Expression.atom ⟨184, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨192, by decide⟩))
          (Compiler.Expression.atom ⟨183, by decide⟩))))
    sharedExpression492

def native.originalExpression62 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
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
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨64, by decide⟩))
                          (Compiler.Expression.atom ⟨82, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨80, by decide⟩))
                  (Compiler.Expression.atom ⟨81, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨176, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨177, by decide⟩)))))
      sharedExpression493)
    sharedExpression494

def native.originalExpression63 : Expression 266 Source.BaseField :=
  sharedExpression495

def native.originalExpression64 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression496
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨190, by decide⟩))
            (Compiler.Expression.atom ⟨185, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨193, by decide⟩))
          (Compiler.Expression.atom ⟨184, by decide⟩))))
    sharedExpression497

def native.originalExpression65 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
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
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨64, by decide⟩))
                          (Compiler.Expression.atom ⟨82, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨80, by decide⟩))
                  (Compiler.Expression.atom ⟨81, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨178, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨179, by decide⟩)))))
      sharedExpression498)
    sharedExpression499

def native.originalExpression66 : Expression 266 Source.BaseField :=
  sharedExpression500

def native.originalExpression67 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression501
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨191, by decide⟩))
            (Compiler.Expression.atom ⟨182, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨190, by decide⟩))
          (Compiler.Expression.atom ⟨185, by decide⟩))))
    sharedExpression502

def native.originalExpression68 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
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
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨64, by decide⟩))
                          (Compiler.Expression.atom ⟨82, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨80, by decide⟩))
                  (Compiler.Expression.atom ⟨81, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨180, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨181, by decide⟩)))))
      sharedExpression503)
    sharedExpression504

def native.originalExpression69 : Expression 266 Source.BaseField :=
  sharedExpression505

def native.originalExpression70 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression506
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨192, by decide⟩))
            (Compiler.Expression.atom ⟨183, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
            (Compiler.Expression.atom ⟨81, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨191, by decide⟩))
          (Compiler.Expression.atom ⟨182, by decide⟩))))
    sharedExpression507

def native.originalExpression71 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨67, by decide⟩))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨84, by decide⟩)))

def native.originalExpression72 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
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
                        (Compiler.Expression.add (Compiler.Expression.constant 0)
                          (Compiler.Expression.atom ⟨81, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨83, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨198, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨199, by decide⟩)))))
      sharedExpression508)
    sharedExpression509

def native.originalExpression73 : Expression 266 Source.BaseField :=
  sharedExpression510

def native.originalExpression74 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression511
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨217, by decide⟩))
            (Compiler.Expression.atom ⟨208, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨83, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨215, by decide⟩))
          (Compiler.Expression.atom ⟨206, by decide⟩))))
    sharedExpression512

def native.originalExpression75 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
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
                        (Compiler.Expression.add (Compiler.Expression.constant 0)
                          (Compiler.Expression.atom ⟨81, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨83, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨200, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨201, by decide⟩)))))
      sharedExpression513)
    sharedExpression514

def native.originalExpression76 : Expression 266 Source.BaseField :=
  sharedExpression515

def native.originalExpression77 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression516
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨214, by decide⟩))
            (Compiler.Expression.atom ⟨209, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨83, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨216, by decide⟩))
          (Compiler.Expression.atom ⟨207, by decide⟩))))
    sharedExpression517

def native.originalExpression78 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
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
                        (Compiler.Expression.add (Compiler.Expression.constant 0)
                          (Compiler.Expression.atom ⟨81, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨83, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨202, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨203, by decide⟩)))))
      sharedExpression518)
    sharedExpression519

def native.originalExpression79 : Expression 266 Source.BaseField :=
  sharedExpression520

def native.originalExpression80 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression521
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨215, by decide⟩))
            (Compiler.Expression.atom ⟨206, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨83, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨217, by decide⟩))
          (Compiler.Expression.atom ⟨208, by decide⟩))))
    sharedExpression522

def native.originalExpression81 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
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
                        (Compiler.Expression.add (Compiler.Expression.constant 0)
                          (Compiler.Expression.atom ⟨81, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨83, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨204, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨205, by decide⟩)))))
      sharedExpression523)
    sharedExpression524

def native.originalExpression82 : Expression 266 Source.BaseField :=
  sharedExpression525

def native.originalExpression83 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression526
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨80, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨216, by decide⟩))
            (Compiler.Expression.atom ⟨207, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨83, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨214, by decide⟩))
          (Compiler.Expression.atom ⟨209, by decide⟩))))
    sharedExpression527

def native.originalExpression84 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨23, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨25, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)
end Airbender.Compiler.FullArithmeticNative.KeccakCached
