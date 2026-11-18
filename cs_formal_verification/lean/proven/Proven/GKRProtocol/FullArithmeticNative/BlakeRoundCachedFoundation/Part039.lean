module
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part021
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part022
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part032
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part033
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part034
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part035
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part036
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part037
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation.Part038
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression166 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨569, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨569, by decide⟩) (Expression.constant (-1)))

def native.originalExpression167 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨575, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨575, by decide⟩) (Expression.constant (-1)))

def native.originalExpression168 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨581, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨581, by decide⟩) (Expression.constant (-1)))

def native.originalExpression169 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨587, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨587, by decide⟩) (Expression.constant (-1)))

def native.originalExpression170 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨593, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨593, by decide⟩) (Expression.constant (-1)))

def native.originalExpression171 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨599, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨599, by decide⟩) (Expression.constant (-1)))

def native.originalExpression172 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨605, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨605, by decide⟩) (Expression.constant (-1)))

def native.originalExpression173 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨611, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨611, by decide⟩) (Expression.constant (-1)))

def native.originalExpression174 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨617, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨617, by decide⟩) (Expression.constant (-1)))

def native.originalExpression175 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨623, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨623, by decide⟩) (Expression.constant (-1)))

def native.originalExpression176 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨629, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨629, by decide⟩) (Expression.constant (-1)))

noncomputable def native.source : List (Polynomial 763 Source.BaseField) :=
  [(native.originalExpression0).polynomial, (native.originalExpression1).polynomial,
      (native.originalExpression2).polynomial, (native.originalExpression3).polynomial,
      (native.originalExpression4).polynomial, (native.originalExpression5).polynomial,
      (native.originalExpression6).polynomial, (native.originalExpression7).polynomial,
      (native.originalExpression8).polynomial, (native.originalExpression9).polynomial,
      (native.originalExpression10).polynomial, (native.originalExpression11).polynomial,
      (native.originalExpression12).polynomial, (native.originalExpression13).polynomial,
      (native.originalExpression14).polynomial, (native.originalExpression15).polynomial,
      (native.originalExpression16).polynomial, (native.originalExpression17).polynomial,
      (native.originalExpression18).polynomial, (native.originalExpression19).polynomial,
      (native.originalExpression20).polynomial, (native.originalExpression21).polynomial,
      (native.originalExpression22).polynomial, (native.originalExpression23).polynomial,
      (native.originalExpression24).polynomial, (native.originalExpression25).polynomial,
      (native.originalExpression26).polynomial, (native.originalExpression27).polynomial,
      (native.originalExpression28).polynomial, (native.originalExpression29).polynomial,
      (native.originalExpression30).polynomial, (native.originalExpression31).polynomial,
      (native.originalExpression32).polynomial, (native.originalExpression33).polynomial,
      (native.originalExpression34).polynomial, (native.originalExpression35).polynomial,
      (native.originalExpression36).polynomial, (native.originalExpression37).polynomial,
      (native.originalExpression38).polynomial, (native.originalExpression39).polynomial,
      (native.originalExpression40).polynomial, (native.originalExpression41).polynomial,
      (native.originalExpression42).polynomial, (native.originalExpression43).polynomial,
      (native.originalExpression44).polynomial, (native.originalExpression45).polynomial,
      (native.originalExpression46).polynomial, (native.originalExpression47).polynomial,
      (native.originalExpression48).polynomial, (native.originalExpression49).polynomial,
      (native.originalExpression50).polynomial, (native.originalExpression51).polynomial,
      (native.originalExpression52).polynomial, (native.originalExpression53).polynomial,
      (native.originalExpression54).polynomial, (native.originalExpression55).polynomial,
      (native.originalExpression56).polynomial, (native.originalExpression57).polynomial,
      (native.originalExpression58).polynomial, (native.originalExpression59).polynomial,
      (native.originalExpression60).polynomial, (native.originalExpression61).polynomial,
      (native.originalExpression62).polynomial, (native.originalExpression63).polynomial,
      (native.originalExpression64).polynomial, (native.originalExpression65).polynomial,
      (native.originalExpression66).polynomial, (native.originalExpression67).polynomial,
      (native.originalExpression68).polynomial, (native.originalExpression69).polynomial,
      (native.originalExpression70).polynomial, (native.originalExpression71).polynomial,
      (native.originalExpression72).polynomial, (native.originalExpression73).polynomial,
      (native.originalExpression74).polynomial, (native.originalExpression75).polynomial,
      (native.originalExpression76).polynomial, (native.originalExpression77).polynomial,
      (native.originalExpression78).polynomial, (native.originalExpression79).polynomial,
      (native.originalExpression80).polynomial, (native.originalExpression81).polynomial,
      (native.originalExpression82).polynomial, (native.originalExpression83).polynomial,
      (native.originalExpression84).polynomial, (native.originalExpression85).polynomial,
      (native.originalExpression86).polynomial, (native.originalExpression87).polynomial,
      (native.originalExpression88).polynomial, (native.originalExpression89).polynomial,
      (native.originalExpression90).polynomial, (native.originalExpression91).polynomial,
      (native.originalExpression92).polynomial, (native.originalExpression93).polynomial,
      (native.originalExpression94).polynomial, (native.originalExpression95).polynomial,
      (native.originalExpression96).polynomial, (native.originalExpression97).polynomial,
      (native.originalExpression98).polynomial, (native.originalExpression99).polynomial,
      (native.originalExpression100).polynomial, (native.originalExpression101).polynomial,
      (native.originalExpression102).polynomial, (native.originalExpression103).polynomial,
      (native.originalExpression104).polynomial, (native.originalExpression105).polynomial,
      (native.originalExpression106).polynomial, (native.originalExpression107).polynomial,
      (native.originalExpression108).polynomial, (native.originalExpression109).polynomial,
      (native.originalExpression110).polynomial, (native.originalExpression111).polynomial,
      (native.originalExpression112).polynomial, (native.originalExpression113).polynomial,
      (native.originalExpression114).polynomial, (native.originalExpression115).polynomial,
      (native.originalExpression116).polynomial, (native.originalExpression117).polynomial,
      (native.originalExpression118).polynomial, (native.originalExpression119).polynomial,
      (native.originalExpression120).polynomial, (native.originalExpression121).polynomial,
      (native.originalExpression122).polynomial, (native.originalExpression123).polynomial,
      (native.originalExpression124).polynomial, (native.originalExpression125).polynomial,
      (native.originalExpression126).polynomial, (native.originalExpression127).polynomial,
      (native.originalExpression128).polynomial, (native.originalExpression129).polynomial,
      (native.originalExpression130).polynomial, (native.originalExpression131).polynomial,
      (native.originalExpression132).polynomial, (native.originalExpression133).polynomial,
      (native.originalExpression134).polynomial, (native.originalExpression135).polynomial,
      (native.originalExpression136).polynomial, (native.originalExpression137).polynomial,
      (native.originalExpression138).polynomial, (native.originalExpression139).polynomial,
      (native.originalExpression140).polynomial, (native.originalExpression141).polynomial,
      (native.originalExpression142).polynomial, (native.originalExpression143).polynomial,
      (native.originalExpression144).polynomial, (native.originalExpression145).polynomial,
      (native.originalExpression146).polynomial, (native.originalExpression147).polynomial,
      (native.originalExpression148).polynomial, (native.originalExpression149).polynomial,
      (native.originalExpression150).polynomial, (native.originalExpression151).polynomial,
      (native.originalExpression152).polynomial, (native.originalExpression153).polynomial,
      (native.originalExpression154).polynomial, (native.originalExpression155).polynomial,
      (native.originalExpression156).polynomial, (native.originalExpression157).polynomial,
      (native.originalExpression158).polynomial, (native.originalExpression159).polynomial,
      (native.originalExpression160).polynomial, (native.originalExpression161).polynomial,
      (native.originalExpression162).polynomial, (native.originalExpression163).polynomial,
      (native.originalExpression164).polynomial, (native.originalExpression165).polynomial,
      (native.originalExpression166).polynomial, (native.originalExpression167).polynomial,
      (native.originalExpression168).polynomial, (native.originalExpression169).polynomial,
      (native.originalExpression170).polynomial, (native.originalExpression171).polynomial,
      (native.originalExpression172).polynomial, (native.originalExpression173).polynomial,
      (native.originalExpression174).polynomial, (native.originalExpression175).polynomial,
      (native.originalExpression176).polynomial] ++
    (native.helperAssertions).map (Source.HelperAssertion.polynomial native.helperPlacement)

def native.gate0 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨769, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1073741824 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨1, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((939524097 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨0, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.mul (Compiler.Expression.constant ((1073741824 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨1, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((939524097 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨0, by decide⟩)))

def native.gate1 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨770, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨677, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨632, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨677, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨632, by decide⟩)))

def native.gate2 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨771, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨678, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨632, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨678, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨632, by decide⟩)))

def native.gate3 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨772, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨679, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨633, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨679, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨633, by decide⟩)))

def native.gate4 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨773, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨680, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨633, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨680, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨633, by decide⟩)))

def native.gate5 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨774, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨681, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨634, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨681, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨634, by decide⟩)))

def native.gate6 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨775, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨682, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨634, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨682, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨634, by decide⟩)))

def native.gate7 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨776, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨683, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨635, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨683, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨635, by decide⟩)))

def native.gate8 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨777, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨684, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨635, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨684, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨635, by decide⟩)))

def native.gate9 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨778, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨685, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨636, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨685, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨636, by decide⟩)))

def native.gate10 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨779, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨686, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨636, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨686, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨636, by decide⟩)))

def native.gate11 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨780, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨687, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨637, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨687, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨637, by decide⟩)))
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
