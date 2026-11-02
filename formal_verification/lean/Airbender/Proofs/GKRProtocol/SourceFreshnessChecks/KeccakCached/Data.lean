import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.KeccakCached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.SourceFreshnessChecks.KeccakCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 0))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 1))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 2))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 3))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 4))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 5))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 6))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 7)))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 8))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 9))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 10))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 11))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 12))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 13))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 14))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 15)))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 16))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 17))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 18))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 19))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 20))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 21))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 22))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 23)))]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 24))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 25))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 26))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 27))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 28))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 29))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 30))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 31)))]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 32))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 33))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 34))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 35))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 36))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 37))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 38))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 39)))]

numeric_functional_base_capture data40 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 40))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 41))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 42))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 43))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 44))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 45))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 46))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 47)))]

numeric_functional_base_capture data48 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 48))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 49))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 50))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 51))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 52))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 53))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 54))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 55)))]

numeric_functional_base_capture data56 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 56))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 57))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 58))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 59))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 60))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 61))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 62))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 63)))]

numeric_functional_base_capture data64 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 64))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 65))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 66))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 67))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 68))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 69))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 70))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 71)))]

numeric_functional_base_capture data72 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 72))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 73))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 74))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 75))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 76))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 77))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 78))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 79)))]

numeric_functional_base_capture data80 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 80))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 81))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 82))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 83))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 84))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 85))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 86))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 87)))]

numeric_functional_base_capture data88 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 88))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 89))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 90))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 91))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 92))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 93))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 94))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 95)))]

numeric_functional_base_capture data96 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 96))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 97))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 98))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 99))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 100))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 101))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 102))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 103)))]

numeric_functional_base_capture data104 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 104))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 105))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 106))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 107))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 108))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 109))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 110))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 111)))]

numeric_functional_base_capture data112 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 112))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 113))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 114))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 115))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 116))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 117))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 118))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 119)))]

numeric_functional_base_capture data120 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 120))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 121))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 122))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 123))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 124))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 125))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 126))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 127)))]

numeric_functional_base_capture data128 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 128))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 129))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 130))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 131))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 132))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 133))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 134))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 135)))]

numeric_functional_base_capture data136 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 136))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 137))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 138))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 139))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 140))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 141))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 142))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 143)))]

numeric_functional_base_capture data144 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 144))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 145))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 146))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 147))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 148))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 149))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 150))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 151)))]

numeric_functional_base_capture data152 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 152))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 153))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 154))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 155))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 156))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 157))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 158))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 159)))]

numeric_functional_base_capture data160 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 160))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 161))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 162))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 163))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 164))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 165))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 166))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 167)))]

numeric_functional_base_capture data168 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 168))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 169))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 170))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 171))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 172))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 173))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 174))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 175)))]

numeric_functional_base_capture data176 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 176))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 177))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 178))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 179))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 180))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 181))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 182))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 183)))]

numeric_functional_base_capture data184 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 184))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 185))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 186))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 187))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 188))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 189))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 190))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 191)))]

numeric_functional_base_capture data192 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 192))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 193))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 194))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 195))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 196))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 197))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 198))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 199)))]

numeric_functional_base_capture data200 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 200))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 201))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 202))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 203))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 204))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 205))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 206))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 207)))]

numeric_functional_base_capture data208 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 208))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 209))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 210))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 211))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 212))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 213))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 214))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 215)))]

numeric_functional_base_capture data216 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 216))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 217))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 218))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 219))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 220))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.address (Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement 221)))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((((data0 ++ (data8 ++ data16)) ++ ((data24 ++ data32) ++ (data40 ++ data48))) ++ ((data56 ++ (data64 ++ data72)) ++ ((data80 ++ data88) ++ (data96 ++ data104)))) ++ (((data112 ++ (data120 ++ data128)) ++ ((data136 ++ data144) ++ (data152 ++ data160))) ++ ((data168 ++ (data176 ++ data184)) ++ ((data192 ++ data200) ++ (data208 ++ data216)))))

numeric_functional_base_capture targetData := [NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 174)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 173))]

end Airbender.Compiler.SourceFreshnessChecks.KeccakCached
