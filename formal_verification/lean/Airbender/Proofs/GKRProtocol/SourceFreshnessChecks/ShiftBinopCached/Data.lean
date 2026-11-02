import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.ShiftBinopCached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.SourceFreshnessChecks.ShiftBinopCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 0))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 1))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 2))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 3))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 4))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 5))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 6))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 7)))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 8))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 9))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 10))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 11))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 12))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 13))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 14))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 15)))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 16))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 17))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 18))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 19))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 20))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 21))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 22))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 23)))]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 24))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 25))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 26))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 27))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 28))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 29))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 30))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 31)))]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 32))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 33))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 34))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 35))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 36))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 37))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 38))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 39)))]

numeric_functional_base_capture data40 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 40))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 41))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 42))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 43))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 44))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 45))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 46))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 47)))]

numeric_functional_base_capture data48 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 48))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 49))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 50))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 51))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 52))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 53))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 54))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 55)))]

numeric_functional_base_capture data56 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 56))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 57))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 58))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 59))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 60))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 61))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 62))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 63)))]

numeric_functional_base_capture data64 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 64))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 65))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 66))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 67))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 68))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 69))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 70))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 71)))]

numeric_functional_base_capture data72 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 72))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 73))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 74))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 75))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 76))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 77))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 78))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 79)))]

numeric_functional_base_capture data80 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 80))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 81))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 82))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 83))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 84))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 85))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 86))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 87)))]

numeric_functional_base_capture data88 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 88))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 89))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 90))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement 91)))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (((data0 ++ (data8 ++ data16)) ++ (data24 ++ (data32 ++ data40))) ++ ((data48 ++ (data56 ++ data64)) ++ (data72 ++ (data80 ++ data88))))

numeric_functional_base_capture targetData := [NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 27)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 25)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 26))]

end Airbender.Compiler.SourceFreshnessChecks.ShiftBinopCached
