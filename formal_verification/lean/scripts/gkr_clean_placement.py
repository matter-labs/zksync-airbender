"""Generate untrusted numeric references for retained Clean placements."""
import json

from gkr_full_arithmetic_certificate import synthesize as full_arithmetic


def pair_nat(first, second):
    return second * second + first if first < second else first * first + first + second


def address_code(address):
    kind, value = next(iter(address.items()))
    tag = {"BaseLayerWitness": 0, "BaseLayerMemory": 1, "InnerLayer": 2, "Setup": 3,
           "VirtualSetup": 4, "ScratchSpace": 5, "Cached": 6}[kind]
    if kind in {"Cached", "InnerLayer"}:
        value = pair_nat(value["layer"], value["offset"])
    elif kind == "VirtualSetup":
        value = ["RangeCheck16Bits", "RangeCheckTimestamp", "InitsAndTeardownsLow",
                 "InitsAndTeardownsHigh"].index(value)
    return pair_nat(tag, value)


def address_term(address):
    kind, value = next(iter(address.items()))
    if isinstance(value, dict):
        arguments = f'{value["layer"]} {value["offset"]}'
    elif kind == "VirtualSetup":
        arguments = f'(.{value})'
    else:
        arguments = str(value)
    return f'(.{kind} {arguments})'


def module(name, case, pair, snapshot):
    complete = full_arithmetic(pair, snapshot)
    entries = complete["addresses"]
    placements = [address for _, address in sorted(pair["circuit"]["placement_data"].items(),
                                                   key=lambda entry: int(entry[0]))]
    coordinates = {json.dumps(address, sort_keys=True): index for index, address in enumerate(entries)}
    references = [(address_code(address), coordinates[json.dumps(address, sort_keys=True)]) for address in placements]
    codes = list(map(address_code, entries))
    base = f'Airbender.Compiler.FullArithmeticNative.{case}.native'
    target = f'Airbender.Proofs.GKRProtocol.CleanPlacementNative.{case}'
    content = ('import Airbender.Proofs.GKRProtocol.CleanPlacementChecks\n'
               'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n'
               f'import Airbender.Proofs.GKRProtocol.FullArithmeticNative.{case}\n\n'
               f'namespace Airbender.Compiler.CleanPlacementNative.{case}\n'
               'open Airbender Airbender.Compiler NumericPolynomialChecks\n'
               'set_option warningAsError true\nset_option Elab.async false\n'
               'set_option maxRecDepth 32768\n\n')
    for start in range(0, len(codes), 16):
        content += f'def bankCodes{start // 16} : List Nat := [' + ', '.join(map(str, codes[start:start + 16])) + ']\n'

    def tree(start, stop):
        if stop - start <= 16:
            return f'(LookupTable.leaf bankCodes{start // 16})'
        middle = start + 16 * (((stop - start + 15) // 16) // 2)
        return f'(LookupTable.branch {middle - start} {tree(start, middle)} {tree(middle, stop)})'

    content += '\ndef bank : LookupTable Nat := ' + tree(0, len(codes)) + '\n'
    content += 'def placements : List GKRAddress := [' + ', '.join(map(address_term, placements)) + ']\n'
    content += 'def references : List (Nat × Nat) := [' + ', '.join(f'({code}, {index})' for code, index in references) + ']\n'
    content += 'def capture : CleanPlacementChecks.Capture := ⟨bank, references⟩\n\n'
    content += f'''numeric_data_binding bank_binding : bank.toList = {base}.addresses.map AddressUniqueChecks.addressCode
numeric_data_binding placements_binding : references.map Prod.fst = placements.map AddressUniqueChecks.addressCode

theorem checked : CleanPlacementChecks.check capture = true := by decide +kernel

theorem placementsInBank : placements.all (fun address => decide
    ({base}.bank.address ({base}.bank.placement address) = address)) = true :=
  CleanPlacementChecks.check_sound {base}.addresses (by decide +kernel) {base}.addressesUnique
    placements capture bank_binding placements_binding checked

end Airbender.Compiler.CleanPlacementNative.{case}
'''
    return target, content


def capture_roots(case, address_count):
    prefix = f'Airbender.Compiler.CleanPlacementNative.{case}.'
    names = ["bank", "placements", "references", "capture", "bank_binding", "placements_binding",
             "checked", "placementsInBank"] + [f'bankCodes{index}' for index in range((address_count + 15) // 16)]
    return [prefix + name for name in names]
