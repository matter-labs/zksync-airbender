#!/usr/bin/env python3
"""Regenerate checked native lookup operand bindings for the execution profiles.

Selectors are read from the existing retained Lean imports. Every generated
field transport, leaf coverage, mask and setup binding is checked by Lean;
this script supplies no new proof assumption and changes no circuit artifact.
"""
from pathlib import Path
import argparse
import json
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true', help='check generated blocks without writing')
parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1], help=argparse.SUPPRESS)
parser.add_argument('--output-root', type=Path, help=argparse.SUPPRESS)
args = parser.parse_args()
ROOT = args.root.resolve()
OUT = args.output_root.resolve() if args.output_root else ROOT
CHANGED = []
NAMES = [family + cache for family in ['AddSub', 'JumpBranch', 'MulDiv', 'ShiftBinop', 'WordMemory', 'SubwordMemory', 'Unified'] for cache in ['Uncached', 'Cached']]
IMPORT_START = '/-- Expanded native lookup operands before alpha compression. The encodings and\n'
IMPORT_END = '-- End expanded native lookup operands.\n'
ARGUMENT_START = '/-- Exact matching of every enabled emitted tuple against the corresponding\n'
ARGUMENT_END = '-- End generated logical lookup argument.\n'
PROOF_START = '/-- Native base arithmetic transports the actual expanded operands to the\n'
PROOF_END = '-- End native operand transport.\n'

def selectors(tree, name):
    certs = []
    for path in sorted((ROOT / tree).glob(name + '*.lean')):
        for quoted in re.findall(r'\bselectors\s+("(?:[^"\\]|\\.)*")', path.read_text()):
            cert = json.loads(json.loads(quoted))
            if 'operands' in cert and cert not in certs:
                certs.append(cert)
    assert len(certs) == 1, (tree, name, len(certs))
    return certs[0]

def list_term(items):
    return '[' + ',\n      '.join(items) + ']'

def cons_proof(proofs):
    result = 'rfl'
    for proof in reversed(proofs):
        result = f'(congrArg₂ List.cons ({proof}) {result})'
    return result

def prepared(name):
    source_cert = selectors('Airbender/Proofs/GKRProtocol/LookupSourceNative', name)
    helper_cert = selectors('Airbender/Proofs/GKRProtocol/HelperNative', name)
    native = f'Airbender.Compiler.LookupSourceNative.{name}.native'
    helper = f'Airbender.Compiler.HelperNative.{name}.native'
    memory = f'Airbender.Compiler.MemoryNative.{name}.native'
    links = f'Airbender.Compiler.FunctionalLinksNative.{name}.native'
    clean = f'Airbender.Compiler.CleanArgumentsNative.{name}.native'
    fields = f'((input.physical ∘ {native}.bank.address) ∘ Airbender.Compiler.LookupNative.{name}.native.sourcePlacement)'
    queries = [[op for op in source_cert['operands'] if op['group'] == group and op['kind'] in ['query', 'decoder']] for group in ['GenericLookup', 'Lookup16Bits']]
    for group in queries:
        group.sort(key=lambda op: op['source_row'])
        assert len({op['source_row'] for op in group}) == len(group)
    helpers = sorted(helper_cert['operands'], key=lambda op: op['source_index'])
    assert [op['source_index'] for op in helpers] == list(range(8)), name
    assert helper_cert['setup_leaf'] == next(op['native_leaf'] for op in source_cert['operands'] if op['group'] == 'LookupTimestamps' and op['kind'] == 'setup'), name
    def native_query(op):
        leaf = op['native_leaf']
        return f'MaterializedQuery.mk ({native}.encoding{leaf}.fields input.physical)\n        ({native}.leaf{leaf}.weight.value input.physical)'
    def native_timestamp(op):
        return native_query(op)
    actual_groups = [list_term([native_query(op) for op in group]) for group in queries]
    actual_groups.append(list_term([native_timestamp(op) for op in helpers]))
    indexed_groups = [list_term([f'({op["native_leaf"]}, {native_query(op)})' for op in group]) for group in queries] + [list_term([f'({op["native_leaf"]}, {native_timestamp(op)})' for op in helpers])]
    setups = [next(op['native_leaf'] for op in source_cert['operands'] if op['group'] == group and op['kind'] == 'setup') for group in ['GenericLookup', 'Lookup16Bits', 'LookupTimestamps']]
    import_block = IMPORT_START + '''masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  (''' + list_term(indexed_groups) + ''').get group

def nativeSetupLeaf (group : Fin 3) : Nat :=
  (''' + list_term([str(index) for index in setups]) + ''').get group

noncomputable def nativeRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  (nativeOperands input group).map Prod.snd
''' + IMPORT_END
    proof_parts = []
    for group in queries:
        for op in group:
            leaf = op['native_leaf']
            start = 1 if op['kind'] == 'decoder' else 0
            copies = 'copies'
            equality = cons_proof([f'{native}.sourceField{leaf}_{column} input.physical {copies}' for column in range(start, len(op['fields']))])
            weight = f'({native}.sourceField{leaf}_0 input.physical {copies})' if start else 'rfl'
            proof_parts.append(f'''private theorem native_query{leaf} (input : Input) :
    {native_query(op)} =
      {native}.query{leaf}.materialized {fields} :=
  let copies := {links}.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk {equality} {weight}).symm
''')
    for op in helpers:
        leaf, index = op['native_leaf'], op['source_index']
        proof_parts.append(f'''private theorem native_timestamp{index} (input : Input) :
    {native_query(op)} =
      MaterializedQuery.mk [(({helper}.fields).get ⟨{index}, by decide⟩).value ({helper}.sourceValues input.physical)] 1 := by
  have same := ({helper}.candidate{leaf}).sound
    {helper}.placement {memory}.bank
    {helper}.checked{leaf} {helper}.inBank{leaf}
    input.physical ({links}.helperCopies input.physical input.arithmetic)
  rw [{clean}.timestampFieldMatch{index}] at same
  change MaterializedQuery.mk [{helper}.recipe{leaf}.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm
''')
    proof_parts.append('''/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem nativeRequests_source (input : Input) (group : Fin 3) :
    nativeRequests input group = physicalRequests input group := by
  fin_cases group
''')
    for group_index, group in enumerate(queries):
        sources = list_term([f'{native}.query{op["native_leaf"]}.materialized {fields}' for op in group])
        proof = cons_proof([f'native_query{op["native_leaf"]} input' for op in group])
        proof_parts.append(f'  · change {actual_groups[group_index]} =\n      {sources}\n    exact {proof}\n')
    sources = list_term([f'MaterializedQuery.mk [(({helper}.fields).get ⟨{op["source_index"]}, by decide⟩).value ({helper}.sourceValues input.physical)] 1' for op in helpers])
    proof = cons_proof([f'native_timestamp{op["source_index"]} input' for op in helpers])
    proof_parts.append(f'  · change {actual_groups[2]} =\n      {sources}\n    exact {proof}\n')
    trees = [f'Airbender.Compiler.LookupNative.{name}.native.{stem}Tree' for stem in ['generic', 'range16', 'timestamp']]
    proof_parts.append(f'''/-- Every native query leaf occurs once, with the single setup leaf completing
exactly the retained native reduction tree's primitive multiset. -/
theorem nativeOperands_coverage (input : Input) (group : Fin 3) :
    (((nativeOperands input group).map Prod.fst) ++ [nativeSetupLeaf group]).Perm
      (({list_term(trees)}).get group).leaves := by
  fin_cases group
''')
    for index, group in enumerate(queries + [helpers]):
        indices = [str(op['native_leaf']) for op in group] + [str(setups[index])]
        checked = [f'{native}.genericLeavesChecked', f'{native}.range16LeavesChecked', f'{helper}.leavesChecked'][index]
        proof_parts.append(f'  · change ({list_term(indices)} : List Nat).Perm ({trees[index]}).leaves\n    exact Eq.mpr (congrArg (fun leaves : List Nat => ({list_term(indices)} : List Nat).Perm leaves)\n      {checked}) (by decide +kernel)\n')
    columns = [f'Airbender.Compiler.TableNative.{name}.native.{stem}SetupColumns' for stem in ['generic', 'range16', 'timestamp']]
    encodings = [f'{native}.encoding{index}.columns' for index in setups]
    proof_parts.append(f'''/-- Each designated native setup operand contains precisely the columns used
by the literal setup table in the corresponding logical argument. -/
theorem nativeSetupColumns_binding (group : Fin 3) :
    ({list_term(encodings)}).get group =
      (Airbender.Compiler.MaterializedWitnessNative.{name}.setupColumns group).map
        (fun column => AffineProgram.input (Address := GKRAddress) (R := Nat) column.address) := by
  fin_cases group
  · exact Airbender.Compiler.TableNative.{name}.native.genericSetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.{name}.native.range16SetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.{name}.native.timestampSetupColumnsPreserved
''')
    proof_parts.append(f'''/-- Exact native matching supplies every enabled source tuple in the supplied
setup rows. Native arithmetic proves the operand transport. -/
theorem source_member_with
    (tables : Fin 3 → Fin Airbender.Compiler.MaterializedNative.{name}.native.model.imported.data.length →
      List Source.BaseField) (input : Input) (arguments : LookupArgumentsWith tables input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    ∃ index, query.fields = tables group index := by
  apply LookupArgument.member (arguments group)
  change query.fields ∈ activeLookupFields (nativeRequests input group)
  rw [nativeRequests_source input group]
  exact activeLookupFields.member member enabled

private noncomputable def sourceArguments (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) : LookupArgument
      (Airbender.Compiler.MaterializedNative.{name}.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.{name}.setupColumns group))
      (activeLookupFields (physicalRequests input group)) := by
  simpa only [nativeRequests_source input group, Airbender.Compiler.MaterializedWitnessNative.{name}.setupColumns] using arguments group
''')
    proof_block = PROOF_START + 'source-projected logical interface; none of the field equalities is a premise. -/\n' + '\n'.join(proof_parts) + PROOF_END
    ip = Path(f'Airbender/Import/Compiler/LogicalRows/{name}.lean')
    text = (ROOT / ip).read_text()
    needle = '/-- Exact matching of every enabled emitted tuple against the corresponding\n'
    if IMPORT_START in text:
        begin = text.index(IMPORT_START)
        end = text.index(IMPORT_END, begin) + len(IMPORT_END)
        text = text[:begin] + import_block + text[end:]
    else:
        assert text.count(needle) == 1
        text = text.replace(needle, import_block + '\n' + needle)
    text = text.replace('(activeLookupFields (physicalRequests input group))', '(activeLookupFields (nativeRequests input group))')
    expected_arguments = 1 + int('def LookupArgumentsWith' in text)
    assert text.count('activeLookupFields (nativeRequests input group)') == expected_arguments
    # Generate the complete public premise instantiation, as well as operands.
    # Its meaning lives in Review.Compiler.LookupArgument, independent of native
    # certificate proofs. Setup columns and requests are artifact bindings.
    argument_block = ARGUMENT_START + f'''literal setup columns. The generic Review definition states exact matching;
this generated binding selects the three setup-column groups and native tuples. -/
def LookupArguments (input : Input) : Type :=
  GroupedLookupArguments
    (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.{name}.native.model.fields
      (([Airbender.Compiler.TableNative.{name}.native.genericSetupColumns,
         Airbender.Compiler.TableNative.{name}.native.range16SetupColumns,
         Airbender.Compiler.TableNative.{name}.native.timestampSetupColumns]).get group))
    (fun group => activeLookupFields (nativeRequests input group))

/-- Match the same native tuples against independently supplied setup rows.
The calling boundary must bind these rows to public text and fixed setup data. -/
def LookupArgumentsWith
    (tables : Fin 3 → Fin Airbender.Compiler.MaterializedNative.{name}.native.model.imported.data.length →
      List Source.BaseField) (input : Input) : Type :=
  GroupedLookupArguments tables (fun group => activeLookupFields (nativeRequests input group))

/-- The retained setup gives exactly the existing lookup argument type. -/
theorem lookup_arguments_with_retained (input : Input) :
    LookupArgumentsWith
      (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.{name}.native.model.fields
        (([Airbender.Compiler.TableNative.{name}.native.genericSetupColumns,
           Airbender.Compiler.TableNative.{name}.native.range16SetupColumns,
           Airbender.Compiler.TableNative.{name}.native.timestampSetupColumns]).get group)) input =
      LookupArguments input := rfl
''' + ARGUMENT_END
    begin = text.index(ARGUMENT_START)
    if ARGUMENT_END in text:
        end = text.index(ARGUMENT_END, begin) + len(ARGUMENT_END)
    else:
        end = text.index('\ndef inputRow', begin)
    text = text[:begin] + argument_block + text[end:]
    text = text.replace('/-- The emitted source-query operands interpreted at the actual physical wires.\nThe generic/range16 groups include their native nonzero masks. The timestamp\nhelper group uses the actual physical borrow and history coordinates. -/', '/-- Source-projected logical operands at the physical source, borrow and\nhistory coordinates. The public lookup argument matches nativeRequests; the\nsupporting proof transports that matching to this source interpretation. -/')
    pp = Path(f'Airbender/Proofs/GKRProtocol/ProgramNativeTransport/{name}.lean')
    ptext = (ROOT / pp).read_text()
    ptext = ptext.replace('(activeLookupFields (physicalRequests input group))) := rfl', '(activeLookupFields (nativeRequests input group))) := rfl')
    assert ptext.count('(activeLookupFields (nativeRequests input group))) := rfl') == 1
    needle = 'private theorem physical_member'
    if PROOF_START in ptext:
        begin = ptext.index(PROOF_START)
        end = ptext.index(PROOF_END, begin) + len(PROOF_END)
        ptext = ptext[:begin] + proof_block + ptext[end:]
    else:
        assert ptext.count(needle) == 1
        ptext = ptext.replace(needle, proof_block + '\n' + needle)
    generated, consumers = ptext.split(PROOF_END, 1)
    consumers = consumers.replace('LookupArgument.member (arguments group)',
                                  'LookupArgument.member (sourceArguments input arguments group)')
    assert consumers.count('LookupArgument.member (sourceArguments input arguments group)') == 1
    ptext = generated + PROOF_END + consumers
    for path, content in [(ip,text),(pp,ptext)]:
        emit(path, content)
    return len(queries[0]), len(queries[1]), len(helpers)

def emit(path, content):
    content = content.rstrip('\n') + '\n'
    original = ROOT / path
    changed = not original.exists() or original.read_text() != content
    if changed:
        CHANGED.append(str(path))
    if not args.check and changed:
        destination = OUT / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(content)

def program_row_interfaces():
    review = '''import Airbender.Review.Compiler.Arithmetic
import Airbender.Import.Compiler.LogicalRows

namespace Airbender.Compiler

/-- Setup row parameters for each native configuration and lookup group.
The public boundary binds these parameters to program and fixed setup data. -/
abbrev ProgramLookupRows := Configuration → Fin 3 → Nat → List Source.BaseField
'''
    proofs = '''import Airbender.Review.Compiler.ProgramLogicalRows
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport

namespace Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
'''
    roots = ['Airbender.Compiler.ProgramLookupRows']
    for execution, native_namespace, family, cases in [
        ('PooledExecution', 'PooledRowNative', 'PooledFamily',
         [name for name in NAMES if not name.startswith('Unified')]),
        ('UnifiedExecution', 'UnifiedRowNative', 'UnifiedFamily',
         [name for name in NAMES if name.startswith('Unified')]),
    ]:
        review += f'''
namespace {execution}

/-- Physical native inputs and exact lookup matching against setup parameters.
Each constructor selects its actual circuit and cache configuration. -/
inductive ProgramLogicalRowCertificate (tables : ProgramLookupRows) where
'''
        for name in cases:
            constructor = name[0].lower() + name[1:]
            native = f'{native_namespace}.{name}'
            review += f'''  | {constructor} (input : {native}.Input)
      (arguments : {native}.LookupArgumentsWith
        (fun group index => tables .{constructor} group index.val) input)
'''
            roots.append(f'Airbender.Compiler.{execution}.ProgramLogicalRowCertificate.{constructor}')
        review += f'''
def ProgramLogicalRowCertificate.row {{tables : ProgramLookupRows}} :
    ProgramLogicalRowCertificate tables → Trace.Row babyBearModulus Trace.{family}
'''
        for name in cases:
            constructor = name[0].lower() + name[1:]
            review += f'  | .{constructor} input _ => {native_namespace}.{name}.inputRow input\n'
        review += '''
def ProgramLogicalRowCertificate.configuration {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Configuration
'''
        for name in cases:
            constructor = name[0].lower() + name[1:]
            review += f'  | .{constructor} _ _ => .{constructor}\n'
        review += '''
def ProgramLogicalRowCertificate.lookupLength {tables : ProgramLookupRows} :
    ProgramLogicalRowCertificate tables → Nat
'''
        for name in cases:
            constructor = name[0].lower() + name[1:]
            review += f'  | .{constructor} _ _ => Airbender.Compiler.MaterializedNative.{name}.native.model.imported.data.length\n'
        review += '''
/-- Source tuples projected from the actual native input coordinates. -/
noncomputable def ProgramLogicalRowCertificate.sourceRequests {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) (group : Fin 3) : List MaterializedQuery :=
  match cert with
'''
        for name in cases:
            constructor = name[0].lower() + name[1:]
            review += f'  | .{constructor} input _ => {native_namespace}.{name}.physicalRequests input group\n'
        review += f'\nend {execution}\n'
        proofs += f'''
namespace {execution}

/-- The physical native input proves the execute bit for either cache mode. -/
theorem ProgramLogicalRowCertificate.row_active {{tables : ProgramLookupRows}}
    (cert : ProgramLogicalRowCertificate tables) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
'''
        for name in cases:
            constructor = name[0].lower() + name[1:]
            proofs += f'  | {constructor} input _arguments => exact {native_namespace}.{name}.input_active input\n'
        proofs += '''
/-- Exact matching and native operand transport supply the source tuple.
The public setup interpretation remains a separate boundary. -/
theorem ProgramLogicalRowCertificate.source_member {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ cert.sourceRequests group) (enabled : query.weight ≠ 0) :
    ∃ index : Fin cert.lookupLength, query.fields = tables cert.configuration group index.val := by
  cases cert with
'''
        for name in cases:
            constructor = name[0].lower() + name[1:]
            proofs += f'''  | {constructor} input arguments =>
    obtain ⟨index, same⟩ := {native_namespace}.{name}.source_member_with
      (fun group index => tables .{constructor} group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
'''
        proofs += f'\nend {execution}\n'
        roots += [f'Airbender.Compiler.{execution}.ProgramLogicalRowCertificate',
                  f'Airbender.Compiler.{execution}.ProgramLogicalRowCertificate.row',
                  f'Airbender.Compiler.{execution}.ProgramLogicalRowCertificate.row_active',
                  f'Airbender.Compiler.{execution}.ProgramLogicalRowCertificate.configuration',
                  f'Airbender.Compiler.{execution}.ProgramLogicalRowCertificate.lookupLength',
                  f'Airbender.Compiler.{execution}.ProgramLogicalRowCertificate.sourceRequests',
                  f'Airbender.Compiler.{execution}.ProgramLogicalRowCertificate.source_member']
    review += '\nend Airbender.Compiler\n'
    proofs += '\nend Airbender.Compiler\n'
    emit(Path('Airbender/Review/Compiler/ProgramLogicalRows.lean'), review)
    emit(Path('Airbender/Proofs/GKRProtocol/ProgramLogicalRows.lean'), proofs)
    return roots

def program_setup_interfaces():
    families = {'AddSub': 'add-sub', 'JumpBranch': 'jump-branch', 'MulDiv': 'mul-div',
                'ShiftBinop': 'shift-binop', 'WordMemory': 'word-memory',
                'SubwordMemory': 'subword-memory', 'Unified': 'unified'}
    data = '''import Airbender.Reference.Compiler.ProgramSetup
import Airbender.Review.Compiler.ProgramLogicalRows

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler

/-- Native setup geometry. Both cache configurations use each exported layout. -/
def layouts : Configuration → Option ProgramSetup.Layout
'''
    for family, filename in families.items():
        artifact = json.loads((ROOT / 'artifacts/setup' / (filename + '.json')).read_text())
        circuit = artifact['circuit']
        assert circuit['has_decoder_lookup'], filename
        roms = [table for table in artifact['tables'] if table['id'] == 34]
        assert len(roms) <= 1, filename
        rom_start = 'none' if not roms else 'some ' + str(roms[0]['offset'])
        rom_words = 0 if not roms else roms[0]['length']
        prefix = family[0].lower() + family[1:]
        data += f'''  | .{prefix}Uncached | .{prefix}Cached => some {{
      «width» := {circuit['generic_lookup_tables_width']}
      tagged := {str(circuit['tables_ids_in_generic_lookups']).lower()}
      decoderStart := {circuit['offset_for_decoder_table']}
      decoderWords := {circuit['total_tables_size'] - circuit['offset_for_decoder_table']}
      romStart := {rom_start}
      romWords := {rom_words} }}
'''
    data += '  | _ => none\n'
    for function, value in [
        ('lookupLength', 'MaterializedNative.{name}.native.model.imported.data.length'),
        ('genericWidth', 'TableNative.{name}.native.genericSetupColumns.length'),
    ]:
        data += f'\ndef {function} : Configuration → Nat\n'
        for name in NAMES:
            constructor = name[0].lower() + name[1:]
            data += f'  | .{constructor} => ' + value.format(name=name) + '\n'
        data += '  | _ => 0\n'
    data += '''
/-- Read the unchanged captured row at every valid native index. -/
noncomputable def retainedRows (configuration : Configuration) (group : Fin 3)
    (index : Nat) : List Source.BaseField :=
  match configuration with
'''
    for name in NAMES:
        constructor = name[0].lower() + name[1:]
        data += f'''  | .{constructor} =>
    if bounded : index < MaterializedNative.{name}.native.model.imported.data.length then
      MaterializedNative.{name}.native.model.fields
        (([TableNative.{name}.native.genericSetupColumns,
           TableNative.{name}.native.range16SetupColumns,
           TableNative.{name}.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
'''
    data += '''  | _ => []

/-- Build lookup rows from public decoder columns and a public ROM word function. -/
noncomputable def rows (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) : ProgramLookupRows :=
  fun configuration group index =>
    match layouts configuration with
    | none => retainedRows configuration group index
    | some layout => ProgramSetup.groupRows layout (retainedRows configuration)
        (decoder configuration) wordAt group index

def ValidGeometry (configuration : Configuration) : Prop :=
  match layouts configuration with
  | none => True
  | some layout =>
    0 < layout.width ∧ layout.width = genericWidth configuration ∧
      layout.decoderStart + layout.decoderWords ≤ lookupLength configuration ∧
      layout.decoderWords = 1048576 ∧ layout.romWords ≤ 1048576 ∧
      match layout.romStart with
      | none => layout.romWords = 0
      | some regionStart => regionStart + layout.romWords ≤ layout.decoderStart

end Airbender.Compiler.NativeProgramSetup
'''
    proof = '''import Airbender.Data.Compiler.NativeProgramSetup
import Airbender.Proofs.GKRProtocol.ProgramSetupRows

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem geometry_valid (configuration : Configuration) : ValidGeometry configuration := by
  cases configuration <;> simp only [ValidGeometry, layouts] <;> decide +kernel

theorem rows_fixed_group (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (configuration : Configuration) (group : Fin 3)
    (index : Nat) (other : group.val ≠ 0) :
    rows decoder wordAt configuration group index = retainedRows configuration group index := by
  cases selected : layouts configuration with
  | none => simp [rows, selected]
  | some layout =>
    simpa [rows, selected] using
      ProgramSetup.fixed_group layout (retainedRows configuration) (decoder configuration)
        wordAt group index other

end Airbender.Compiler.NativeProgramSetup
'''
    emit(Path('Airbender/Data/Compiler/NativeProgramSetup.lean'), data)
    emit(Path('Airbender/Proofs/GKRProtocol/ProgramSetupNative.lean'), proof)
    return ['Airbender.Compiler.NativeProgramSetup.' + name for name in
            ['layouts', 'lookupLength', 'genericWidth', 'retainedRows', 'rows', 'ValidGeometry',
             'geometry_valid', 'rows_fixed_group']]

def program_decoder_interfaces():
    root = ROOT
    roots = []
    families = {'AddSub': ('addSub', 'add-sub'), 'JumpBranch': ('jumpBranchSlt', 'jump-branch'),
                'MulDiv': ('mulDiv', 'mul-div'), 'ShiftBinop': ('shiftBinop', 'shift-binop'),
                'WordMemory': ('wordMemory', 'word-memory'),
                'SubwordMemory': ('subwordMemory', 'subword-memory'), 'Unified': ('', 'unified')}
    for name in NAMES:
        family, filename = families[next(family for family in families if name.startswith(family))]
        owner = 'UnifiedRowNative' if name.startswith('Unified') else 'PooledRowNative'
        argument_source = (root / 'Airbender/Proofs/GKRProtocol/DecoderArgumentsNative' / f'{name}.lean').read_text()
        trace_columns = re.search(r'\btrace_columns (\S+)', argument_source)[1]
        decoder_columns = re.search(r'\bdecoder_columns (\S+)', argument_source)[1]
        artifact=json.loads((root/'artifacts/setup'/f'{filename}.json').read_text())
        circuit=artifact['circuit']; width=circuit['generic_lookup_tables_width'];tagged=circuit['tables_ids_in_generic_lookups'];mask=circuit['decode_table_columns_mask']
        assert sum(mask) + int(tagged) == width, name
        selectors=[]
        for quoted in re.findall(r'\bselectors\s+("(?:[^"\\]|\\.)*")',(root/'Airbender/Proofs/GKRProtocol/LookupSourceNative'/f'{name}.lean').read_text()):
            obj=json.loads(json.loads(quoted))
            if 'operands' in obj:selectors.append(obj)
        assert len(selectors)==1
        queries=sorted([op for op in selectors[0]['operands'] if op['group']=='GenericLookup' and op['kind'] in ['query','decoder']],key=lambda o:o['source_row'])
        decoder=next(o for o in queries if o['kind']=='decoder');leaf=decoder['native_leaf'];slot=queries.index(decoder)
        source=f'Airbender.Compiler.LookupSourceNative.{name}.native'
        native=f'Airbender.Compiler.DecoderArgumentsNative.{name}.native'
        clean=f'Airbender.Compiler.CleanArithmeticNative.{name}.native'
        case=f'Airbender.Compiler.{owner}.{name}'
        coordinates=f'((input.physical ∘ {source}.bank.address) ∘ Airbender.Compiler.LookupNative.{name}.native.sourcePlacement)'
        fields=f'{source}.query{leaf}.fields.map (fun field => field.value {coordinates})'
        query=f'({case}.inputRow input).decoderQuery'
        native_mask = 'ProgramRows.Proofs.unifiedMask' if name.startswith('Unified') else f'(ProgramRows.Proofs.maskOfFamily .{family})'
        masked=f'ProgramRows.maskRow {native_mask} {query}'
        packed=f'ProgramSetup.packTagged {width} 46 ({masked})' if tagged else masked
        projection=', '.join([f'row[{i}]' for i,b in enumerate(mask) if b]+(['46'] if tagged else []))
        exprs=', '.join(f'{native}.expression{i}' for i in range(1,width+1))
        simplifiers=f'project, {native}.payloadExpressions, '+exprs+(', _root_.Expression.eval' if tagged else '')
        code=f'''import Airbender.Import.Compiler.LogicalRows.{name}
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.{name}
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.{name}
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : {case}.Input) :
    {fields} =
      {packed} := by
  rw [← {native}.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [{projection}]
  have left : ({native}.payloadExpressions.map (fun expression => expression.eval
      ({clean}.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions {trace_columns} {decoder_columns}).map
        (fun expression => expression.eval ({clean}.environment input.physical (fun _ _ => #[])))) := by simp [{simplifiers}]
  have right : {packed} = project (Trace.nativeDecoderQuery
      {trace_columns} {decoder_columns}
      (fun index => ({clean}.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    {trace_columns} {decoder_columns}
    ({clean}.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : {case}.Input) :
    {source}.query{leaf}.weight (RingHom.id _) {coordinates} ≠ 0 := by
  rw [{native}.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : ({native}.expression0).eval
      ({clean}.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : {case}.Input) :
    {source}.query{leaf}.materialized {coordinates} ∈ {case}.physicalRequests input 0 := by
  have member : {source}.query{leaf} ∈ {source}.genericQueries :=
    List.get_mem {source}.genericQueries ⟨{slot}, by decide⟩
  exact List.mem_map.mpr ⟨{source}.query{leaf}, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.{name}
'''
        emit(Path('Airbender/Proofs/GKRProtocol/ProgramDecoderNative') / f'{name}.lean', code)
        roots.extend(f'Airbender.Compiler.ProgramDecoderNative.{name}.{theorem}'
                     for theorem in ['decoder_tuple', 'decoder_enabled', 'decoder_member'])
        constructor = name[0].lower() + name[1:]
        if name.startswith('Unified'):
            parameters = '''{initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)'''
            factory = 'unifiedLookupRows initial columns'
            result = f'ProgramRows.maskRow mask {query} ∈ columns'
            choice = 'Or.inr rfl' if name.endswith('Cached') else 'Or.inl rfl'
            application = f'''NativeProgramSetup.unified_decoder_lookup setup .{constructor} _
    ({choice}) rfl index.val _ typed
  rw [NativeProgramSetup.unified_mask_eq setup]'''
        else:
            parameters = '''{config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : Trace.PooledFamily → ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)'''
            factory = 'unrolledLookupRows initial columns'
            result = f'ProgramRows.maskRow (masks .{family}) {query} ∈ columns .{family}'
            application = f'''NativeProgramSetup.unrolled_decoder_lookup setup .{constructor} .{family} _
    rfl rfl index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .{family}]'''
        code = f'''import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.{name}
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.{name}
import Airbender.Proofs.GKRProtocol.NativePublicDecoder

namespace Airbender.Compiler.ProgramDecoderLookup.{name}
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Exact native matching and arithmetic derive the public decoder lookup. -/
theorem decoder_lookup
    {parameters}
    (input : {case}.Input)
    (arguments : {case}.LookupArgumentsWith
      (fun group index => {factory} .{constructor} group index.val) input)
    (typed : {query}[0].val < 65536) : {result} := by
  obtain ⟨index, equal⟩ := {case}.source_member_with
    (fun group index => {factory} .{constructor} group index.val)
    input arguments 0 ({source}.query{leaf}.materialized {coordinates})
    (ProgramDecoderNative.{name}.decoder_member input)
    (ProgramDecoderNative.{name}.decoder_enabled input)
  have matched : {fields} = {factory} .{constructor} 0 index.val := equal
  apply {application}
  exact (ProgramDecoderNative.{name}.decoder_tuple input).symm.trans matched

end Airbender.Compiler.ProgramDecoderLookup.{name}
'''
        emit(Path('Airbender/Proofs/GKRProtocol/ProgramDecoderLookup') / f'{name}.lean', code)
        roots.append(f'Airbender.Compiler.ProgramDecoderLookup.{name}.decoder_lookup')
    return roots

def program_fixed_interfaces():
    roots = []
    for name in NAMES:
        owner = 'UnifiedRowNative' if name.startswith('Unified') else 'PooledRowNative'
        case = f'Airbender.Compiler.{owner}.{name}'
        constructor = name[0].lower() + name[1:]
        model = f'Airbender.Compiler.MaterializedNative.{name}.native.model'
        setup_columns = f'Airbender.Compiler.MaterializedWitnessNative.{name}.setupColumns'
        source = f'Airbender.Compiler.LookupSourceNative.{name}.native'
        coordinates = f'((input.physical ∘ {source}.bank.address) ∘ Airbender.Compiler.LookupNative.{name}.native.sourcePlacement)'
        tables = f'(fun group index => NativeProgramSetup.rows decoder wordAt .{constructor} group index.val)'
        parameters = f'''(decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith {tables} input)'''
        old = (ROOT / 'Airbender/Proofs/GKRProtocol/ProgramNativeTransport' / (name + '.lean')).read_text()
        helpers = old[old.index('theorem helpers_from_arguments'):old.index('theorem input_active')]
        helpers = helpers.replace('(input : Input) (arguments : LookupArguments input)', parameters)
        helpers = helpers.replace('physical_member input arguments 2',
                                  'fixed_group_member decoder wordAt input arguments 2 (by decide +kernel)')
        code = f'''import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.{name}
import Airbender.Proofs.GKRProtocol.ProgramSetupNative
import Airbender.Proofs.GKRProtocol.NativeProgramQueries

namespace Airbender.Compiler.ProgramFixedLookup.{name}
open Airbender Airbender.Compiler {case}
set_option warningAsError true
set_option Elab.async false

/-- Range and timestamp matching use the unchanged native setup groups. -/
theorem fixed_group_member
    {parameters}
    (group : Fin 3) (other : group.val ≠ 0) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    {model}.Contains ({setup_columns} group) query.fields := by
  obtain ⟨index, equal⟩ := source_member_with {tables}
    input arguments group query member enabled
  rw [NativeProgramSetup.rows_fixed_group decoder wordAt .{constructor} group index.val other] at equal
  refine ⟨index, ?_⟩
  simpa only [NativeProgramSetup.retainedRows, dif_pos index.isLt, {setup_columns}] using equal

theorem range_from_arguments
    {parameters} :
    ∀ query ∈ {source}.range16Queries,
      query.weight (RingHom.id _) {coordinates} ≠ 0 →
        {model}.Contains Airbender.Compiler.TableNative.{name}.native.range16SetupColumns
          (query.fields.map (fun field => field.value {coordinates})) := by
  intro query member enabled
  apply fixed_group_member decoder wordAt input arguments 1 (by decide +kernel)
    (query.materialized {coordinates}) ?_ enabled
  exact List.mem_map.mpr ⟨query, member, rfl⟩

{helpers}'''
        if name.startswith(('JumpBranch', 'MulDiv', 'ShiftBinop')):
            fields = f'query.fields.map (fun field => field.value {coordinates})'
            code += f'''
/-- Program rows cannot alter a lookup with a fixed helper tag. -/
theorem generic_from_arguments
    {parameters} (query : SourceLookupQuery) (member : query ∈ {source}.genericQueries)
    (nonzeroTag : ({fields}).getLast?.getD 0 ≠ 0)
    (notDecoder : ({fields}).getLast?.getD 0 ≠ 46)
    (notROM : ({fields}).getLast?.getD 0 ≠ 34)
    (enabled : query.weight (RingHom.id _) {coordinates} ≠ 0) :
    {model}.Contains Airbender.Compiler.TableNative.{name}.native.genericSetupColumns
      ({fields}) := by
  obtain ⟨index, equal⟩ := source_member_with {tables} input arguments 0
    (query.materialized {coordinates}) (List.mem_map.mpr ⟨query, member, rfl⟩) enabled
  have matched : ({fields}) = NativeProgramSetup.rows decoder wordAt .{constructor} 0 index.val := equal
  have fixedRow := NativeProgramSetup.fixed_member decoder wordAt .{constructor} _ rfl rfl
    index.val ({fields}) matched nonzeroTag notDecoder notROM
  refine ⟨index, ?_⟩
  simpa [NativeProgramSetup.retainedRows, index.isLt] using fixedRow
'''
            roots.append(f'Airbender.Compiler.ProgramFixedLookup.{name}.generic_from_arguments')
        code += f'''end Airbender.Compiler.ProgramFixedLookup.{name}
'''
        emit(Path('Airbender/Proofs/GKRProtocol/ProgramFixedLookup') / f'{name}.lean', code)
        roots.extend(f'Airbender.Compiler.ProgramFixedLookup.{name}.{theorem}'
                     for theorem in ['fixed_group_member', 'range_from_arguments', 'helpers_from_arguments'])
    return roots

def program_shift_tag_guards(name):
    constructor = name[0].lower() + name[1:]
    source = f'Airbender.Compiler.LookupSourceNative.{name}.native'
    clean = f'Airbender.Compiler.CleanGenericArgumentsNative.{name}.native'
    arithmetic = f'Airbender.Compiler.CleanArithmeticNative.{name}.native'
    code = f'''/-- The five helper requests use fixed tags, not decoder or ROM tags. -/
def FixedHelperTags (input : Input) : Prop :=
  ∀ index : Fin 5,
    let query := {source}.genericQueries.get
      ⟨index.val, by have small := index.isLt; change index.val < 6; omega⟩
    let tag := (query.fields.map (fun field => field.value
      ((input.physical ∘ {source}.bank.address) ∘
        Airbender.Compiler.LookupNative.{name}.native.sourcePlacement))).getLast?.getD 0
    tag ≠ 0 ∧ tag ≠ 46 ∧ tag ≠ 34

/-- Public program decoding and native arithmetic derive all helper tags. -/
theorem helper_guards
    {{config : Trace.NativeDecoder.ProgramRows.Config}} {{initial : Reference.RiscV.Sail.State}}
    {{text : List (BitVec 32)}} {{capacity : Nat}}
    {{masks : Trace.PooledFamily → Trace.NativeDecoder.ProgramRows.Mask}}
    {{columns : Trace.PooledFamily → List (List Source.BaseField)}}
    (programSetup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.unrolledLookupRows initial columns .{constructor} group index.val) input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) : FixedHelperTags input := by
  have matched := ProgramDecoderLookup.{name}.decoder_lookup programSetup input arguments typed
  have assertions : ∀ expression ∈ FlatOperation.constraints
      (ShiftBinop.importedConstraints (p := babyBearModulus)),
      expression.eval (Verification.environment (inputRow input).assignment) = 0 := by
    rw [Airbender.Compiler.CleanLinksNative.{name}.arithmetic_inventory]
    exact CleanExpression.assertions_only _ _
      ({arithmetic}.arithmetic_preserved input.physical (fun _ _ => #[]) input.arithmetic)
  have tags := public_shift_helper_tags programSetup (inputRow input).assignment matched typed assertions
  have tagEquations := shift_tag_equations_of_assertions assertions
  have firstTag : (8 * (inputRow input).assignment 11 + 3 * (inputRow input).assignment 12 ≠ 0) ∧
      (8 * (inputRow input).assignment 11 + 3 * (inputRow input).assignment 12 ≠ 46) ∧
      (8 * (inputRow input).assignment 11 + 3 * (inputRow input).assignment 12 ≠ 34) := by
    rcases tags.1 with selected | selected
    all_goals rw [selected]; exact of_decide_eq_true rfl
  have otherTag : (9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 ≠ 0) ∧
      (9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 ≠ 46) ∧
      (9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 ≠ 34) := by
    rcases tags.2 with selected | selected | selected | selected
    all_goals rw [selected]; exact of_decide_eq_true rfl
  intro index
  fin_cases index
'''
    for index in range(5):
        code += f'''  · have same : ({clean}.part0.genericExpression{index}_9).eval
        ({arithmetic}.environment input.physical (fun _ _ => #[])) =
        ((({source}.genericQueries.get ⟨{index}, by decide⟩).fields.map (fun field => field.value
          ((input.physical ∘ {source}.bank.address) ∘
            Airbender.Compiler.LookupNative.{name}.native.sourcePlacement))).getLast?.getD 0) :=
      {clean}.part0.generic_value{index}_9 input.physical (fun _ _ => #[]) input.arithmetic
    dsimp only
    rw [← same]
    simp [{clean}.part0.genericExpression{index}_9, _root_.Expression.eval]
    change (inputRow input).assignment {55 if index == 0 else 64 + 9 * (index - 1)} ≠ 0 ∧
      (inputRow input).assignment {55 if index == 0 else 64 + 9 * (index - 1)} ≠ 46 ∧
      (inputRow input).assignment {55 if index == 0 else 64 + 9 * (index - 1)} ≠ 34
    have equation : (inputRow input).assignment {55 if index == 0 else 64 + 9 * (index - 1)} =
        {"8 * (inputRow input).assignment 11 + 3 * (inputRow input).assignment 12" if index == 0 else "9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12"} :=
      {"tagEquations.1" if index == 0 else f"tagEquations.2 ⟨{index - 1}, by decide⟩"}
    rw [equation]
    exact {"firstTag" if index == 0 else "otherTag"}
'''
    return code + '\n'


def program_fixed_cpu_constraints():
    roots = []
    for name in [name for name in NAMES if name.startswith(('AddSub', 'JumpBranch', 'MulDiv', 'ShiftBinop'))]:
        shift = name.startswith('ShiftBinop')
        constructor = name[0].lower() + name[1:]
        case = f'Airbender.Compiler.PooledRowNative.{name}'
        tables = f'(fun group index => NativeProgramSetup.rows decoder wordAt .{constructor} group index.val)'
        parameters = f'''(decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith {tables} input)'''
        source = (ROOT / 'Airbender/Proofs/GKRProtocol/PhysicalClosedNative' / (name + '.lean')).read_text()
        ranges = source[source.index('theorem range_lookup0'):source.index('theorem retained_clock_from_physical')]
        entries = re.split(r'(?=theorem (?:range|generic)_lookup\d+\n)', ranges)
        code = f'''import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.{name}

namespace Airbender.Compiler.ProgramConstraintsNative.{name}
open Airbender Airbender.Compiler {case}
open Airbender.Compiler.PhysicalClosedNative.{name}
set_option warningAsError true
set_option Elab.async false

'''
        if shift:
            code = (f'import Airbender.Proofs.GKRProtocol.ProgramShiftTags\n'
                    f'import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.{name}\n' + code)
            code += program_shift_tag_guards(name)
        for entry in entries:
            if not entry.strip():
                continue
            theorem = re.search(r'^theorem ((?:range|generic)_lookup\d+)', entry)[1]
            target = entry[entry.index(' :\n', entry.index('(authored')) + len(' :\n'):]
            target = re.sub(r'\bphysical\b', 'input.physical', target)
            target = re.sub(r'\barithmetic\b', 'input.arithmetic', target)
            target = target.replace('authored.2 query',
                                    f'ProgramFixedLookup.{name}.range_from_arguments decoder wordAt input arguments query')
            target = target.replace('authored.1 query',
                                    f'ProgramFixedLookup.{name}.generic_from_arguments decoder wordAt input arguments query')
            if theorem.startswith('generic_'):
                index = int(theorem.removeprefix('generic_lookup'))
                guards = (f' (guards ⟨{index}, by decide⟩).1 (guards ⟨{index}, by decide⟩).2.1 (guards ⟨{index}, by decide⟩).2.2'
                          if shift else ' (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)')
                target = '\n'.join(line + guards
                                   if line.startswith('  have member :=') else line for line in target.splitlines()) + '\n\n'
            guard_parameter = ' (guards : FixedHelperTags input)' if shift and theorem.startswith('generic_') else ''
            code += f'private theorem {theorem}\n    {parameters}{guard_parameter} (data : ProverData Source.BaseField) :\n' + target
        body = source[source.index('theorem retained_clock_from_physical'):]
        body = body[body.index(' := by\n') + len(' := by\n'):body.index('\nend ')]
        body = re.sub(r'((?:range|generic)_lookup\d+) physical data arithmetic authored',
                      r'\1 decoder wordAt input arguments (fun _ _ => #[])', body)
        body = re.sub(r'\bphysical\b', 'input.physical', body)
        body = re.sub(r'\barithmetic\b', 'input.arithmetic', body)
        body = re.sub(r'\bdata\b', '(fun _ _ => #[])', body)
        body = body.replace('clock_lookup_inventory', f'Airbender.Compiler.PhysicalClosedNative.{name}.clock_lookup_inventory')
        if shift:
            body = re.sub(r'(generic_lookup\d+ decoder wordAt input arguments) ', r'\1 guards ', body)
            decoder = 'NativeProgramSetup.unrolledDecoderColumns columns'
            word_at = 'Trace.ROM.words initial'
            body = body.replace('decoder wordAt input arguments', f'({decoder}) ({word_at}) input arguments')
            parameters = f'''{{config : Trace.NativeDecoder.ProgramRows.Config}} {{initial : Reference.RiscV.Sail.State}}
    {{text : List (BitVec 32)}} {{capacity : Nat}}
    {{masks : Trace.PooledFamily → Trace.NativeDecoder.ProgramRows.Mask}}
    {{columns : Trace.PooledFamily → List (List Source.BaseField)}}
    (programSetup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.unrolledLookupRows initial columns .{constructor} group index.val) input)
    (typed : (inputRow input).decoderQuery[0].val < 65536)'''
            helpers = f'''  have helpers := ProgramFixedLookup.{name}.helpers_from_arguments
    ({decoder}) ({word_at}) input arguments
  have guards := helper_guards programSetup input arguments typed'''
            roots += [f'Airbender.Compiler.ProgramConstraintsNative.{name}.{suffix}'
                      for suffix in ['FixedHelperTags', 'helper_guards']]
        else:
            helpers = f'  have helpers := ProgramFixedLookup.{name}.helpers_from_arguments decoder wordAt input arguments'
        code += f'''/-- Native CPU constraints hold for any public program setup rows. -/
theorem input_constraints
    {parameters} (setup : Trace.PooledSetup babyBearModulus) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints setup) := by
{helpers}
{body}
end Airbender.Compiler.ProgramConstraintsNative.{name}
'''
        emit(Path('Airbender/Proofs/GKRProtocol/ProgramConstraintsNative') / (name + '.lean'), code)
        roots.append(f'Airbender.Compiler.ProgramConstraintsNative.{name}.input_constraints')
    return roots

def program_subword_constraints():
    roots = []
    for name in [name for name in NAMES if name.startswith('SubwordMemory')]:
        constructor = name[0].lower() + name[1:]
        case = f'Airbender.Compiler.PooledRowNative.{name}'
        source_model = f'Airbender.Compiler.LookupSourceNative.{name}.native'
        clean = f'Airbender.Compiler.CleanGenericArgumentsNative.{name}.native'
        arithmetic = f'Airbender.Compiler.CleanArithmeticNative.{name}.native'
        values = f'((input.physical ∘ {source_model}.bank.address) ∘ Airbender.Compiler.LookupNative.{name}.native.sourcePlacement)'
        tables = f'(fun group index => NativeProgramSetup.programRows decoder wordAt .{constructor} group index.val)'
        parameters = f'''(decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith {tables} input)'''
        code = f'''import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.{name}
import Airbender.Proofs.GKRProtocol.ProgramSubwordSetup
import Airbender.Proofs.GKRProtocol.ProgramSubwordTags
import Airbender.Proofs.GKRProtocol.ProgramSubwordDecoder
import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.{name}
import Airbender.Proofs.Tables.DecoderPCLow

namespace Airbender.Compiler.ProgramConstraintsNative.{name}
open Airbender Airbender.Compiler {case}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

'''
        fixed = (ROOT / 'Airbender/Proofs/GKRProtocol/ProgramFixedLookup' / (name + '.lean')).read_text()
        fixed = fixed[fixed.index('/-- Range and timestamp matching'):fixed.index('\nend ')]
        fixed = re.sub(r'^theorem ', 'private theorem ', fixed, flags=re.M)
        fixed = fixed.replace('NativeProgramSetup.rows ', 'NativeProgramSetup.programRows ')
        fixed = fixed.replace('NativeProgramSetup.rows_fixed_group', 'NativeProgramSetup.program_rows_fixed_group')
        code += fixed + '\n'
        original = (ROOT / 'Airbender/Proofs/GKRProtocol/PhysicalClosedNative' / (name + '.lean')).read_text()
        ranges = original[original.index('theorem range_lookup0'):original.index('theorem generic_lookup0')]
        for entry in re.split(r'(?=theorem range_lookup\d+\n)', ranges):
            if not entry.strip():
                continue
            theorem = re.search(r'^theorem (range_lookup\d+)', entry)[1]
            target = entry[entry.index(' :\n', entry.index('(authored')) + len(' :\n'):]
            target = re.sub(r'\bphysical\b', 'input.physical', target)
            target = re.sub(r'\barithmetic\b', 'input.arithmetic', target)
            target = target.replace('authored.2 query', 'range_from_arguments decoder wordAt input arguments query')
            code += f'private theorem {theorem}\n    {parameters} (data : ProverData Source.BaseField) :\n' + target
        for index in range(2):
            code += f'''private theorem generic_lookup{index}
    {parameters} ({"_notDecoder" if index == 0 else "notDecoder"} : (inputRow input).assignment 61 ≠ 46)
    (data : ProverData Source.BaseField) :
    (Lookup.mk (Verification.subwordTable wordAt).toRaw {clean}.genericExpressions{index}).Contains
      ({arithmetic}.environment input.physical data) := by
  let query := {source_model}.genericQueries.get ⟨{index}, by decide⟩
  have tagSame : ({clean}.part0.genericExpression{index}_8).eval
      ({arithmetic}.environment input.physical data) =
      (query.fields.map (fun field => field.value {values})).getLast?.getD 0 :=
    {clean}.part0.generic_value{index}_8 input.physical data input.arithmetic
  have guard : (query.fields.map (fun field => field.value {values})).getLast?.getD 0 ≠ 46 := by
    rw [← tagSame]
    simp [{clean}.part0.genericExpression{index}_8, _root_.Expression.eval]
'''
            if index == 0:
                code += '    exact of_decide_eq_true rfl\n'
            else:
                code += '    exact notDecoder\n'
            code += f'''  obtain ⟨nativeIndex, matched⟩ := source_member_with {tables} input arguments 0
    (query.materialized {values})
    (List.mem_map.mpr ⟨query, List.get_mem {source_model}.genericQueries ⟨{index}, by decide⟩, rfl⟩)
    one_ne_zero
  have matchedRow : (query.fields.map (fun field => field.value {values})) =
      NativeProgramSetup.subwordRows (decoder .{constructor}) wordAt nativeIndex.val := by
    simpa [NativeProgramSetup.programRows, SourceLookupQuery.materialized] using matched
  obtain ⟨row, equal⟩ := NativeProgramSetup.subword_query_member (decoder .{constructor}) wordAt
    nativeIndex.val _ matchedRow guard
'''
            for field in range(9):
                code += f'  have same{field} := {clean}.part0.generic_value{index}_{field} input.physical data input.arithmetic\n'
            code += f'''  apply clean_vector_lookup
  refine ⟨row, ?_⟩
  apply Vector.toList_inj.mp
  simp only [{clean}.genericExpressions{index}, Vector.map_mk, List.map_toArray]
  change [''' + ', '.join(f'({clean}.part0.genericExpression{index}_{field}).eval ({arithmetic}.environment input.physical data)' for field in range(9)) + '''] = _
  rw [''' + ', '.join('same' + str(field) for field in range(9)) + ''']
  exact equal

'''
        inventory = original[original.index('theorem clock_lookup_inventory'):original.index('theorem range_lookup0')]
        inventory = inventory.replace('theorem clock_lookup_inventory :', 'private theorem clock_lookup_inventory (wordAt : Nat → BitVec 32) :')
        inventory = inventory.replace('nativeSetup', '(Verification.subwordTable wordAt)')
        code += inventory
        body = original[original.index('theorem retained_clock_from_physical'):]
        body = body[body.index(' := by\n') + len(' := by\n'):body.index('\nend ')]
        body = re.sub(r'(range_lookup\d+) physical data arithmetic authored', r'\1 decoder wordAt input arguments (fun _ _ => #[])', body)
        body = re.sub(r'(generic_lookup\d+) physical data arithmetic authored', r'\1 decoder wordAt input arguments notDecoder (fun _ _ => #[])', body)
        body = re.sub(r'\bphysical\b', 'input.physical', body)
        body = re.sub(r'\barithmetic\b', 'input.arithmetic', body)
        body = re.sub(r'\bdata\b', '(fun _ _ => #[])', body)
        body = body.replace('nativeSetup', '(Verification.subwordTable wordAt)')
        code += f'''/-- Exact native matching proves subword constraints for the public ROM function. -/
theorem input_constraints
    {parameters} (wordSetup : Table Source.BaseField (fields 9)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨wordSetup, Verification.subwordTable wordAt⟩ : Trace.PooledSetup babyBearModulus)) := by
  have helpers := helpers_from_arguments decoder wordAt input arguments
  have assertions : ∀ expression ∈ FlatOperation.constraints (SubwordMemory.importedConstraints (Verification.subwordTable wordAt)),
      expression.eval (Verification.environment (inputRow input).assignment) = 0 := by
    rw [Airbender.Compiler.CleanLinksNative.{name}.arithmetic_inventory]
    exact CleanExpression.assertions_only _ _
      ({arithmetic}.arithmetic_preserved input.physical (fun _ _ => #[]) input.arithmetic)
  have notDecoder := subword_helper_not_decoder _ _ assertions
{body}

/-- Native range matching bounds the outgoing PC for the complete program factory. -/
theorem final_pc_low
    {parameters} : (inputRow input).finish.word.lo < 65536 :=
  Trace.NativeDecoder.Proofs.pooled_final_pc_low (by decide +kernel) (inputRow input)
    (⟨Verification.subwordTable wordAt, Verification.subwordTable wordAt⟩ : Trace.PooledSetup babyBearModulus)
    (input_constraints decoder wordAt input arguments (Verification.subwordTable wordAt))

/-- Exact native decoder matching uses the complete public subword setup. -/
theorem decoder_lookup
    {{config : Trace.NativeDecoder.ProgramRows.Config}} {{initial : Reference.RiscV.Sail.State}}
    {{text : List (BitVec 32)}} {{capacity : Nat}}
    {{masks : Trace.PooledFamily → Trace.NativeDecoder.ProgramRows.Mask}}
    {{columns : Trace.PooledFamily → List (List Source.BaseField)}}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.unrolledProgramLookupRows initial columns .{constructor} group index.val) input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    Trace.NativeDecoder.ProgramRows.maskRow (masks .subwordMemory) (inputRow input).decoderQuery ∈ columns .subwordMemory := by
  obtain ⟨index, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.unrolledProgramLookupRows initial columns .{constructor} group index.val)
    input arguments 0 ({source_model}.query12.materialized {values})
    (ProgramDecoderNative.{name}.decoder_member input) (ProgramDecoderNative.{name}.decoder_enabled input)
  have equal : {source_model}.query12.fields.map (fun field => field.value {values}) =
      NativeProgramSetup.unrolledProgramLookupRows initial columns .{constructor} 0 index.val := matched
  apply NativeProgramSetup.unrolled_subword_decoder_lookup setup .{constructor}
    ({"Or.inl" if name.endswith("Uncached") else "Or.inr"} rfl) index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .subwordMemory]
  exact (ProgramDecoderNative.{name}.decoder_tuple input).symm.trans equal

end Airbender.Compiler.ProgramConstraintsNative.{name}
'''
        emit(Path('Airbender/Proofs/GKRProtocol/ProgramConstraintsNative') / (name + '.lean'), code)
        roots.append(f'Airbender.Compiler.ProgramConstraintsNative.{name}.input_constraints')
        roots += [f'Airbender.Compiler.ProgramConstraintsNative.{name}.{suffix}'
                  for suffix in ['final_pc_low', 'decoder_lookup']]
    return roots


def program_word_constraints():
    roots = []
    for name in [name for name in NAMES if name.startswith('WordMemory')]:
        constructor = name[0].lower() + name[1:]
        case = f'Airbender.Compiler.PooledRowNative.{name}'
        source_model = f'Airbender.Compiler.LookupSourceNative.{name}.native'
        clean = f'Airbender.Compiler.CleanGenericArgumentsNative.{name}.native'
        arithmetic = f'Airbender.Compiler.CleanArithmeticNative.{name}.native'
        values = f'((input.physical ∘ {source_model}.bank.address) ∘ Airbender.Compiler.LookupNative.{name}.native.sourcePlacement)'
        tables = f'(fun group index => NativeProgramSetup.rows decoder wordAt .{constructor} group index.val)'
        range_parameters = f'''(decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith {tables} input)'''
        parameters = f'''{{initial : Reference.RiscV.Sail.State}}
    (decoder : Configuration → List (List Source.BaseField)) (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.rows decoder (Trace.ROM.words initial) .{constructor} group index.val) input)
    {{cells : List Trace.Cell}} {{tokens : List (Trace.MemoryToken babyBearModulus)}}
    (image : Trace.initialImage initial cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells)'''
        code = f'''import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.{name}
import Airbender.Proofs.GKRProtocol.ProgramWordROM
import Airbender.Proofs.GKRProtocol.ProgramWordTags

namespace Airbender.Compiler.ProgramConstraintsNative.{name}
open Airbender Airbender.Compiler {case}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

'''
        original = (ROOT / 'Airbender/Proofs/GKRProtocol/PhysicalClosedNative' / (name + '.lean')).read_text()
        ranges = original[original.index('theorem range_lookup0'):original.index('theorem generic_lookup0')]
        for entry in re.split(r'(?=theorem range_lookup\d+\n)', ranges):
            if not entry.strip():
                continue
            theorem = re.search(r'^theorem (range_lookup\d+)', entry)[1]
            target = entry[entry.index(' :\n', entry.index('(authored')) + len(' :\n'):]
            target = re.sub(r'\bphysical\b', 'input.physical', target)
            target = re.sub(r'\barithmetic\b', 'input.arithmetic', target)
            target = target.replace('authored.2 query', f'ProgramFixedLookup.{name}.range_from_arguments decoder wordAt input arguments query')
            code += f'private theorem {theorem}\n    {range_parameters} (data : ProverData Source.BaseField) :\n' + target
        code += f'''private theorem generic_lookup0
    {parameters} (notDecoder : (inputRow input).assignment 45 ≠ 46)
    (data : ProverData Source.BaseField) :
    (Lookup.mk (Trace.ROM.table cells tokens).toRaw {clean}.genericExpressions0).Contains
      ({arithmetic}.environment input.physical data) := by
  let query := {source_model}.genericQueries.get ⟨0, by decide⟩
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.rows decoder (Trace.ROM.words initial) .{constructor} group index.val) input arguments 0
    (query.materialized {values})
    (List.mem_map.mpr ⟨query, List.get_mem {source_model}.genericQueries ⟨0, by decide⟩, rfl⟩)
    one_ne_zero
'''
        for field in range(9):
            code += f'  have same{field} := {clean}.part0.generic_value0_{field} input.physical data input.arithmetic\n'
        code += f'''  let actual := {clean}.genericExpressions0.map
    (fun expression => expression.eval ({arithmetic}.environment input.physical data))
  have guard : actual[8] ≠ 46 := by
    simp [actual, {clean}.genericExpressions0,
      {clean}.part0.genericExpression0_8, _root_.Expression.eval]
    change (inputRow input).assignment 45 ≠ 46
    exact notDecoder
  apply clean_vector_lookup
  apply NativeProgramSetup.word_public_member image domain decoder .{constructor}
    ({"Or.inl" if name.endswith("Uncached") else "Or.inr"} rfl) nativeIndex actual ?_ guard
  simp only [actual, {clean}.genericExpressions0, Vector.map_mk, List.map_toArray]
  change [''' + ', '.join(f'({clean}.part0.genericExpression0_{field}).eval ({arithmetic}.environment input.physical data)' for field in range(9)) + '''] = _
  rw [''' + ', '.join('same' + str(field) for field in range(9)) + ''']
  exact matched

'''
        inventory = original[original.index('theorem clock_lookup_inventory'):original.index('theorem range_lookup0')]
        inventory = inventory.replace('theorem clock_lookup_inventory :', 'private theorem clock_lookup_inventory (rom : Table Source.BaseField (fields 9)) :')
        inventory = inventory.replace('nativeSetup', 'rom')
        code += inventory
        body = original[original.index('theorem retained_clock_from_physical'):]
        body = body[body.index(' := by\n') + len(' := by\n'):body.index('\nend ')]
        body = re.sub(r'(range_lookup\d+) physical data arithmetic authored', r'\1 decoder (Trace.ROM.words initial) input arguments (fun _ _ => #[])', body)
        body = body.replace('generic_lookup0 physical data arithmetic authored', 'generic_lookup0 decoder input arguments image domain notDecoder (fun _ _ => #[])')
        body = re.sub(r'\bphysical\b', 'input.physical', body)
        body = re.sub(r'\barithmetic\b', 'input.arithmetic', body)
        body = re.sub(r'\bdata\b', '(fun _ _ => #[])', body)
        body = body.replace('nativeSetup', '(Trace.ROM.table cells tokens)')
        code += f'''/-- Exact native matching proves word-memory constraints for the public image. -/
theorem input_constraints
    {parameters} (subwordSetup : Table Source.BaseField (fields 9)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨Trace.ROM.table cells tokens, subwordSetup⟩ : Trace.PooledSetup babyBearModulus)) := by
  have helpers := ProgramFixedLookup.{name}.helpers_from_arguments decoder (Trace.ROM.words initial) input arguments
  have assertions : ∀ expression ∈ FlatOperation.constraints (WordMemory.importedConstraints (Trace.ROM.table cells tokens)),
      expression.eval (Verification.environment (inputRow input).assignment) = 0 := by
    rw [Airbender.Compiler.CleanLinksNative.{name}.arithmetic_inventory]
    exact CleanExpression.assertions_only _ _
      ({arithmetic}.arithmetic_preserved input.physical (fun _ _ => #[]) input.arithmetic)
  have notDecoder := word_helper_not_decoder _ _ assertions
{body}
end Airbender.Compiler.ProgramConstraintsNative.{name}
'''
        emit(Path('Airbender/Proofs/GKRProtocol/ProgramConstraintsNative') / (name + '.lean'), code)
        roots.append(f'Airbender.Compiler.ProgramConstraintsNative.{name}.input_constraints')
    return roots


def program_unified_constraints():
    roots = []
    for name in [name for name in NAMES if name.startswith('Unified')]:
        constructor = name[0].lower() + name[1:]
        case = f'Airbender.Compiler.UnifiedRowNative.{name}'
        source_model = f'Airbender.Compiler.LookupSourceNative.{name}.native'
        clean = f'Airbender.Compiler.CleanGenericArgumentsNative.{name}.native'
        arithmetic = f'Airbender.Compiler.CleanArithmeticNative.{name}.native'
        values = f'((input.physical ∘ {source_model}.bank.address) ∘ Airbender.Compiler.LookupNative.{name}.native.sourcePlacement)'
        tables = f'(fun group index => NativeProgramSetup.rows decoder wordAt .{constructor} group index.val)'
        range_parameters = f'''(decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith {tables} input)'''
        generic_parameters = f'''(decoder : Configuration → List (List Source.BaseField))
    (initial : Reference.RiscV.Sail.State) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder
      (Trace.ROM.words initial) .{constructor} group index.val) input)
    (guards : ∀ index : Fin 5, (inputRow input).assignment (#v[82, 86, 95, 104, 113][index]) ≠ 46)'''
        code = f'''import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.{name}
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.{name}
import Airbender.Proofs.GKRProtocol.ProgramUnifiedDecoderTags
import Airbender.Proofs.GKRProtocol.ProgramUnifiedArithmeticTags
import Airbender.Proofs.GKRProtocol.ProgramUnifiedROM

namespace Airbender.Compiler.ProgramConstraintsNative.{name}
open Airbender Airbender.Compiler {case}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

'''
        original = (ROOT / 'Airbender/Proofs/GKRProtocol/PhysicalClosedNative' / (name + '.lean')).read_text()
        ranges = original[original.index('theorem range_lookup0'):original.index('theorem generic_lookup0')]
        for entry in re.split(r'(?=theorem range_lookup\d+\n)', ranges):
            if not entry.strip():
                continue
            theorem = re.search(r'^theorem (range_lookup\d+)', entry)[1]
            target = entry[entry.index(' :\n', entry.index('(authored')) + len(' :\n'):]
            target = re.sub(r'\bphysical\b', 'input.physical', target)
            target = re.sub(r'\barithmetic\b', 'input.arithmetic', target)
            target = target.replace('authored.2 query', f'ProgramFixedLookup.{name}.range_from_arguments decoder wordAt input arguments query')
            code += f'private theorem {theorem}\n    {range_parameters} (data : ProverData Source.BaseField) :\n' + target
        for index, tag_column in enumerate([82, 86, 95, 104, 113]):
            code += f'''private theorem generic_lookup{index}
    {generic_parameters} (data : ProverData Source.BaseField) :
    (Lookup.mk (UnifiedReduced.Setup.table initial).toRaw {clean}.genericExpressions{index}).Contains
      ({arithmetic}.environment input.physical data) := by
  let query := {source_model}.genericQueries.get ⟨{index}, by decide⟩
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.rows decoder (Trace.ROM.words initial) .{constructor} group index.val) input arguments 0
    (query.materialized {values})
    (List.mem_map.mpr ⟨query, List.get_mem {source_model}.genericQueries ⟨{index}, by decide⟩, rfl⟩)
    one_ne_zero
'''
            for field in range(10):
                code += f'  have same{field} := {clean}.part0.generic_value{index}_{field} input.physical data input.arithmetic\n'
            code += f'''  let actual := {clean}.genericExpressions{index}.map
    (fun expression => expression.eval ({arithmetic}.environment input.physical data))
  have guard : actual[9] ≠ 46 := by
    simp [actual, {clean}.genericExpressions{index},
      {clean}.part0.genericExpression{index}_9, _root_.Expression.eval]
    change (inputRow input).assignment {tag_column} ≠ 46
    exact guards ⟨{index}, by decide⟩
  apply clean_vector_lookup
  apply NativeProgramSetup.unified_public_member decoder initial .{constructor}
    ({"Or.inl" if name.endswith("Uncached") else "Or.inr"} rfl) nativeIndex actual ?_ guard
  simp only [actual, {clean}.genericExpressions{index}, Vector.map_mk, List.map_toArray]
  change [''' + ', '.join(f'({clean}.part0.genericExpression{index}_{field}).eval ({arithmetic}.environment input.physical data)' for field in range(10)) + '''] = _
  rw [''' + ', '.join('same' + str(field) for field in range(10)) + ''']
  exact matched

'''
        inventory = original[original.index('theorem clock_lookup_inventory'):original.index('theorem range_lookup0')]
        inventory = inventory.replace('theorem clock_lookup_inventory :', 'private theorem clock_lookup_inventory (setup : Table Source.BaseField (fields 10)) :')
        inventory = inventory.replace('nativeSetup', 'setup')
        code += inventory
        body = original[original.index('theorem retained_clock_from_physical'):]
        body = body[body.index(' := by\n') + len(' := by\n'):body.index('\nend ')]
        body = re.sub(r'(range_lookup\d+) physical data arithmetic authored', r'\1 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])', body)
        body = re.sub(r'(generic_lookup\d+) physical data arithmetic authored', r'\1 (NativeProgramSetup.unifiedDecoderColumns columns) initial input arguments guards (fun _ _ => #[])', body)
        body = re.sub(r'\bphysical\b', 'input.physical', body)
        body = re.sub(r'\barithmetic\b', 'input.arithmetic', body)
        body = re.sub(r'\bdata\b', '(fun _ _ => #[])', body)
        body = body.replace('nativeSetup', '(UnifiedReduced.Setup.table initial)')
        code += f'''/-- Public decoding and exact native matching prove all unified row constraints. -/
theorem input_constraints
    {{initial : Reference.RiscV.Sail.State}} {{text : List (BitVec 32)}} {{capacity : Nat}}
    {{mask : Trace.NativeDecoder.ProgramRows.Mask}} {{columns : List (List Source.BaseField)}}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.unifiedLookupRows initial columns .{constructor} group index.val) input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (UnifiedReduced.Setup.table initial)) := by
  have helpers := ProgramFixedLookup.{name}.helpers_from_arguments
    (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments
  have assertions : ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table initial)),
      expression.eval (Verification.environment (inputRow input).assignment) = 0 := by
    rw [Airbender.Compiler.CleanLinksNative.{name}.arithmetic_inventory]
    exact CleanExpression.assertions_only _ _
      ({arithmetic}.arithmetic_preserved input.physical (fun _ _ => #[]) input.arithmetic)
  have matched := ProgramDecoderLookup.{name}.decoder_lookup setup input arguments typed
  have operation := public_unified_operation setup (inputRow input).assignment matched typed
  have guards := UnifiedPublicConstraints.helper_not_decoder _ (inputRow input).assignment assertions input.active operation
{body}
end Airbender.Compiler.ProgramConstraintsNative.{name}
'''
        emit(Path('Airbender/Proofs/GKRProtocol/ProgramConstraintsNative') / (name + '.lean'), code)
        roots.append(f'Airbender.Compiler.ProgramConstraintsNative.{name}.input_constraints')
    return roots


def program_pc_bounds():
    roots = []
    direct = {'ShiftBinop': 0, 'WordMemory': 1, 'SubwordMemory': 3, 'Unified': 11}
    for name in NAMES:
        owner = 'UnifiedRowNative' if name.startswith('Unified') else 'PooledRowNative'
        case = f'Airbender.Compiler.{owner}.{name}'
        constructor = name[0].lower() + name[1:]
        tables = f'(fun group index => NativeProgramSetup.rows decoder wordAt .{constructor} group index.val)'
        parameters = f'''(decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith {tables} input)'''
        family = next((family for family in direct if name.startswith(family)), None)
        code = f'''import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.{name}
import Airbender.Proofs.Constraints
'''
        if family is None:
            code += f'''import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.{name}
import Airbender.Proofs.Tables.DecoderPCLow
'''
        code += f'''
namespace Airbender.Compiler.ProgramPCLowNative.{name}
open Airbender Airbender.Compiler {case}
set_option warningAsError true
set_option Elab.async false

'''
        if family is not None:
            decoder_source = (ROOT / 'Airbender/Proofs/GKRProtocol/DecoderArgumentsNative' / (name + '.lean')).read_text()
            trace_columns = re.search(r'\btrace_columns (\S+)', decoder_source)[1]
            source = (ROOT / 'Airbender/Proofs/GKRProtocol/PhysicalClosedNative' / (name + '.lean')).read_text()
            wanted = direct[family]
            entry = source[source.index(f'theorem range_lookup{wanted}\n'):]
            entry = entry[:entry.index('\ntheorem ', 1)]
            target = entry[entry.index(' :\n', entry.index('(authored')) + len(' :\n'):]
            target = re.sub(r'\bphysical\b', 'input.physical', target)
            target = re.sub(r'\barithmetic\b', 'input.arithmetic', target)
            target = target.replace('authored.2 query',
                                    f'ProgramFixedLookup.{name}.range_from_arguments decoder wordAt input arguments query')
            code += f'private theorem final_range_lookup\n    {parameters} (data : ProverData Source.BaseField) :\n' + target
            code += f'''
/-- Exact native range matching bounds the outgoing PC before decoder use. -/
theorem final_pc_low
    {parameters} : (inputRow input).finish.word.lo < 65536 := by
  change ((Airbender.Compiler.CleanArithmeticNative.{name}.native.environment input.physical
    (fun _ _ => #[])).get {trace_columns}.finalPC[0]).val < 65536
  simpa [Airbender.Compiler.CleanArgumentsNative.{name}.native.rangeExpression{wanted}, _root_.Expression.eval,
    {trace_columns}, Arithmetic.limbBase] using
    Verification.range16_bound (final_range_lookup decoder wordAt input arguments (fun _ _ => #[]))
'''
        else:
            code += f'''
theorem final_pc_low
    {parameters} (setup : Trace.PooledSetup babyBearModulus) :
    (inputRow input).finish.word.lo < 65536 :=
  Trace.NativeDecoder.Proofs.pooled_final_pc_low (by decide +kernel) (inputRow input) setup
    (ProgramConstraintsNative.{name}.input_constraints decoder wordAt input arguments setup)
'''
        code += f'\nend Airbender.Compiler.ProgramPCLowNative.{name}\n'
        emit(Path('Airbender/Proofs/GKRProtocol/ProgramPCLowNative') / (name + '.lean'), code)
        roots.append(f'Airbender.Compiler.ProgramPCLowNative.{name}.final_pc_low')
    return roots

for name in NAMES:
    prepared(name)
program_roots = program_row_interfaces()
setup_roots = program_setup_interfaces()
decoder_roots = program_decoder_interfaces()
fixed_roots = program_fixed_interfaces()
constraint_roots = program_fixed_cpu_constraints()
constraint_roots += program_subword_constraints()
constraint_roots += program_word_constraints()
constraint_roots += program_unified_constraints()
pc_roots = program_pc_bounds()
shift_roots = ['Airbender.Compiler.' + name for name in [
    'public_program_full_fields', 'public_program_shift_source',
    'shift_flags_of_assertions', 'shift_tag_equations_of_assertions',
    'public_shift_helper_tags']]
subword_roots = ['Airbender.Compiler.NativeProgramSetup.' + name for name in [
    'subwordRows', 'programRows', 'subword_geometry', 'subword_zero_row',
    'subword_query_member', 'program_rows_fixed_group']]
subword_roots += ['Airbender.SubwordMemory.Proofs.subword_flags_of_assertions',
                  'Airbender.Compiler.subword_helper_not_decoder']
subword_roots += ['Airbender.Compiler.NativeProgramSetup.' + name for name in [
    'unrolledProgramLookupRows', 'subword_prefix_not_decoder',
    'subword_decoder_member', 'unrolled_subword_decoder_lookup']]
public_row_roots = ['Airbender.Compiler.PooledExecution.' + name for name in [
    'ProgramLogicalRowCertificate.program_decoder_lookup',
    'program_decoder_exact_lookup',
    'ProgramLogicalRowCertificate.program_final_pc_low',
    'program_native_query_pc_low', 'program_decoder_exact_lookup_from_native']]
word_roots = ['Airbender.Reference.Compiler.ProgramSetup.fixed_query_or_zero',
              'Airbender.Compiler.word_helper_not_decoder',
              'Airbender.WordMemory.Proofs.word_flags_of_assertions']
word_roots += ['Airbender.Compiler.NativeProgramSetup.' + name for name in [
    'fixed_or_zero_member', 'vector_nine_last', 'fixed_word_query_zero',
    'word_query_member', 'word_public_member']]
word_roots += ['Airbender.Compiler.PooledExecution.' + name for name in [
    'ProgramLogicalRowCertificate.program_constraints',
    'program_row_constraints_from_native']]
unified_roots = ['Airbender.Compiler.public_unified_field_tags',
                 'Airbender.Compiler.public_unified_operation',
                 'Airbender.UnifiedReduced.Proofs.unified_flags_of_assertions',
                 'Airbender.UnifiedReduced.Proofs.unified_dispatch_count_of_assertions',
                 'Airbender.Compiler.UnifiedPublicConstraints.helper_not_decoder']
unified_roots += ['Airbender.Compiler.NativeProgramSetup.' + name for name in [
    'vector_ten_last', 'unified_fixed_query_member', 'unified_zero_member',
    'unified_public_member']]
unified_roots += ['Airbender.Compiler.UnifiedExecution.' + name for name in [
    'ProgramLogicalRowCertificate.program_constraints',
    'program_row_constraints_from_native']]
acceptance_roots = ['Airbender.Compiler.MachineTargets.' + name for name in [
    'UnrolledNativeArguments', 'UnifiedNativeArguments',
    'unrolled_acceptance_from_native', 'unified_acceptance_from_native']]
decode_roots = ['Airbender.Trace.NativeDecoder.ProgramRows.decodeWord',
                'Airbender.Trace.NativeDecoder.ProgramRows.Proofs.decode_word_sound',
                'Airbender.Trace.NativeDecoder.ProgramRows.Proofs.program_code']

packed_table_roots = ['Airbender.Setup.packedByte',
 'Airbender.Setup.packedArray',
 'Airbender.Setup.PackedBlock',
 'Airbender.Setup.PackedBlock.decode',
 'Airbender.Setup.PackedBlock.length',
 'Airbender.Setup.PackedRunInput',
 'Airbender.Setup.PackedBlock.input',
 'Airbender.Setup.Proofs.PackedColumn.digit',
 'Airbender.Setup.Proofs.PackedColumn.bytePower',
 'Airbender.Setup.Proofs.PackedColumn.bytePower_eq',
 'Airbender.Setup.Proofs.PackedColumn.segment_digit',
 'Airbender.Setup.Proofs.PackedRadix.extractDigitBase',
 'Airbender.Setup.Proofs.PackedRun.ones',
 'Airbender.Setup.Proofs.PackedRun.positions',
 'Airbender.Setup.Proofs.PackedRun.linear_digits',
 'Airbender.Setup.Proofs.PackedRun.translated_digits',
 'Airbender.Setup.Proofs.PackedRun.Run',
 'Airbender.Setup.Proofs.PackedRun.Run.length',
 'Airbender.Setup.Proofs.PackedRun.Run.value',
 'Airbender.Setup.Proofs.PackedRun.Run.valid',
 'Airbender.Setup.Proofs.PackedRun.Run.row',
 'Airbender.Setup.Proofs.PackedRun.Run.packed',
 'Airbender.Setup.Proofs.PackedRun.row_linear',
 'Airbender.Setup.Proofs.PackedRun.packed_rows',
 'Airbender.Setup.Proofs.PackedRun.row_values_bounded',
 'Airbender.Setup.Proofs.PackedRun.packed_byte',
 'Airbender.Setup.Proofs.PackedRun.ones_succ',
 'Airbender.Setup.Proofs.PackedRun.positions_succ',
 'Airbender.Setup.Proofs.PackedRun.geometric_identity',
 'Airbender.Setup.Proofs.PackedRun.moment_identity',
 'Airbender.Setup.Proofs.PackedRun.geometric_closed',
 'Airbender.Setup.Proofs.PackedRun.moment_closed',
 'Airbender.Setup.Proofs.PackedRun.Run.packedArithmetic',
 'Airbender.Setup.Proofs.PackedRun.packedArithmetic_eq',
 'Airbender.Setup.Proofs.PackedRun.packedArithmetic_byte',
 'Airbender.Setup.Proofs.PackedRunColumn.ofBlock',
 'Airbender.Setup.Proofs.PackedRunColumn.ofBlock_sound',
 'Airbender.Setup.Proofs.PackedPayload.packedByte_eq',
 'Airbender.Setup.Proofs.PackedPayload.packedArray_get',
 'Airbender.Setup.Proofs.PackedPayload.payload_roundtrip',
 'Airbender.Setup.PackedRunInput.length',
 'Airbender.Setup.PackedRunInput.asRun',
 'Airbender.Setup.PackedRunInput.valid',
 'Airbender.Setup.PackedRunInput.packed',
 'Airbender.Setup.Proofs.PackedPayload.run_length',
 'Airbender.Setup.Proofs.PackedPayload.valid_sound',
 'Airbender.Setup.Proofs.PackedPayload.packed_sound',
 'Airbender.Setup.Proofs.PackedWindows.window',
 'Airbender.Setup.Proofs.PackedWindows.span',
 'Airbender.Setup.Proofs.PackedWindows.legal',
 'Airbender.Setup.Proofs.PackedWindows.window_low',
 'Airbender.Setup.Proofs.PackedWindows.window_high',
 'Airbender.Setup.Proofs.PackedWindows.span_byte',
 'Airbender.Setup.Proofs.PackedBlockCertificate.decode_length',
 'Airbender.Setup.Proofs.PackedBlockCertificate.input_length',
 'Airbender.Setup.Proofs.PackedBlockCertificate.input_raw',
 'Airbender.Setup.Proofs.PackedBlockCertificate.checkBlock',
 'Airbender.Setup.Proofs.PackedBlockCertificate.check',
 'Airbender.Setup.Proofs.PackedBlockCertificate.checkBlock_sound',
 'Airbender.Setup.Proofs.PackedBlockCertificate.check_sound',
 'Airbender.Verification.byteAndPackedBlocks',
 'Airbender.Verification.byteAndPackedBlocksSourceBytes',
 'Airbender.Verification.ShiftPackedCertificate.source_binding',
 'Airbender.Verification.ShiftPackedCertificate.same_source_bytes',
 'Airbender.Verification.ShiftPackedCertificate.check',
 'Airbender.Verification.ShiftPackedCertificate.ok',
 'Airbender.Verification.ShiftPackedCertificate.check_sound',
 'Airbender.Verification.ShiftPackedCertificate.and_outputs',
 'Tests.PackedTableCertificates.first_nonzero_byte',
 'Tests.PackedTableCertificates.changed_byte_rejected',
 'Tests.PackedTableCertificates.little_endian_payload',
 'Tests.PackedTableCertificates.reversed_bytes_rejected',
 'Tests.PackedTableCertificates.extra_payload_byte_rejected',
 'Tests.PackedTableCertificates.periodic_source',
 'Tests.PackedTableCertificates.affine_source',
 'Tests.PackedTableCertificates.row_boundary',
 'Tests.PackedTableCertificates.last_source_byte',
 'Tests.PackedTableCertificates.outside_table_rejected',
 'Airbender.Verification.byteAndDataPackedColumn2',
 'Airbender.Setup.PackedBlock.affine',
 'Airbender.Setup.PackedBlock.dense',
 'Airbender.Setup.PackedBlock.periodic',
 'Airbender.Setup.PackedRunInput.mk',
 'Airbender.Setup.PackedRunInput.count',
 'Airbender.Setup.PackedRunInput.stride',
 'Airbender.Setup.PackedRunInput.period',
 'Airbender.Setup.PackedRunInput.payload',
 'Airbender.Setup.Proofs.PackedRun.Run.mk',
 'Airbender.Setup.Proofs.PackedRun.Run.count',
 'Airbender.Setup.Proofs.PackedRun.Run.stride',
 'Airbender.Setup.Proofs.PackedRun.Run.values',
 'Airbender.Verification.ShiftPackedCertificate.coverage',
 'Airbender.UnifiedReduced.Setup.nativeAndDataPackedColumn2']

packed_setup_roots = ['Airbender.Compiler.PackedSetupEquality.bytes',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.decode',
 'Airbender.Compiler.PackedSetupEquality.BlockCode.decode',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.length',
 'Airbender.Compiler.PackedSetupEquality.BlockCode.length',
 'Airbender.Compiler.PackedSetupEquality.bytes_length',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.decode_length',
 'Airbender.Compiler.PackedSetupEquality.BlockCode.decode_length',
 'Airbender.Compiler.PackedSetupEquality.rowCount',
 'Airbender.Compiler.PackedSetupEquality.rowCount_eq',
 'Airbender.Compiler.PackedSetupEquality.check',
 'Airbender.Compiler.PackedSetupEquality.check_sound',
 'Airbender.Compiler.PackedSetupEquality.checkWithLengths',
 'Airbender.Compiler.PackedSetupEquality.checkWithLengths_sound',
 'Airbender.Compiler.PackedSetupEquality.select_middle',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.literal',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.append',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.constant',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.range',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.linear',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.rotate',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.linearRuns',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.lookupRuns',
 'Airbender.Compiler.PackedSetupEquality.ArrayCode.packedBytes',
 'Airbender.Compiler.PackedSetupEquality.BlockCode',
 'Airbender.Compiler.PackedSetupEquality.BlockCode.affine',
 'Airbender.Compiler.PackedSetupEquality.BlockCode.dense',
 'Airbender.Compiler.PackedSetupEquality.BlockCode.periodic',
 'Airbender.Compiler.PackedSetupEquality.LengthCheck',
 'Airbender.Compiler.PackedSetupEquality.LengthCheck.mk',
 'Airbender.Compiler.PackedSetupEquality.LengthCheck.first',
 'Airbender.Compiler.PackedSetupEquality.LengthCheck.count',
 'Airbender.Compiler.PackedSetupEquality.LengthCheck.expected',
 'Airbender.Compiler.UnifiedPackedEquality.sourceCode',
 'Airbender.Compiler.UnifiedPackedEquality.xorCode',
 'Airbender.Compiler.UnifiedPackedEquality.orCode',
 'Airbender.Compiler.UnifiedPackedEquality.andCode',
 'Airbender.Compiler.UnifiedPackedEquality.targetCode',
 'Airbender.Compiler.UnifiedPackedEquality.lengthChecks',
 'Airbender.Compiler.UnifiedPackedEquality.rawPrefix',
 'Airbender.Compiler.UnifiedPackedEquality.rawOriginal',
 'Airbender.Compiler.UnifiedPackedEquality.rawSuffix',
 'Airbender.Compiler.UnifiedPackedEquality.sourceLayout',
 'Airbender.Compiler.UnifiedPackedEquality.raw_source_binding',
 'Airbender.Compiler.UnifiedPackedEquality.source_binding',
 'Airbender.Compiler.UnifiedPackedEquality.rawXorPrefix',
 'Airbender.Compiler.UnifiedPackedEquality.rawXor',
 'Airbender.Compiler.UnifiedPackedEquality.xorLayout',
 'Airbender.Compiler.UnifiedPackedEquality.rawOr',
 'Airbender.Compiler.UnifiedPackedEquality.orLayout',
 'Airbender.Compiler.UnifiedPackedEquality.rawAnd',
 'Airbender.Compiler.UnifiedPackedEquality.andLayout',
 'Airbender.Compiler.UnifiedPackedEquality.raw_target_binding',
 'Airbender.Compiler.UnifiedPackedEquality.target_binding',
 'Airbender.Compiler.UnifiedPackedEquality.ok',
 'Airbender.Compiler.UnifiedPackedEquality.fixed_column_blocks',
 'Airbender.Compiler.UnifiedPackedEquality.row_counts',
 'Tests.PackedSetupEquality.literal_bytes',
 'Tests.PackedSetupEquality.constant_array',
 'Tests.PackedSetupEquality.range_array',
 'Tests.PackedSetupEquality.linear_array',
 'Tests.PackedSetupEquality.rotated_array',
 'Tests.PackedSetupEquality.repeated_runs',
 'Tests.PackedSetupEquality.indexed_runs',
 'Tests.PackedSetupEquality.adopted_byte_array',
 'Tests.PackedSetupEquality.signed_stride',
 'Tests.PackedSetupEquality.changed_stride_rejected',
 'Tests.PackedSetupEquality.changed_byte_rejected',
 'Tests.PackedSetupEquality.row_count_checked',
 'Tests.PackedSetupEquality.changed_row_count_rejected',
 'Airbender.Compiler.PackedSetupEquality.slice_split',
 'Airbender.Compiler.UnifiedPackedEquality.sourceBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.targetBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.blocks_eq',
 'Airbender.Compiler.UnifiedPackedEquality.slice_eq',
 'Airbender.Compiler.UnifiedPackedEquality.length_at']

packed_setup_roots += ['Airbender.Compiler.PackedSetupEquality.CodeTree',
 'Airbender.Compiler.PackedSetupEquality.CodeTree.blocks',
 'Airbender.Compiler.PackedSetupEquality.CodeTree.size',
 'Airbender.Compiler.PackedSetupEquality.CodeTree.valid',
 'Airbender.Compiler.PackedSetupEquality.CodeTree.size_sound',
 'Airbender.Compiler.PackedSetupEquality.CodeTree.rowCount',
 'Airbender.Compiler.PackedSetupEquality.CodeTree.rowCount_sound',
 'Airbender.Compiler.PackedSetupEquality.checkTree',
 'Airbender.Compiler.PackedSetupEquality.checkTree_sound',
 'Tests.PackedSetupTree.valid_metadata',
 'Tests.PackedSetupTree.changed_metadata_rejected',
 'Tests.PackedSetupTree.complete_rows',
 'Tests.PackedSetupTree.crossing_rows',
 'Tests.PackedSetupTree.right_rows',
 'Tests.PackedSetupTree.empty_rows',
 'Tests.PackedSetupTree.clipped_rows',
 'Tests.PackedSetupTree.past_end_rows',
 'Tests.PackedSetupTree.wrong_rows_rejected',
 'Tests.PackedSetupTree.changed_byte_rejected',
 'Tests.PackedSetupTree.changed_stride_rejected',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.sourceCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.targetCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.lengthChecks',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.raw_source0_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.raw_source1_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.source0_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.source1_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.source_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.raw_shift_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.shift_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.raw_rotate8_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.rotate8_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.raw_rotate7_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.rotate7_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.target_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.source_tree_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.target_tree_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.ok',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.checked_facts',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.sourceBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.targetBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.blocks_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.slice_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.length_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.fixed_column_blocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.row_counts',
 'Airbender.Compiler.PackedSetupEquality.CodeTree.leaf',
 'Airbender.Compiler.PackedSetupEquality.CodeTree.branch',
 'Airbender.Compiler.PackedSetupEquality.instBEqArrayCode',
 'Airbender.Compiler.PackedSetupEquality.instReflBEqArrayCode',
 'Airbender.Compiler.PackedSetupEquality.instLawfulBEqArrayCode',
 'Airbender.Compiler.PackedSetupEquality.instBEqBlockCode',
 'Airbender.Compiler.PackedSetupEquality.instReflBEqBlockCode',
 'Airbender.Compiler.PackedSetupEquality.instLawfulBEqBlockCode',
 'Airbender.Compiler.PackedSetupEquality.instBEqCodeTree',
 'Airbender.Compiler.PackedSetupEquality.instReflBEqCodeTree',
 'Airbender.Compiler.PackedSetupEquality.instLawfulBEqCodeTree',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.source0',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.source1',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.shiftCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.rotate8Code',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.rotate7Code',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.sourceTree',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.targetTree',
 'Airbender.Compiler.PackedSetupEquality.CodeTree.chunk',
 'Airbender.Compiler.PackedSetupEquality.decoded_row_sum',
 'Airbender.Compiler.PackedSetupEquality.checkTree_codes_eq',
 'Airbender.Compiler.PackedSetupEquality.checkTree_rows',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.sourceChunk',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.targetChunk',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.chunk_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.tree_rows_at',
 'Tests.PackedSetupTree.application_view_binding',
 'Airbender.Compiler.PackedSetupEquality.checkTreeWithChunks',
 'Airbender.Compiler.PackedSetupEquality.checkTreeWithChunks_base',
 'Airbender.Compiler.PackedSetupEquality.checkTreeWithChunks_chunk_length',
 'Airbender.Compiler.PackedSetupEquality.checkTreeWithChunks_sound',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.tree_ok',
 'Airbender.Compiler.UnifiedPackedEquality.Column5.chunk_length_at',
 'Tests.PackedSetupTree.projection_rows',
 'Tests.PackedSetupTree.incomplete_leaf_rejected',
 'Airbender.Compiler.PackedSetupEquality.take_drop_append',
 'Tests.PackedSetupTreeLayout.tree',
 'Tests.PackedSetupTreeLayout.exact_layout',
 'Tests.PackedSetupTreeLayout.valid_layout']

packed_setup_roots += ['Airbender.Compiler.UnifiedPackedEquality.Column4.sourceCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.targetCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.lengthChecks',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.source0',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.source1',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.shiftCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rotate16Code',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rotate12Code',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.sourceTree',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.source_tree_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.targetTree',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.target_tree_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawPrefix',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawSource0',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawGap1',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawSource1',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawSuffix',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.sourceLayout',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.raw_source0_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.raw_source1_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.source0_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.source1_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.source_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawShiftPrefix',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawShift',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawShiftSuffix',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.shiftLayout',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.raw_shift_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.shift_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawRotate16Prefix',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawRotate16',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rotate16Layout',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.raw_rotate16_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rotate16_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawRotate12',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rawRotate12Suffix',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rotate12Layout',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.raw_rotate12_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.rotate12_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.target_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.ok',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.tree_ok',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.checked_facts',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.sourceBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.targetBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.blocks_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.slice_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.length_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.sourceChunk',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.targetChunk',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.chunk_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.tree_rows_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.chunk_length_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.fixed_column_blocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column4.row_counts',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.sourceCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.targetCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.lengthChecks',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.source0',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.shiftCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.sourceTree',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.source_tree_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.targetTree',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.target_tree_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.rawPrefix',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.rawSource0',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.rawSuffix',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.sourceLayout',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.raw_source0_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.source0_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.source_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.rawShiftPrefix',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.rawShift',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.rawShiftSuffix',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.shiftLayout',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.raw_shift_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.shift_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.target_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.ok',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.tree_ok',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.checked_facts',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.sourceBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.targetBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.blocks_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.slice_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.length_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.sourceChunk',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.targetChunk',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.chunk_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.tree_rows_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.chunk_length_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.fixed_column_blocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column6.row_counts',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.sourceCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.targetCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.lengthChecks',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.source0',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.shiftCode',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.sourceTree',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.source_tree_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.targetTree',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.target_tree_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.rawPrefix',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.rawSource0',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.rawSuffix',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.sourceLayout',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.raw_source0_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.source0_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.source_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.rawShiftPrefix',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.rawShift',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.rawShiftSuffix',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.shiftLayout',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.raw_shift_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.shift_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.target_binding',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.ok',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.tree_ok',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.checked_facts',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.sourceBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.targetBlocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.blocks_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.slice_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.length_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.sourceChunk',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.targetChunk',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.chunk_eq',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.tree_rows_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.chunk_length_at',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.fixed_column_blocks',
 'Airbender.Compiler.UnifiedPackedEquality.Column7.row_counts']

packed_arithmetic_roots = ['Airbender.Compiler.AddressUniqueChecks.addressCode',
 'Airbender.Compiler.AddressUniqueChecks.ascendingFrom',
 'Airbender.Compiler.AddressUniqueChecks.ascendingFrom_sound',
 'Airbender.Compiler.AddressUniqueChecks.ascending',
 'Airbender.Compiler.AddressUniqueChecks.ascending_sound',
 'Airbender.Compiler.AddressUniqueChecks.check',
 'Airbender.Compiler.AddressUniqueChecks.check_sound',
 'Airbender.Compiler.AddressUniqueChecks.distinctAt_complete',
 'Airbender.Compiler.FastPolynomialChecks.insertTerm',
 'Airbender.Compiler.FastPolynomialChecks.insertTerm_eq',
 'Airbender.Compiler.FastPolynomialChecks.normalize',
 'Airbender.Compiler.FastPolynomialChecks.normalize_eq',
 'Airbender.Compiler.FastPolynomialChecks.equal',
 'Airbender.Compiler.FastPolynomialChecks.equal_eq',
 'Airbender.Compiler.FullArithmeticChecks.allFin',
 'Airbender.Compiler.FullArithmeticChecks.allFin_eq',
 'Airbender.Compiler.FullArithmeticChecks.translationCheck',
 'Airbender.Compiler.FullArithmeticChecks.translationCheck_eq',
 'Airbender.Compiler.FullArithmeticChecks.check',
 'Airbender.Compiler.FullArithmeticChecks.checked_parts',
 'Airbender.Compiler.FullArithmeticChecks.check_sound',
 'Airbender.Compiler.FullArithmeticChecks.unique_at',
 'Airbender.Compiler.FullArithmeticChecks.relation_at',
 'Airbender.Compiler.FullArithmeticChecks.source_at',
 'Airbender.Compiler.FullArithmeticChecks.source_at_original',
 'Airbender.Compiler.FullArithmeticChecks.gate_at',
 'Tests.PackedArithmeticChecks.identityArtifact',
 'Tests.PackedArithmeticChecks.identityCertificate',
 'Tests.PackedArithmeticChecks.identity_accepted',
 'Tests.PackedArithmeticChecks.duplicate_address_rejected',
 'Tests.PackedArithmeticChecks.address_constructors_distinct',
 'Tests.PackedArithmeticChecks.missing_backward_rejected',
 'Tests.PackedArithmeticChecks.missing_forward_rejected',
 'Tests.PackedArithmeticChecks.changedGate',
 'Tests.PackedArithmeticChecks.changed_gate_rejected',
 'Tests.PackedArithmeticChecks.changedProjection',
 'Tests.PackedArithmeticChecks.changed_projection_rejected',
 'Airbender.Compiler.FullArithmeticNative.AddSubCached.native.captureChecked',
 'Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.captureChecked']

packed_arithmetic_roots += ['Airbender.Compiler.NumericPolynomialChecks.Data',
 'Airbender.Compiler.NumericPolynomialChecks.encode',
 'Airbender.Compiler.NumericPolynomialChecks.monomialCompare',
 'Airbender.Compiler.NumericPolynomialChecks.insertTerm',
 'Airbender.Compiler.NumericPolynomialChecks.normalize',
 'Airbender.Compiler.NumericPolynomialChecks.equal',
 'Airbender.Compiler.NumericPolynomialChecks.multiply',
 'Airbender.Compiler.NumericPolynomialChecks.rename',
 'Airbender.Compiler.NumericPolynomialChecks.substitute',
 'Airbender.Compiler.NumericPolynomialChecks.combination',
 'Airbender.Compiler.NumericPolynomialChecks.monomial_injective',
 'Airbender.Compiler.NumericPolynomialChecks.encode_injective',
 'Airbender.Compiler.NumericPolynomialChecks.compare_encode',
 'Airbender.Compiler.NumericPolynomialChecks.encode_insertTerm',
 'Airbender.Compiler.NumericPolynomialChecks.encode_normalize',
 'Airbender.Compiler.NumericPolynomialChecks.equal_encode',
 'Airbender.Compiler.NumericPolynomialChecks.encode_append',
 'Airbender.Compiler.NumericPolynomialChecks.encode_atom',
 'Airbender.Compiler.NumericPolynomialChecks.encode_multiply',
 'Airbender.Compiler.NumericPolynomialChecks.encode_rename',
 'Airbender.Compiler.NumericPolynomialChecks.encode_substitute',
 'Airbender.Compiler.NumericPolynomialChecks.encodeCombination',
 'Airbender.Compiler.NumericPolynomialChecks.encode_combination',
 'Airbender.Compiler.NumericPolynomialChecks.canonical',
 'Airbender.Compiler.NumericPolynomialChecks.isUnit',
 'Airbender.Compiler.NumericPolynomialChecks.isUnit_iff',
 'Airbender.Compiler.NumericPolynomialChecks.multiply_unit_left',
 'Airbender.Compiler.NumericPolynomialChecks.multiply_unit_right',
 'Airbender.Compiler.NumericPolynomialChecks.fastMultiply',
 'Airbender.Compiler.NumericPolynomialChecks.fastMultiply_eq',
 'Airbender.Compiler.NumericPolynomialChecks.initial',
 'Airbender.Compiler.NumericPolynomialChecks.product_inputs',
 'Airbender.Compiler.NumericPolynomialChecks.fastSubstitute',
 'Airbender.Compiler.NumericPolynomialChecks.fastSubstitute_eq',
 'Airbender.Compiler.NumericPolynomialChecks.fastEqual',
 'Airbender.Compiler.NumericPolynomialChecks.fastEqual_eq',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.size',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.toList',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.valid',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.getD',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.ofList',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.toList_ofList',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.size_ofList',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.valid_ofList',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.size_eq_length',
 'Airbender.Compiler.NumericPolynomialChecks.LookupTable.getD_eq',
 'Airbender.Compiler.NumericArithmeticChecks.Capture',
 'Airbender.Compiler.NumericArithmeticChecks.Capture.extension',
 'Airbender.Compiler.NumericArithmeticChecks.combine',
 'Airbender.Compiler.NumericArithmeticChecks.combine_eq',
 'Airbender.Compiler.NumericArithmeticChecks.translationCheck',
 'Airbender.Compiler.NumericArithmeticChecks.gateCheck',
 'Airbender.Compiler.NumericArithmeticChecks.layoutCheck',
 'Airbender.Compiler.NumericArithmeticChecks.Layout',
 'Airbender.Compiler.NumericArithmeticChecks.layout_sound',
 'Airbender.Compiler.NumericArithmeticChecks.check',
 'Airbender.Compiler.NumericArithmeticChecks.gateInput',
 'Airbender.Compiler.NumericArithmeticChecks.gateOutput',
 'Airbender.Compiler.NumericArithmeticChecks.gate_check_eq',
 'Airbender.Compiler.NumericArithmeticChecks.Bindings',
 'Airbender.Compiler.NumericArithmeticChecks.mapped_size',
 'Airbender.Compiler.NumericArithmeticChecks.mapped_getD',
 'Airbender.Compiler.NumericArithmeticChecks.vector_getD',
 'Airbender.Compiler.NumericArithmeticChecks.initial_extension',
 'Airbender.Compiler.NumericArithmeticChecks.map_encode_normalize',
 'Airbender.Compiler.NumericArithmeticChecks.encode_rename_prefix',
 'Airbender.Compiler.NumericArithmeticChecks.translation_valid',
 'Airbender.Compiler.NumericArithmeticChecks.gates_checked',
 'Airbender.Compiler.NumericArithmeticChecks.check_sound',
 'Airbender.Compiler.NumericArithmeticChecks.full_check',
 'Tests.NumericArithmeticChecks.identityArtifact',
 'Tests.NumericArithmeticChecks.identityCertificate',
 'Tests.NumericArithmeticChecks.identityData',
 'Tests.NumericArithmeticChecks.identity_checked',
 'Tests.NumericArithmeticChecks.identity_binding',
 'Tests.NumericArithmeticChecks.original_check_preserved',
 'Tests.NumericArithmeticChecks.noncanonical_unit_fallback',
 'Tests.NumericArithmeticChecks.mixed_input_computed_substitution',
 'Tests.NumericArithmeticChecks.coefficient_erasure',
 'Tests.NumericArithmeticChecks.changed_variable_rejected',
 'Tests.NumericArithmeticChecks.monomial_permutation',
 'Tests.NumericArithmeticChecks.missing_backward_rejected',
 'Tests.NumericArithmeticChecks.missing_forward_rejected',
 'Tests.NumericArithmeticChecks.changed_gate_rejected',
 'Tests.NumericArithmeticChecks.duplicate_address_key_rejected',
 'Tests.NumericArithmeticChecks.forgedSizes',
 'Tests.NumericArithmeticChecks.forged_sizes_skip_row_loops',
 'Tests.NumericArithmeticChecks.forged_sizes_rejected',
 'Tests.NumericArithmeticChecks.importedPolynomials',
 'Tests.NumericArithmeticChecks.importedCombinations',
 'Tests.NumericArithmeticChecks.importedKeys',
 'Tests.NumericArithmeticChecks.polynomials_bound',
 'Tests.NumericArithmeticChecks.combinations_bound',
 'Tests.NumericArithmeticChecks.keys_bound',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericKeys',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericKeys_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericCapture',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBindings',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericChecked',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericFullChecked',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.captureChecked',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericExtensionData',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericKeys',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericExtensionData_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericKeys_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericCapture',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBindings',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericChecked',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericFullChecked',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.captureChecked']

packed_arithmetic_roots += ['Tests.NumericArithmeticChecks.changed_normalized_source_rejected', 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource', 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource_binding', 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource', 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource_binding']

packed_arithmetic_roots += ['Airbender.Compiler.NumericArithmeticChecks.forwardEqual',
 'Airbender.Compiler.NumericArithmeticChecks.forwardEqual_eq',
 'Airbender.Compiler.NumericArithmeticChecks.normalized_getD',
 'Tests.NumericArithmeticChecks.forward_noncanonical_fallback',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericSource.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericNormalizedSource.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf14',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf15',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf16',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf17',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf18',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericLowered.leaf19',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericExtensionData.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf14',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf15',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf16',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf17',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf18',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateInputs.leaf19',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf14',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf15',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf16',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf17',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf18',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericGateOutputs.leaf19',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericBackward.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf14',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf15',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf16',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf17',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf18',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.numericForward.leaf19',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericSource.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericNormalizedSource.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericLowered.leaf14',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericExtensionData.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericExtensionData.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericExtensionData.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericExtensionData.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateInputs.leaf14',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericGateOutputs.leaf14',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericBackward.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.tree',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.tree_binding',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.tree_valid',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf0',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf1',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf2',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf3',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf4',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf5',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf6',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf7',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf8',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf9',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf10',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf11',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf12',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf13',
 'Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.numericForward.leaf14',
 'Tests.NumericArithmeticChecks.importedPolynomials.leaf0',
 'Tests.NumericArithmeticChecks.importedPolynomials.tree',
 'Tests.NumericArithmeticChecks.importedPolynomials.tree_binding',
 'Tests.NumericArithmeticChecks.importedPolynomials.tree_valid',
 'Tests.NumericArithmeticChecks.importedCombinations.leaf0',
 'Tests.NumericArithmeticChecks.importedCombinations.tree',
 'Tests.NumericArithmeticChecks.importedCombinations.tree_binding',
 'Tests.NumericArithmeticChecks.importedCombinations.tree_valid']

from gkr_numeric_arithmetic import (NUMERIC_CAPTURES, CASES as NUMERIC_CASES,
                                    FAMILIES as NUMERIC_FAMILIES, capture_roots as numeric_capture_roots)
for numeric_stem, numeric_family in zip(NUMERIC_CASES, NUMERIC_FAMILIES, strict=True):
    for numeric_mode in ["Cached", "Uncached"]:
        numeric_case = numeric_stem + numeric_mode
        if numeric_case not in NUMERIC_CAPTURES or numeric_stem == "BlakeRound":
            continue
        numeric_payload = json.loads((ROOT / "artifacts/compiler/numeric-arithmetic" /
                                      (numeric_family + "-" + numeric_mode.lower() + ".json")).read_text())
        packed_arithmetic_roots += numeric_capture_roots(numeric_case, numeric_payload)

packed_arithmetic_roots += ['Airbender.Compiler.NumericPolynomialChecks.FastNormalization.monomial_compare_eq',
 'Airbender.Compiler.NumericPolynomialChecks.FastNormalization.compareMonomial',
 'Airbender.Compiler.NumericPolynomialChecks.FastNormalization.compareMonomial_eq',
 'Airbender.Compiler.NumericPolynomialChecks.FastNormalization.insert',
 'Airbender.Compiler.NumericPolynomialChecks.FastNormalization.insert_eq',
 'Airbender.Compiler.NumericPolynomialChecks.FastNormalization.normalize',
 'Airbender.Compiler.NumericPolynomialChecks.FastNormalization.normalize_eq',
 'Airbender.Compiler.NumericPolynomialChecks.FastNormalization.map_eq',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.decode',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.compare_decode',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.key',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.small',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.decode_key',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.decodeRows',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.insert',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.decode_insert',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.keyedNormalize',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.keyedNormalize_eq',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.encodeRows',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.sortedSmall',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.sortedSmall_small',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.decode_key_sorted',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.decode_encode',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.decode_injective',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.decodeRows_injective',
 'Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization.normalizedKeys',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.coefficientBase',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.radix',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.Row',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.Packed',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.Packed.ext',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.termCode',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.decodeTerm',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.bounded',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.code_bound',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.decode_code',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.prepend',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack_cons',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack_length',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack_eta',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.head_pack',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.tail_pack',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack_injective',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.insert_bounded',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.normalizeRows',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.normalizeRows_encode',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.normalizeRows_bounded',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.boundsCheck',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.boundsCheck_sound',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.insertAt',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.insertAtCheck',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.hintedCheck',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.Ordered',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.insert_all',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.insert_ordered',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.normalizeRows_ordered',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.insert_append',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack_value',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.codes_bounded',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack_take',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack_drop',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack_get',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.pack_append',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.ordered_prefix',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.insertAt_append',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.insertAtCheck_sound',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.hintedCheck_sound',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow.check',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow.Binding',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow.check_sound',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.check',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.check_sound',
 'Tests.PackedNormalizationTrace.input',
 'Tests.PackedNormalizationTrace.expected',
 'Tests.PackedNormalizationTrace.encoded',
 'Tests.PackedNormalizationTrace.trace',
 'Tests.PackedNormalizationTrace.row',
 'Tests.PackedNormalizationTrace.accepted',
 'Tests.PackedNormalizationTrace.binding',
 'Tests.PackedNormalizationTrace.original_normalization',
 'Tests.PackedNormalizationTrace.coefficient_wrap',
 'Tests.PackedNormalizationTrace.wrongPosition',
 'Tests.PackedNormalizationTrace.wrongInput',
 'Tests.PackedNormalizationTrace.wrongExpected',
 'Tests.PackedNormalizationTrace.missingStep',
 'Tests.PackedNormalizationTrace.extraStep',
 'Tests.PackedNormalizationTrace.wrongLength',
 'Tests.PackedNormalizationTrace.wrong_position_rejected',
 'Tests.PackedNormalizationTrace.wrong_input_rejected',
 'Tests.PackedNormalizationTrace.wrong_expected_rejected',
 'Tests.PackedNormalizationTrace.missing_step_rejected',
 'Tests.PackedNormalizationTrace.extra_step_rejected',
 'Tests.PackedNormalizationTrace.wrong_length_rejected',
 'Tests.PackedNormalizationTrace.coefficient_bound_rejected',
 'Tests.PackedNormalizationTrace.key_bound_rejected',
 'Tests.PackedNormalizationTrace.zero_modulus_rejected',
 'Tests.PackedNormalizationTrace.large_modulus_rejected',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow.Binding.expectedEncoding',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow.Binding.inputEncoding',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow.Binding.expectedSorted',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow.Binding.inputSmall',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow.Binding.expectedBound',
 'Airbender.Compiler.NumericPolynomialChecks.PackedNormalization.PolynomialRow.Binding.inputBound']

packed_arithmetic_roots += ['Airbender.Compiler.NumericExpressionChecks.Code',
 'Airbender.Compiler.NumericExpressionChecks.Code.polynomial',
 'Airbender.Compiler.NumericExpressionChecks.encode',
 'Airbender.Compiler.NumericExpressionChecks.encode_polynomial',
 'Airbender.Compiler.NumericExpressionChecks.source_binding',
 'Airbender.Compiler.NumericArithmeticTrace.rowBindingCheck',
 'Airbender.Compiler.NumericArithmeticTrace.rowBindingCheck_sound',
 'Airbender.Compiler.NumericArithmeticTrace.bindingCheck',
 'Airbender.Compiler.NumericArithmeticTrace.bindingCheck_sound',
 'Airbender.Compiler.NumericArithmeticTrace.checked_pairs',
 'Airbender.Compiler.NumericArithmeticTrace.forwardExpected',
 'Airbender.Compiler.NumericArithmeticTrace.forwardExpected_eq',
 'Airbender.Compiler.NumericArithmeticTrace.pairs',
 'Airbender.Compiler.NumericArithmeticTrace.Capture',
 'Airbender.Compiler.NumericArithmeticTrace.check',
 'Airbender.Compiler.NumericArithmeticTrace.check_sound',
 'Tests.NumericExpressionChecks.original',
 'Tests.NumericExpressionChecks.expanded_terms',
 'Tests.NumericExpressionChecks.original_terms',
 'Tests.NumericExpressionChecks.zero_terms_retained',
 'Tests.NumericExpressionChecks.variable_order_retained',
 'Tests.NumericArithmeticTrace.bindings_checked',
 'Tests.NumericArithmeticTrace.imported_checked',
 'Tests.NumericArithmeticTrace.original_normalization_checked']

packed_arithmetic_roots += ['Airbender.Compiler.CleanPlacementChecks.addressCode_injective',
 'Airbender.Compiler.CleanPlacementChecks.Capture',
 'Airbender.Compiler.CleanPlacementChecks.check',
 'Airbender.Compiler.CleanPlacementChecks.reference_mem',
 'Airbender.Compiler.CleanPlacementChecks.member_sound',
 'Airbender.Compiler.CleanPlacementChecks.address_placement_of_mem',
 'Airbender.Compiler.CleanPlacementChecks.check_sound',
 'Airbender.Compiler.CleanPlacementChecks.placement_at',
 'Airbender.Compiler.CleanPlacementChecks.placement_from_lookup',
 'Airbender.Compiler.CleanPlacementChecks.all_lookup',
 'Tests.CleanPlacementChecks.entries',
 'Tests.CleanPlacementChecks.placements',
 'Tests.CleanPlacementChecks.capture',
 'Tests.CleanPlacementChecks.bank_binding',
 'Tests.CleanPlacementChecks.placement_binding',
 'Tests.CleanPlacementChecks.checked',
 'Tests.CleanPlacementChecks.original_roundtrips',
 'Tests.CleanPlacementChecks.wrongIndex',
 'Tests.CleanPlacementChecks.wrongCode',
 'Tests.CleanPlacementChecks.outside',
 'Tests.CleanPlacementChecks.forgedSize',
 'Tests.CleanPlacementChecks.wrong_index_rejected',
 'Tests.CleanPlacementChecks.wrong_code_rejected',
 'Tests.CleanPlacementChecks.default_value_cannot_hide_outside_index',
 'Tests.CleanPlacementChecks.forged_size_rejected']

from gkr_clean_placement import capture_roots as clean_placement_roots
for clean_case in NUMERIC_CASES:
    for clean_mode in ["Cached", "Uncached"]:
        clean_name = clean_case + clean_mode
        clean_foundation = ROOT / ("Airbender/Proofs/GKRProtocol/FullArithmeticNative/" + clean_name + "Foundation.lean")
        clean_selectors = json.loads(json.loads(re.search(r'\bselectors\s+("(?:[^"\\]|\\.)*")', clean_foundation.read_text())[1]))
        packed_arithmetic_roots += clean_placement_roots(clean_name, len(clean_selectors["addresses"]))
        packed_arithmetic_roots.append("Airbender.Compiler.CleanArithmeticNative." + clean_name + ".native.placementsSourceBinding")

for word_source in [
    "Airbender/Proofs/Tables/PackedSignedRun.lean",
    "Airbender/Proofs/Tables/PackedWordBlocks.lean",
    "Airbender/Proofs/Tables/PackedWordBounds.lean",
    "Airbender/Proofs/Tables/PackedXor9Checks.lean",
    "Airbender/Proofs/Blake2G/Xor9PackedCapture.lean",
    "Airbender/Proofs/Blake2G/Xor9PackedCertificate.lean",
    "Tests/PackedSignedRun.lean",
    "Airbender/Proofs/Tables/PackedByteTableChecks.lean",
    "Airbender/Proofs/Keccak/ChiPackedCapture.lean",
    "Airbender/Proofs/Keccak/ChiPackedCertificate.lean",
    "Tests/PackedByteTables.lean",
    'Airbender/Proofs/Tables/PackedWordColumn.lean',
    'Airbender/Proofs/Tables/PackedDisjointSum.lean',
    'Airbender/Proofs/Tables/ShiftPackedReference.lean',
    'Airbender/Proofs/Tables/ShiftPackedBasisData.lean',
    'Airbender/Proofs/Tables/ShiftPackedBasis.lean',
    'Airbender/Proofs/Tables/ShiftPackedRows.lean',
    'Airbender/Proofs/Tables/ShiftPackedExpectedRows.lean',
    'Airbender/Proofs/Tables/ShiftPackedRowData.lean',
    'Airbender/Proofs/Tables/ShiftPackedRowBinding.lean',
    'Airbender/Proofs/Tables/ShiftPackedRowBinding0.lean',
    'Airbender/Proofs/Tables/ShiftPackedRowBinding1.lean',
    'Airbender/Proofs/Tables/ShiftPackedRowBinding2.lean',
    'Airbender/Proofs/Tables/ShiftPackedRowBinding3.lean',
    'Airbender/Proofs/Tables/ShiftOrPackedCapture.lean',
    'Airbender/Proofs/Tables/ShiftOrPackedCertificate.lean',
    'Airbender/Proofs/Tables/ShiftXorPackedCapture.lean',
    'Airbender/Proofs/Tables/ShiftXorPackedCertificate.lean',
    'Airbender/Proofs/Blake2G/Xor8PackedCapture.lean',
    'Airbender/Proofs/Blake2G/Xor8PackedCertificate.lean',
    'Tests/PackedWordColumn.lean',
    'Tests/ShiftPackedReference.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column0Data.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column0.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column0Requests.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column0Reference.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column1Data.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column1.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column1Requests.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column1Reference.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column2Data.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column2.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column2Requests.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column2Reference.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column3Data.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column3.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column3Requests.lean',
    'Airbender/Proofs/Tables/ShiftPackedEncoding/Column3Reference.lean',
]:
    word_text = (ROOT / word_source).read_text()
    word_namespace = re.search(r"^namespace (\S+)", word_text, re.M)[1]
    word_names = re.findall(r"^(?:def|theorem|structure|inductive|numeric_data_binding) (\S+)", word_text, re.M)
    packed_arithmetic_roots += [word_namespace + "." + name for name in word_names]

packed_arithmetic_roots += ["Airbender.Keccak.Proofs.ChiPackedCapture.column"]
for chi_part in range(32):
    packed_arithmetic_roots += ["Airbender.Keccak.Proofs.ChiPackedCapture.column" + stem + str(chi_part)
                                for stem in ["Blocks", "Start", "Size"]]

packed_arithmetic_roots.append("Airbender.Blake2G.Proofs.Xor8PackedCapture.column")
for blake_byte_part in range(32):
    packed_arithmetic_roots += ["Airbender.Blake2G.Proofs.Xor8PackedCapture.column" + stem + str(blake_byte_part)
                                for stem in ["Blocks", "Start", "Size"]]

for bitwise_name in ["Or", "Xor"]:
    bitwise_prefix = "Airbender.Verification.ShiftCertificate." + bitwise_name + "PackedCapture.column"
    packed_arithmetic_roots.append(bitwise_prefix)
    for bitwise_part in range(32):
        packed_arithmetic_roots += [bitwise_prefix + stem + str(bitwise_part)
                                    for stem in ["Blocks", "Start", "Size"]]

for shift_lane in range(4):
    shift_prefix = f"Airbender.Verification.ShiftPackedEncoding.Lane{shift_lane}.sourceColumn"
    packed_arithmetic_roots.append(shift_prefix)
    for shift_part in range(256):
        packed_arithmetic_roots += [shift_prefix + stem + str(shift_part)
                                    for stem in ["Blocks", "Start", "Size"]]

from gkr_clean_ideal import CAPTURES as CLEAN_IDEAL_CAPTURES, TRACE_CASES as CLEAN_TRACE_CASES, ROW_CASES as CLEAN_ROW_CASES, load as clean_ideal_payload
for clean_source in ["Airbender/Proofs/GKRProtocol/CleanIdealChecks.lean",
        "Airbender/Proofs/GKRProtocol/CleanIdealTrace.lean",
        "Airbender/Proofs/GKRProtocol/CleanIdealRows.lean",
        "Tests/CleanIdealChecks.lean", "Tests/CleanIdealTrace.lean", "Tests/CleanIdealRows.lean"] + [
        f"Airbender/Proofs/GKRProtocol/CleanIdealNative/{case}{suffix}.lean"
        for case in CLEAN_IDEAL_CAPTURES
        for suffix in (["Data", "Bindings", "TraceBindings", ""] if case in CLEAN_TRACE_CASES else ["Data", "Bindings", ""] if case in CLEAN_ROW_CASES else ["Data", ""])]:
    clean_text = (ROOT / clean_source).read_text()
    clean_namespace = re.search(r"^namespace (\S+)", clean_text, re.M)[1]
    clean_names = re.findall(r"^(?:def|theorem|structure|inductive|numeric_data_binding) (\S+)", clean_text, re.M)
    packed_arithmetic_roots += [clean_namespace + "." + name for name in clean_names]
for clean_case, clean_name in CLEAN_IDEAL_CAPTURES.items():
    clean_payload = clean_ideal_payload(clean_case, clean_name)
    clean_count = len(clean_payload["expressions"])
    if clean_case in CLEAN_TRACE_CASES:
        trace_prefix = f"Airbender.Compiler.CleanIdealNative.{clean_case}.traceRows"
        packed_arithmetic_roots += [trace_prefix]
        packed_arithmetic_roots += [trace_prefix + ".leaf" + str(index)
            for index in range((len(clean_payload["normalizationTraces"]) + 7) // 8)]
    clean_prefix = f"Airbender.Compiler.CleanArithmeticNative.{clean_case}.native."
    packed_arithmetic_roots += [clean_prefix + name for name in [
        "idealRelationsBinding", "idealCountBinding", "idealScopeLimitBinding"]]
    packed_arithmetic_roots += [clean_prefix + name + str(index)
        for name in ["idealCodeBinding", "idealWitnessBinding", "idealInputsBinding"]
        for index in range(clean_count)]

from gkr_packed_wiring import CAPTURES as WIRING_CAPTURES, load as wiring_payload, legacy_roots as wiring_legacy_roots
for wiring_source in [
        "Airbender/Proofs/GKRCompiler/WiringKeySort.lean",
        "Airbender/Proofs/GKRCompiler/WiringChecks.lean",
        "Airbender/Proofs/GKRCompiler/WiringCheckProjections.lean",
        "Tests/WiringChecks.lean"] + [
        f"Airbender/Proofs/GKRCompiler/WiringCheckNative/{case}{suffix}.lean"
        for case in WIRING_CAPTURES for suffix in ["Data", "Bindings", ""]]:
    wiring_text = (ROOT / wiring_source).read_text()
    wiring_namespace = re.search(r"^namespace (\S+)", wiring_text, re.M)[1]
    wiring_names = re.findall(r"^(?:def|theorem|structure|inductive|numeric_data_binding) (\S+)", wiring_text, re.M)
    packed_arithmetic_roots += [wiring_namespace + "." + name for name in wiring_names]
for wiring_case, wiring_name in WIRING_CAPTURES.items():
    packed_arithmetic_roots += wiring_legacy_roots(wiring_case, wiring_name, wiring_payload(wiring_name))

for rotation_source in [
        "Airbender/Proofs/Tables/FiniteGridChecks.lean", "Tests/FiniteGridChecks.lean",
        "Airbender/Proofs/UnifiedReduced/Tables/RotateReferenceBytes.lean",
        "Airbender/Proofs/UnifiedReduced/Tables/ImportedRotate8.lean",
        "Airbender/Proofs/UnifiedReduced/Tables/ImportedRotate16.lean"]:
    rotation_text = (ROOT / rotation_source).read_text()
    rotation_namespace = re.search(r"^namespace (\S+)", rotation_text, re.M)[1]
    rotation_names = re.findall(r"^(?:def|theorem|numeric_data_binding) (\S+)", rotation_text, re.M)
    packed_arithmetic_roots += [rotation_namespace + "." + name for name in rotation_names]

from gkr_packed_shift_prefix import ADOPTED as PACKED_SHIFT_COLUMNS, capture as shift_capture
from gkr_shift_prefix_instances import plans as shift_capture_plan
shift_artifact = json.loads((ROOT / 'artifacts/setup/shift-binop.json').read_text())
for shift_source in ["Airbender/Proofs/GKRProtocol/PackedSetupNormalization.lean",
                     "Tests/PackedSetupNormalization.lean"]:
    shift_text = (ROOT / shift_source).read_text()
    shift_namespace = re.search(r"^namespace (\S+)", shift_text, re.M)[1]
    packed_arithmetic_roots += [shift_namespace + "." + name for name in
        re.findall(r"^(?:def|theorem|structure) (\S+)", shift_text, re.M)]
for column in PACKED_SHIFT_COLUMNS:
    for module, shift_text in shift_capture(shift_artifact, column):
        shift_namespace = re.search(r"^namespace (\S+)", shift_text, re.M)[1]
        packed_arithmetic_roots += [shift_namespace + "." + name for name in
            re.findall(r"^(?:def|theorem|numeric_data_binding) (\S+)", shift_text, re.M)]
    _, chunks = shift_capture_plan(shift_artifact, column)
    for index, (first, last, _, _, selected) in enumerate(chunks):
        code_spans = [(f'source{index}', last-first)] + [
            (f'target{index}Region{kind}', stop-start) for kind, start, stop in selected]
        for name, count in code_spans:
            packed_arithmetic_roots.append(f'Airbender.Compiler.ShiftPrefixChecks.Column{column}.' + name)
            if count > 128:
                packed_arithmetic_roots += [f'Airbender.Compiler.ShiftPrefixChecks.Column{column}.{name}Data{part}'
                    for part in range((count + 127) // 128)]

path = Path('Airbender/Checks/Axioms.lean')
content = (ROOT / path).read_text()
from gkr_packed_special_spans import COLUMNS as FIXED_SPECIAL_COLUMNS, modules as fixed_special_modules, capture_plan as fixed_special_plan
for column in FIXED_SPECIAL_COLUMNS:
    for module, fixed_text in fixed_special_modules(column):
        if module.endswith(('.Data', '.Projected')):
            continue
        fixed_namespace = re.search(r'^namespace (\S+)', fixed_text, re.M)[1]
        packed_arithmetic_roots += [fixed_namespace + '.' + name for name in
            re.findall(r'^(?:def|theorem|numeric_data_binding) (\S+)', fixed_text, re.M)]
    _, fixed_groups, _, selected, _ = fixed_special_plan(column)
    for index in selected:
        fixed_owner = f'Airbender.Compiler.UnifiedFixedSpans.Column{column}.'
        packed_arithmetic_roots.append(fixed_owner + f'source{index}')
        packed_arithmetic_roots += [fixed_owner + f'target{index}_{part}'
            for part in range(len(fixed_groups[index]))]
    fixed_import = f'import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column{column}.Projected'
    if fixed_import not in content.splitlines():
        content = fixed_import + '\n' + content
from generate_shift_extent_checks import generated as shift_extent_modules
for extent_source in ['Airbender/Proofs/Tables/PackedLengthChecks.lean', 'Tests/PackedLengthChecks.lean']:
    extent_text = (ROOT / extent_source).read_text()
    extent_namespace = re.search(r'^namespace (\S+)', extent_text, re.M)[1]
    packed_arithmetic_roots += [extent_namespace + '.' + name for name in
        re.findall(r'^(?:def|theorem|structure) (\S+)', extent_text, re.M)]
for lane in range(4):
    for module, extent_text in shift_extent_modules(shift_artifact, lane):
        extent_namespace = re.search(r'^namespace (\S+)', extent_text, re.M)[1]
        packed_arithmetic_roots += [extent_namespace + '.' + name for name in
            re.findall(r'^(?:def|theorem) (\S+)', extent_text, re.M)]
for extent_import in ['import Tests.PackedLengthChecks'] + [
        f'import Airbender.Proofs.Tables.ShiftExtentChecks{lane}' for lane in range(4)]:
    if extent_import not in content.splitlines():
        content = extent_import + '\n' + content
from gkr_packed_rotate_boundary import modules as rotate_boundary_modules
for span_source in ['Airbender/Proofs/GKRProtocol/PackedSetupAccess.lean',
                    'Airbender/Proofs/GKRProtocol/PackedSetupSpans.lean', 'Tests/PackedSetupSpans.lean']:
    span_text = (ROOT / span_source).read_text()
    span_namespace = re.search(r'^namespace (\S+)', span_text, re.M)[1]
    packed_arithmetic_roots += [span_namespace + '.' + name for name in
        re.findall(r'^(?:def|theorem|structure) (\S+)', span_text, re.M)]
for module, span_text in rotate_boundary_modules():
    span_namespace = re.search(r'^namespace (\S+)', span_text, re.M)[1]
    packed_arithmetic_roots += [span_namespace + '.' + name for name in
        re.findall(r'^(?:def|theorem|numeric_data_binding) (\S+)', span_text, re.M)]
packed_arithmetic_roots += ['Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.' + name
    for name in ['sourceCode'] + [f'target{index}' for index in range(12)]]
for span_import in ['import Tests.PackedSetupSpans',
                    'import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.RotateBoundary.Certificate']:
    if span_import not in content.splitlines():
        content = span_import + '\n' + content
for shift_import in ['import Tests.PackedSetupNormalization'] + [
        f'import Airbender.Proofs.GKRProtocol.ShiftPrefixChecks.Column{column}.Projected'
        for column in PACKED_SHIFT_COLUMNS]:
    if shift_import not in content.splitlines():
        content = shift_import + '\n' + content
rotation_import = 'import Tests.FiniteGridChecks'
if rotation_import not in content.splitlines():
    content = rotation_import + '\n' + content
for wiring_import in ['import Tests.WiringChecks'] + [
        'import Airbender.Proofs.GKRCompiler.WiringNative.' + case for case in WIRING_CAPTURES]:
    if wiring_import not in content.splitlines():
        content = wiring_import + '\n' + content
for clean_import in ['import Tests.CleanIdealChecks', 'import Tests.CleanIdealTrace', 'import Tests.CleanIdealRows'] + [
        'import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.' + case for case in CLEAN_IDEAL_CAPTURES]:
    if clean_import not in content.splitlines():
        content = clean_import + '\n' + content
for numeric_case in sorted(NUMERIC_CAPTURES):
    numeric_capture_import = "import Airbender.Proofs.GKRProtocol.FullArithmeticNative." + numeric_case
    if numeric_capture_import not in content.splitlines():
        content = numeric_capture_import + "\n" + content
for dense_import in ['import Tests.NumericExpressionChecks', 'import Tests.NumericArithmeticTrace']:
    if dense_import not in content.splitlines():
        content = dense_import + '\n' + content
content = re.sub(r'^import Airbender\.Proofs\.Blake2G\.(?:Xor9CertificatePart[0-9]+|Xor9Extents)\n', '', content, flags=re.M)
content = re.sub(r'^import Airbender\.Proofs\.Tables\.ShiftOutputCertificate[0-3]Part[0-9]+\n', '', content, flags=re.M)
for shift_import in ['import Tests.PackedWordColumn', 'import Tests.ShiftPackedReference'] + [
        f'import Airbender.Proofs.Tables.ShiftPackedEncoding.Column{lane}' for lane in range(4)]:
    if shift_import not in content.splitlines():
        content = shift_import + '\n' + content
byte_import = 'import Tests.PackedByteTables'
if byte_import not in content.splitlines():
    content = byte_import + '\n' + content
word_import = 'import Tests.PackedSignedRun'
if word_import not in content.splitlines():
    content = word_import + '\n' + content
clean_import = 'import Tests.CleanPlacementChecks'
if clean_import not in content.splitlines():
    content = clean_import + '\n' + content
trace_import = 'import Tests.PackedNormalizationTrace'
if trace_import not in content.splitlines():
    content = trace_import + '\n' + content
numeric_import = 'import Tests.NumericArithmeticChecks'
if numeric_import not in content.splitlines():
    content = numeric_import + '\n' + content
arithmetic_import = 'import Tests.PackedArithmeticChecks'
if arithmetic_import not in content.splitlines():
    content = arithmetic_import + '\n' + content
program_import = 'import Airbender.Proofs.GKRProtocol.ProgramLogicalRows'
if program_import not in content.splitlines():
    content = program_import + '\n' + content
setup_import = 'import Airbender.Proofs.GKRProtocol.ProgramSetupNative'
if setup_import not in content.splitlines():
    content = setup_import + '\n' + content
public_row_import = 'import Airbender.Proofs.GKRProtocol.ProgramPublicRows'
if public_row_import not in content.splitlines():
    content = public_row_import + '\n' + content
public_constraints_import = 'import Airbender.Proofs.GKRProtocol.ProgramPublicConstraints'
if public_constraints_import not in content.splitlines():
    content = public_constraints_import + '\n' + content
unified_constraints_import = 'import Airbender.Proofs.GKRProtocol.ProgramUnifiedConstraints'
if unified_constraints_import not in content.splitlines():
    content = unified_constraints_import + '\n' + content
setup_packed_import = 'import Airbender.Proofs.GKRProtocol.UnifiedPackedEqualityCertificate'
if setup_packed_import not in content.splitlines():
    content = setup_packed_import + '\n' + content
setup_packed_test_import = 'import Tests.PackedSetupEquality'
if setup_packed_test_import not in content.splitlines():
    content = setup_packed_test_import + '\n' + content
for setup_tree_import in [
        'import Airbender.Proofs.GKRProtocol.UnifiedPackedEquality.Column5.Certificate',
        'import Tests.PackedSetupTree',
        'import Tests.PackedSetupTreeLayout']:
    if setup_tree_import not in content.splitlines():
        content = setup_tree_import + '\n' + content
for column in (4, 6, 7):
    fixed_import = f'import Airbender.Proofs.GKRProtocol.UnifiedPackedEquality.Column{column}.Certificate'
    if fixed_import not in content.splitlines():
        content = fixed_import + '\n' + content
packed_import = 'import Airbender.Proofs.Tables.ShiftAndPackedCertificate'
if packed_import not in content.splitlines():
    content = packed_import + '\n' + content
packed_test_import = 'import Tests.PackedTableCertificates'
if packed_test_import not in content.splitlines():
    content = packed_test_import + '\n' + content
acceptance_import = 'import Airbender.Proofs.GKRProtocol.NativeMachineAcceptance'
if acceptance_import not in content.splitlines():
    content = acceptance_import + '\n' + content
decoder_imports = '\n'.join('import Airbender.Proofs.GKRProtocol.' + tree + '.' + name
                          for tree in ['ProgramDecoderNative', 'ProgramDecoderLookup', 'ProgramFixedLookup', 'ProgramPCLowNative'] for name in NAMES)
for decoder_import in decoder_imports.splitlines():
    if decoder_import not in content.splitlines():
        content = decoder_import + '\n' + content
for name in NAMES:
    constraint_import = 'import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.' + name
    if constraint_import not in content.splitlines():
        content = constraint_import + '\n' + content
roots = []
existing_roots = set(content.splitlines())
for name in program_roots + setup_roots + decoder_roots + fixed_roots + constraint_roots + pc_roots + shift_roots + subword_roots + public_row_roots + word_roots + unified_roots + acceptance_roots + decode_roots + packed_table_roots + packed_setup_roots + packed_arithmetic_roots:
    root = f'#print axioms {name}'
    if root not in existing_roots:
        roots.append(root)
        existing_roots.add(root)
if '#print axioms Airbender.Compiler.GroupedLookupArguments' not in existing_roots:
    roots.append('#print axioms Airbender.Compiler.GroupedLookupArguments')
for name in NAMES:
    namespace = 'UnifiedRowNative' if name.startswith('Unified') else 'PooledRowNative'
    for theorem in ['LookupArgumentsWith', 'lookup_arguments_with_retained',
                    'nativeRequests_source', 'nativeOperands_coverage', 'nativeSetupColumns_binding',
                    'source_member_with']:
        root = f'#print axioms Airbender.Compiler.{namespace}.{name}.{theorem}'
        if root not in existing_roots:
            roots.append(root)
            existing_roots.add(root)
if roots:
    content += '\n' + '\n'.join(roots) + '\n'
emit(path, content)

if args.check and CHANGED:
    parser.exit(1, 'Generated native lookup bindings are stale:\n' + '\n'.join(CHANGED) + '\n')
print(f'Native lookup operand bindings: {len(NAMES)} profiles; {len(CHANGED)} changed files.')
