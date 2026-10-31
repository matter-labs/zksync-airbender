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
    pp = Path(f'Airbender/Proofs/GKRProtocol/LogicalRows/{name}.lean')
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
import Airbender.Proofs.GKRProtocol.LogicalRows

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
import Airbender.Proofs.GKRProtocol.LogicalRows.{name}
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
        old = (ROOT / 'Airbender/Proofs/GKRProtocol/LogicalRows' / (name + '.lean')).read_text()
        helpers = old[old.index('theorem helpers_from_arguments'):old.index('theorem input_active')]
        helpers = helpers.replace('(input : Input) (arguments : LookupArguments input)', parameters)
        helpers = helpers.replace('physical_member input arguments 2',
                                  'fixed_group_member decoder wordAt input arguments 2 (by decide +kernel)')
        code = f'''import Airbender.Proofs.GKRProtocol.LogicalRows.{name}
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

path = Path('Airbender/Checks/Axioms.lean')
content = (ROOT / path).read_text()
program_import = 'import Airbender.Proofs.GKRProtocol.ProgramLogicalRows'
if program_import not in content.splitlines():
    content = program_import + '\n' + content
setup_import = 'import Airbender.Proofs.GKRProtocol.ProgramSetupNative'
if setup_import not in content.splitlines():
    content = setup_import + '\n' + content
decoder_imports = '\n'.join('import Airbender.Proofs.GKRProtocol.' + tree + '.' + name
                          for tree in ['ProgramDecoderNative', 'ProgramDecoderLookup', 'ProgramFixedLookup', 'ProgramPCLowNative'] for name in NAMES)
for decoder_import in decoder_imports.splitlines():
    if decoder_import not in content.splitlines():
        content = decoder_import + '\n' + content
for name in [name for name in NAMES if name.startswith(('AddSub', 'JumpBranch', 'MulDiv', 'ShiftBinop', 'SubwordMemory'))]:
    constraint_import = 'import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.' + name
    if constraint_import not in content.splitlines():
        content = constraint_import + '\n' + content
roots = []
for name in program_roots + setup_roots + decoder_roots + fixed_roots + constraint_roots + pc_roots + shift_roots + subword_roots:
    root = f'#print axioms {name}'
    if root not in content.splitlines():
        roots.append(root)
if '#print axioms Airbender.Compiler.GroupedLookupArguments' not in content.splitlines():
    roots.append('#print axioms Airbender.Compiler.GroupedLookupArguments')
for name in NAMES:
    namespace = 'UnifiedRowNative' if name.startswith('Unified') else 'PooledRowNative'
    for theorem in ['LookupArgumentsWith', 'lookup_arguments_with_retained',
                    'nativeRequests_source', 'nativeOperands_coverage', 'nativeSetupColumns_binding',
                    'source_member_with']:
        root = f'#print axioms Airbender.Compiler.{namespace}.{name}.{theorem}'
        if root not in content.splitlines():
            roots.append(root)
if roots:
    content += '\n' + '\n'.join(roots) + '\n'
emit(path, content)

if args.check and CHANGED:
    parser.exit(1, 'Generated native lookup bindings are stale:\n' + '\n'.join(CHANGED) + '\n')
print(f'Native lookup operand bindings: {len(NAMES)} profiles; {len(CHANGED)} changed files.')
