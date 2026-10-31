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
import Airbender.Review.Compiler.LogicalRows

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

for name in NAMES:
    prepared(name)
program_roots = program_row_interfaces()

path = Path('Airbender/Checks/Axioms.lean')
content = (ROOT / path).read_text()
program_import = 'import Airbender.Proofs.GKRProtocol.ProgramLogicalRows'
if program_import not in content.splitlines():
    content = program_import + '\n' + content
roots = []
for name in program_roots:
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
