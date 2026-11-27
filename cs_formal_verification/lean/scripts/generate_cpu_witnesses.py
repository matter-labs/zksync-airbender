#!/usr/bin/env python3
"""Generate checked affine operands and canonical native CPU certificate constructors."""
from pathlib import Path
import json
from generate_worker_selectors import selectors, address_key
from generate_worker_constraints import operand, source_expression, fields_theorem, cons_proof
from check_compiler_captures import FAMILIES, cached_layout

ROOT = Path(__file__).resolve().parents[1]
FAMILIES_CPU = {
    'AddSub': ('add-sub', '.pooled .addSub', '.addSub'),
    'JumpBranch': ('jump-branch', '.pooled .jumpBranchSlt', '.jumpBranchSlt'),
    'MulDiv': ('mul-div', '.pooled .mulDiv', '.mulDiv'),
    'ShiftBinop': ('shift-binop', '.pooled .shiftBinop', '.shiftBinop'),
    'WordMemory': ('word-memory', '.pooled .wordMemory', '.wordMemory'),
    'SubwordMemory': ('subword-memory', '.pooled .subwordMemory', '.subwordMemory'),
    'Unified': ('unified', '.unified', '.machine'),
}

def header(name, imports):
    return 'module\n' + ''.join('public import '+item+'\n' for item in imports) + f'''
@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.{name}
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768
'''

def generate(name):
    from generate_worker_constraints import address
    key,family,row_family=FAMILIES_CPU[name]
    circuit=json.loads(cached_layout(FAMILIES[key]).read_text())
    native=selectors(circuit)
    reverse={address_key(a):int(i) for i,a in circuit['placement_data'].items()}
    positions={int(i):position for position,i in enumerate(sorted(circuit['placement_data'],key=int))}
    logical=lambda a: reverse[address_key(a)]
    source=[{'columns':row['encoding']['columns']} for row in native]
    for i,row in enumerate(native):row['source']=i
    execute=logical({'BaseLayerMemory':circuit['memory_layout']['machine_state']['execute']})
    directory=ROOT/'proven/Proven/Compiler/CPUWitnesses'/name
    directory.mkdir(parents=True,exist_ok=True)
    ending=f'\nend Airbender.Compiler.CPUWitnesses.{name}\n'
    files={}
    namespace=f'Proven.Compiler.CPUWitnesses.{name}'
    data_parts=[];field_parts=[]
    for start in range(0,len(native),8):
        part=f'Queries{start//8:03d}';data_parts.append(namespace+'.'+part)
        text=header(name,['Proven.Compiler.CPUWitnesses.Common','Proven.KernelRfl'])
        for i in range(start,min(start+8,len(native))):
            row=native[i];value=operand(row)
            if row['weight']=='mask':
                from generate_worker_constraints import address
                value=value.replace('⟨.one,',f'⟨.column {address(row["mask"])},',1)
            expressions=[f'Import.expression {source_expression(c,logical)}' for c in row['encoding']['columns']]
            text+=f'\n/-- The actual resolved native primitive operand. -/\nnoncomputable def operand{i} : NativeLookups.Operand := {value}\n'
            text+=f'\n/-- Its affine fields use the captured logical columns. -/\nnoncomputable def sourceFields{i} (logical : Nat → F) : List F := ['+', '.join(f'({e}).eval (Verification.environment logical)'for e in expressions)+']\n'
        files[directory/(part+'.lean')]=text+ending
    for start in range(0,len(native),8):
        part=f'Fields{start//8:03d}';field_parts.append(namespace+'.'+part)
        text=header(name,[namespace+f'.Queries{start//8:03d}'])
        for i in range(start,min(start+8,len(native))):
            proof = fields_theorem(name,i,circuit,native,source,logical,positions)
            linear = any('linear' in col for col in native[i]['encoding']['columns'])
            if not linear:
                proof = proof[:proof.index('  simp only')]
                proof += f'  change [physical {address(native[i]["encoding"]["columns"][0]["cell"])}] = [logical {logical(native[i]["encoding"]["columns"][0]["cell"])}]\n'
                proof += f'  exact congrArg (fun value => [value]) p{logical(native[i]["encoding"]["columns"][0]["cell"])}\n'
            else:
                proof = proof.replace('  norm_num [', '  all_goals norm_num [')
            text+='\n'+proof+'\n'
            text+=f'\n/-- Every retained primitive query is enabled on an active CPU row. -/\ntheorem enabled{i} (physical : GKRAddress → F) (logical : Nat → F)\n    ({'agreement' if native[i]['weight'] == 'mask' else '_agreement'} : PlacementAgreement Captures.{name}.imported.circuit physical logical)\n    ({'active' if native[i]['weight'] == 'mask' else '_active'} : logical {execute} = 1) : operand{i}.weight.value physical ≠ 0 := by\n'
            if native[i]['weight']=='mask':
                from generate_worker_constraints import address
                addr=native[i]['mask'];idx=logical(addr)
                text+=f'  have placed : physical {address(addr)} = logical {idx} :=\n    WorkerConstraints.placed agreement (position := {positions[idx]}) (by kernel_rfl)\n  change physical {address(addr)} ≠ 0\n  rw [placed, active]\n  exact one_ne_zero\n'
            else:
                text+='  change (1 : F) ≠ 0\n  exact one_ne_zero\n'
        files[directory/(part+'.lean')]=text+ending
    text=header(name,data_parts)
    groups=[[i for i,r in enumerate(native)if r['group']==g]for g in range(3)]
    text+='\n/-- The resolved operands retain the exact native selector order. -/\nnoncomputable def operands (group : Fin 3) : List NativeLookups.Operand :=\n  (['+', '.join('['+', '.join('operand'+str(i)for i in ids)+']'for ids in groups)+'] : List (List NativeLookups.Operand)).get group\n'
    text+='\n/-- The complete logical tuples retain each native occurrence. -/\nnoncomputable def tuples (logical : Nat → F) (group : Fin 3) : List (List F) :=\n  (['+', '.join('['+', '.join('sourceFields'+str(i)+' logical'for i in ids)+']'for ids in groups)+'] : List (List (List F))).get group\n'
    text+=f'''\n/-- The canonical check compares each logical tuple with its actual public native row. -/
noncomputable def canonicalCheck (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (logical : Nat → F) : Bool := CPUWitnesses.canonicalCheck ({family}) initial program (tuples logical)
'''
    files[directory/'Data.lean']=text+ending
    text=header(name,[namespace+'.Data']+field_parts+['Proven.Compiler.NativeExtension.'+name])
    text+=f'''\n/-- Every selector resolves to its retained primitive operand. -/
theorem resolved (group : Fin 3) :
    ((NativeLookups.selectorsFor ({family})).filter (fun selector => selector.group == group)).mapM
      (NativeLookups.select (NativeLookups.circuitFor ({family}))) = .ok (operands group) := by
  fin_cases group <;> kernel_rfl

/-- Active rows retain all primitive query occurrences. -/
theorem enabled (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.{name}.imported.circuit physical logical)
    (active : logical {execute} = 1) :
    ∀ group, ∀ value ∈ operands group, value.weight.value physical ≠ 0 := by
  intro group
  fin_cases group
'''
    for ids in groups:text+='  · exact '+cons_proof([f'enabled{i} physical logical agreement active'for i in ids])+'\n'
    text+=f'''\n/-- Placement gives the same complete logical tuple at every resolved operand. -/
theorem fields (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.{name}.imported.circuit physical logical) (group : Fin 3) :
    (operands group).map (fun operand => operand.input.fields physical) = tuples logical group := by
  fin_cases group
'''
    for ids in groups:
        proof='rfl'
        for i in reversed(ids):proof=f'(congrArg₂ List.cons (fields{i} physical logical agreement) {proof})'
        text+='  · exact '+proof+'\n'
    text+=f'''\n/-- Exact selector resolution and canonical tuple checks give the full native lookup argument. -/
noncomputable def arguments (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.{name}.imported.circuit physical logical)
    (active : logical {execute} = 1) (checked : canonicalCheck initial program logical = true) :
    NativeLookups.Arguments (NativeLookups.circuitFor ({family})) (NativeLookups.selectorsFor ({family}))
      physical (NativePublicSetup.rows initial program ({family})) :=
  CPUWitnesses.arguments_of_checked (tuples logical) (fun group =>
    (CPUWitnesses.requests_of_enabled physical group (operands group) (resolved group)
      (enabled physical logical agreement active group)).trans
      (congrArg Except.ok (fields physical logical agreement group))) checked
'''
    cert='UnifiedLogicalRowCertificate' if name=='Unified'else'ProgramLogicalRowCertificate'
    kind='Trace.UnifiedFamily' if name == 'Unified' else 'Trace.PooledFamily'
    text+=f'''\n/-- The checked constructor describes this logical row exactly. -/
noncomputable def of_checked (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (logical : Nat → F)
    (sourceHolds : Satisfies FullArithmeticNative.{name}Cached.native.artifact.source
      (NativeExtension.{name}.inputValues logical))
    (checked : canonicalCheck initial program logical = true) (active : logical {execute} = 1) :
    {cert} (NativePublicSetup.rows initial program) := by
  have extension := NativeExtension.{name}.extension_preserves logical sourceHolds
  let physical := Classical.choose extension
  have facts := Classical.choose_spec extension
  exact {{
    row := ⟨{row_family}, logical⟩
    physical := physical
    arithmetic := facts.1
    placement := facts.2
    lookups := arguments initial program physical logical facts.2 active checked
    active := active }}

/-- The constructor retains the complete supplied logical row. -/
theorem row_of_checked (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (logical : Nat → F)
    (sourceHolds : Satisfies FullArithmeticNative.{name}Cached.native.artifact.source
      (NativeExtension.{name}.inputValues logical))
    (checked : canonicalCheck initial program logical = true) (active : logical {execute} = 1) :
    (of_checked initial program logical sourceHolds checked active).row =
      (⟨{row_family}, logical⟩ : Trace.Row babyBearModulus {kind}) := rfl
'''
    files[directory.with_suffix('.lean')]=text+ending
    return files


FIXTURES = {
    'AddSub': ('Airbender.AddSub.Witness', 'entry', 'fun family => .pooled family'),
    'JumpBranch': ('Airbender.JumpBranchSlt.Comparison.NonVacuous', 'entry', 'fun family => .pooled family'),
    'MulDiv': ('Airbender.NonVacuous.MulDivTrace', 'program', 'fun _ => .pooled .mulDiv'),
    'ShiftBinop': ('Airbender.NonVacuous.ShiftBinopTrace', 'program', 'fun _ => .pooled .shiftBinop'),
    'WordMemory': ('Airbender.WordMemory.NonVacuous', 'entry', 'fun family => .pooled family'),
    'SubwordMemory': ('Airbender.NonVacuous.SubwordMemoryTrace', 'program', 'fun _ => .pooled .subwordMemory'),
    'Unified': ('Airbender.NonVacuous.UnifiedBoot', 'program', 'fun _ => .unified'),
}


def fixture(name):
    space, program, family_function = FIXTURES[name]
    entries = f'[{space}.entry]' if program == 'entry' else f'{space}.program'
    certificate = 'UnifiedLogicalRowCertificate' if name == 'Unified' else 'ProgramLogicalRowCertificate'
    kind = 'Trace.UnifiedFamily' if name == 'Unified' else 'Trace.PooledFamily'
    row_family = FAMILIES_CPU[name][2]
    return f"""module
public import Proven.Compiler.CPUWitnesses.{name}
public import Proven.Compiler.NativeSatisfiable.{name}

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.{name}.Fixture
open NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 32768

/-- The public program retains each instruction address, bits and decoder fields. -/
def program : List Trace.RVMachineProgramEntry :=
  ({entries}).map fun entry =>
    ⟨entry.pc, entry.bits, Trace.RVMachineDecoderData.ofOrdinary ({family_function}) entry.data⟩

/-- Every retained native tuple equals the selected canonical public setup row. -/
theorem lookup_check : canonicalCheck {space}.initial program {space}.assignment = true := by
  kernel_rfl

/-- The active honest row supplies a complete cached native CPU certificate. -/
noncomputable def rowCertificate : {certificate} (NativePublicSetup.rows {space}.initial program) :=
  of_checked {space}.initial program {space}.assignment
    NativeSatisfiable.{name}.source_satisfied lookup_check (by kernel_rfl)

/-- The native certificate retains the supplied CPU family and complete logical assignment. -/
theorem rowCertificate_row : rowCertificate.row =
    (⟨{row_family}, {space}.assignment⟩ : Trace.Row babyBearModulus {kind}) := rfl

end Airbender.Compiler.CPUWitnesses.{name}.Fixture
"""

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('families',nargs='*',choices=list(FAMILIES_CPU));args=p.parse_args()
    for name in args.families or FAMILIES_CPU:
        for path,text in generate(name).items():path.write_text(text)
        (ROOT / f'proven/Proven/Compiler/CPUWitnesses/{name}/Fixture.lean').write_text(fixture(name))
