#!/usr/bin/env python3
"""Emit independent kernel checks for native worker selector batches and groups."""
from pathlib import Path
import sys,json
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from generate_worker_selectors import selectors,FAMILIES,WORKERS
r=ROOT
variants={'Bigint':'bigint','BlakeG':'blakeG','BlakeRound':'blakeRound','KeccakColumnParity':'columnParity','KeccakThetaRho':'thetaRho','KeccakChi5':'chi5'}
for title,family in WORKERS.items():
 variant=variants[title];entries=selectors(json.load(open(ROOT.parent.parent / f'cs/compiled_circuits/{FAMILIES[family]}_layout_gkr.json')));n=len(entries)
 d=r/f'proven/Proven/Compiler/WorkerSelectors/{title}';d.mkdir(exist_ok=True)
 parts=[]
 for first in range(0,n,16):
  name=f'Part{first//16:03d}';parts.append(name)
  s=f'''module
public import Proven.Compiler.WorkerSelectors.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.{title}
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch{first//16:03d} : List NativeLookups.Selector :=
  ((selectorsFor .{variant}).drop {first}).take {min(16,n-first)}

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved{first//16:03d} : batch{first//16:03d}.all (fun selector =>
    match NativeLookups.select (circuitFor .{variant}) selector with
    | .ok _ => true | .error _ => false) = true := by kernel_rfl

/-- Every selector in this batch has its actual native output group. -/
theorem grouped{first//16:03d} :
    NativeLookups.groupsAgree (circuitFor .{variant}) batch{first//16:03d} = true := by kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.{title}
''';(d/(name+'.lean')).write_text(s)
 s='module\n'+''.join(f'public import Proven.Compiler.WorkerSelectors.{title}.{part}\n' for part in parts)+f'''
@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.{title}
set_option maxRecDepth 32768

/-- The contiguous batches cover every native query selector. -/
theorem batches : selectorsFor .{variant} = '''+' ++ '.join(f'batch{i:03d}' for i in range(len(parts)))+''' := by kernel_rfl

'''
 resolved=f'resolved{len(parts)-1:03d}';grouped=f'grouped{len(parts)-1:03d}'
 for i in reversed(range(len(parts)-1)):
  resolved=f'(append_all _ resolved{i:03d} {resolved})';grouped=f'(append_groups _ grouped{i:03d} {grouped})'
 s+=f'''/-- Every worker query has its actual gate, expansion and native chain group. -/
theorem binding :
    NativeLookups.queryLocators (circuitFor .{variant}) =
      .ok ((selectorsFor .{variant}).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor .{variant}).all (fun selector =>
      match NativeLookups.select (circuitFor .{variant}) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor .{variant}) (selectorsFor .{variant}) = true := by
  refine ⟨by kernel_rfl, ?_, ?_⟩
  · rw [batches]
    exact {resolved}
  · rw [batches]
    exact {grouped}

end Airbender.Compiler.NativeWorkerLookups.Proofs.{title}
'''
 (d.parent/(title+'.lean')).write_text(s)
 print(title,len(parts),'independent selector batches')

# Resolve each batch independently. Check the complete native chain groups once per worker.
for title, variant in variants.items():
    directory = r / f'proven/Proven/Compiler/WorkerSelectors/{title}'
    for path in directory.glob('Part*.lean'):
        text = path.read_text()
        position = text.index('/-- Every selector in this batch')
        text = text[:position] + f'end Airbender.Compiler.NativeWorkerLookups.Proofs.{title}\n'
        text = text.replace('public import Proven.Compiler.WorkerSelectors.Common',
                            'public import Proven.Compiler.WorkerSelectors.Common\npublic import Proven.KernelExact')
        import re
        batch = re.search(r'def (batch\d+)', text)[1]
        text = text.replace('= true := by kernel_rfl',
            f'= true := by\n  kernel_exact (resolved_all_eq (circuitFor .{variant}) {batch}).symm.trans\n'
            f'    (show NativeLookups.resolvedAll (circuitFor .{variant}) {batch} = true from by kernel_rfl)')
        path.write_text(text)
    (directory / 'Grouped.lean').write_text(f"""module
public import Proven.Compiler.WorkerSelectors.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.{title}
set_option maxRecDepth 32768

/-- Each worker selector belongs to its actual public native output chain. -/
theorem grouped :
    NativeLookups.groupsAgree (circuitFor .{variant}) (selectorsFor .{variant}) = true := by kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.{title}
""")
    path = directory.parent / (title + '.lean')
    text = path.read_text().replace('module\n',
        f'module\npublic import Proven.Compiler.WorkerSelectors.{title}.Grouped\n', 1)
    position = text.index('  · rw [batches]', text.index('    exact (append_all'))
    end = text.index('\nend ', position)
    path.write_text(text[:position] + '  · exact grouped\n' + text[end:])

# List append is left associative. Keep the proof composition in that order.
for title in variants:
    directory = r / f'proven/Proven/Compiler/WorkerSelectors/{title}'
    path = directory.parent / (title + '.lean')
    text = path.read_text()
    proof = 'resolved000'
    for index in range(1, len(list(directory.glob('Part*.lean')))):
        proof = f'(append_all _ {proof} resolved{index:03d})'
    begin = text.index('    exact (append_all')
    end = text.index('\n', begin)
    text = text[:begin] + '    kernel_exact ' + proof + text[end:]
    path.write_text(text.replace('  · exact grouped', '  · kernel_exact grouped'))

# The generic batch proof does not infer concrete prefixes from earlier proofs.
for title, variant in variants.items():
    directory = r / f'proven/Proven/Compiler/WorkerSelectors/{title}'
    count = len(list(directory.glob('Part*.lean')))
    chunks = '[' + ', '.join(f'batch{index:03d}' for index in range(count)) + ']'
    witnesses = 'by\n      refine ⟨' + ', '.join(['?_'] * count + ['True.intro']) + '⟩\n'\
        + '\n'.join(f'      · kernel_exact resolved{index:03d}' for index in range(count))
    imports = '\n'.join(f'public import Proven.Compiler.WorkerSelectors.{title}.Part{index:03d}'
                        for index in range(count))
    text = f'''module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.{title}.Grouped
{imports}

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.{title}
set_option maxRecDepth 32768

/-- The contiguous batches cover every native query selector. -/
theorem batches : selectorsFor .{variant} = ({chunks}).flatten := by kernel_rfl

/-- Every worker query has its actual gate, expansion and native chain group. -/
theorem binding :
    NativeLookups.queryLocators (circuitFor .{variant}) =
      .ok ((selectorsFor .{variant}).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor .{variant}).all (fun selector =>
      match NativeLookups.select (circuitFor .{variant}) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor .{variant}) (selectorsFor .{variant}) = true := by
  refine ⟨by kernel_rfl, ?_, ?_⟩
  · let predicate := fun selector =>
      match NativeLookups.select (circuitFor .{variant}) selector with
      | .ok _ => true | .error _ => false
    have accepted : AllBatches predicate {chunks} :=
      {witnesses}
    kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all predicate) batches).trans
      (flatten_all predicate {chunks} accepted)
  · kernel_exact grouped

end Airbender.Compiler.NativeWorkerLookups.Proofs.{title}
'''
    (directory.parent / (title + '.lean')).write_text(text)
