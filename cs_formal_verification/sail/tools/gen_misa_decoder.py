"""Generate the MisaOnly lemmas the decoder walk (slop/Slop/Sail/MisaWalk.lean) finds by name.

  python3 sail/tools/gen_misa_decoder.py lean/sail-rv32/SailRV32 > lean/slop/Slop/Sail/MisaDecoder.lean

Three families, reached from `encdec_backwards` in the generated model (sail/regen.sh), emitted in one dependency
order so that every proof can use the lemmas of the definitions it calls:
  * `misa_ce_<Ext>`   : `currentlyEnabled Ext_<Ext>` (the extension checks; a clause reads `misa` or is a constant),
  * `misa_fn_<f>`     : the SailM-valued helper functions `SailRV32.Functions.<f>`,
  * `misa_<s>`        : the decoder helpers `encdec_<s>_backwards`.
Each proof unfolds one definition, reduces configuration constants, and applies the MisaOnly rules and the
earlier lemmas; `repeat' first` is the only search. The kernel checks every proof.
"""
import re, pathlib, sys

model = pathlib.Path(sys.argv[1])
bodies, sigs, qual = {}, {}, {}
for f in sorted(model.glob('*.lean')):
    cur = None
    depth_functions = []   # the nesting of `namespace` blocks: `Functions` ones are where Sail's functions live
    stack = []
    for line in f.read_text().split('\n'):
        ns = re.match(r'namespace (\S+)', line)
        if ns:
            stack.append(ns.group(1))
        elif re.match(r'end(\s|$)', line) and stack:
            stack.pop()
        m = re.match(r'(?:noncomputable )?(?:private )?def (\S+?)(?=[ \(\{:]|$)', line)
        if m:
            cur = m.group(1); bodies[cur] = ''; sigs[cur] = line
            qual[cur] = 'SailRV32.Functions.' if 'Functions' in stack else 'SailRV32.'
        elif re.match(r'(?:noncomputable )?(?:private )?(def|theorem|abbrev|instance|end|namespace|section|lemma|structure|inductive|open|set_option|@\[)', line):
            cur = None
        if cur:
            bodies[cur] += line + '\n'

# the extension checks: the clauses of `currentlyEnabled`
cur_body = bodies['currentlyEnabled']
clauses = {}
for block in re.split(r'\n(?=  \| \.Ext_)', cur_body):
    k = re.match(r'  \| \.(Ext_\w+)', block)
    if k:
        clauses[k.group(1)] = block

def binders(sig):
    head = sig.split(' : SailM', 1)[0]
    found = re.findall(r'\((\w+) : ([^()]*(?:\([^()]*\)[^()]*)*)\)', head)
    return [(x if x != '_' else f'unit_{i}', t) for i, (x, t) in enumerate(found)]

# units: (kind, key, lemma name, statement, body text)
units = {}
def add_unit(key, kind, lemma, stmt, body, arity=0):
    units[key] = dict(kind=kind, lemma=lemma, stmt=stmt, body=body, arity=arity)
for x, body in clauses.items():
    add_unit('ext:' + x, 'ext', f'misa_ce_{x[4:]}',
             f'MisaOnly (SailRV32.Functions.currentlyEnabled SailRV32.extension.{x})', body)

# hand-written in MisaWalk.lean (leaves of the walk): the register, opcode and rounding-mode decoders
HANDWRITTEN_SHORT = {'reg', 'bop', 'iop', 'mul_op', 'uop', 'csrop', 'rounding_mode'}
HANDWRITTEN = {'helper:encdec_' + h + '_backwards' for h in HANDWRITTEN_SHORT}

# the decoder closure (names), without the extension checks themselves
skip_fn = {'currentlyEnabled', 'get_sew', 'get_sew_pow', 'virtual_memory_supported', 'internal_error', 'sailThrow',
           'reserved_behavior'}
reach, todo = set(), ['encdec_backwards']
while todo:
    n = todo.pop()
    if n in reach or n not in bodies:
        continue
    reach.add(n)
    todo.extend(i for i in set(re.findall(r'\b([A-Za-z_][A-Za-z0-9_]*)\b', bodies[n])) if i in bodies)
for n in sorted(reach):
    if n == 'encdec_backwards' or ' : SailM' not in sigs[n] or n in skip_fn or n == 'currentlyEnabled':
        continue
    if n in {'encdec_' + h + '_backwards' for h in HANDWRITTEN_SHORT}:
        continue
    if n.startswith('encdec_') and n.endswith('_backwards'):
        short = n[len('encdec_'):-len('_backwards')]
        kind, lemma = 'helper', f'misa_{short}'
    elif n.startswith('encdec_'):
        continue  # forwards / matches: not in the walk
    else:
        kind, lemma = 'fn', f'misa_fn_{n}'
    bs = binders(sigs[n])
    args = ' '.join(f'({x} : {t})' for x, t in bs)
    call = ' '.join(x for x, _ in bs)
    stmt = f'{args} : MisaOnly (SailRV32.Functions.{n} {call})' if args else f'MisaOnly (SailRV32.Functions.{n})'
    add_unit(('helper:' if kind == 'helper' else 'fn:') + n, kind, lemma, stmt, bodies[n], arity=len(bs))
# the hand-written lemmas (Slop/Sail/MisaWalk.lean) and the config-only ones are not generated here

def unit_deps(key):
    body = units[key]['body']
    deps = set()
    for ident in re.findall(r'\b(Ext_\w+|[A-Za-z_][A-Za-z0-9_]*)\b', body):
        if ident.startswith('Ext_') and ('ext:' + ident) in units and ('ext:' + ident) != key:
            deps.add('ext:' + ident)
        elif key != 'ext:' + ident and ('fn:' + ident) in units:
            deps.add('fn:' + ident)
        elif ('helper:' + ident) in units:
            deps.add('helper:' + ident)
    for ident in re.findall(r'\bencdec_(\w+?)_backwards\b', body):
        if ('helper:encdec_' + ident + '_backwards') in units and key != 'helper:encdec_' + ident + '_backwards':
            deps.add('helper:encdec_' + ident + '_backwards')
    deps.discard(key)
    # the opcode-clause and rounding-mode helpers are hand-written in MisaWalk.lean
    deps = {d for d in deps if d not in HANDWRITTEN}
    return deps

# configuration constants the bodies match on (enumeration values): reduced first, so no split refutes them
constdefs = {n for n in bodies if not binders(sigs[n]) and ' : SailM' not in sigs[n]
             and re.search(r' : [^=]+:=', sigs[n]) and '()' not in sigs[n]}
constname = {n: qual[n] + n for n in constdefs}

order, seen = [], set()
def visit(k, stack=()):
    if k in seen or k in stack:
        return
    for d in sorted(unit_deps(k)):
        visit(d, stack + (k,))
    seen.add(k); order.append(k)
for k in sorted(units):
    visit(k)

done_units = []
out = ['import Slop.Sail.MisaWalk', '', 'namespace Airbender.Reference.Sail',
       'open Reference.RiscV.Sail _root_.Sail.ArchSem SailRV32', '',
       '/-! GENERATED by sail/tools/gen_misa_decoder.py (do not edit): the `MisaOnly` lemmas of the decoder walk for',
       'the extension checks (`misa_ce_*`), the decoder helper functions (`misa_fn_*`) and the `encdec_*` helpers',
       '(`misa_*`), in dependency order. The kernel checks every proof. -/', '']
for k in order:
    u = units[k]
    out.append('set_option maxHeartbeats 1000000 in')
    out.append('set_option maxRecDepth 16384 in')
    stmt = (' ' + u['stmt']) if u['stmt'].startswith('(') else ' : ' + u['stmt']
    out.append(f"theorem {u['lemma']}{stmt} := by")
    if u['kind'] == 'ext':
        out.append(f'  unfold SailRV32.Functions.currentlyEnabled')
        out.append('  try dsimp only')
    else:
        name = k.split(':', 1)[1]
        out.append(f'  unfold SailRV32.Functions.{name}')
        consts = sorted(i for i in set(re.findall(r'\b([A-Za-z_][A-Za-z0-9_]*)\b', u['body']))
                        if i in constdefs)
        if consts:
            out.append('  try dsimp only [' + ', '.join(constname[c] for c in consts) + ']')
    out.append("  repeat' first")
    for d in sorted(unit_deps(k), key=lambda d: order.index(d)):
        if order.index(d) < order.index(k):
            out.append(f"    | (with_reducible exact {units[d]['lemma']}{' _' * units[d]['arity']})")
    out.append('    | (apply read_outside; decide)')
    if u['kind'] == 'ext':
        out.append('    | (apply misa_enabled; simp only [List.mem_cons, List.mem_nil_iff, reduceCtorEq, or_false, or_true, true_or, false_or]; done)')
    out.append('    | apply misa_pure')
    out.append('    | apply misa_assert')
    out.append('    | apply misa_throw')
    out.append('    | (apply misa_bind <;> try intro)')
    out.append('    | apply misa_ite')
    out.append('    | split')
    out.append('    | (exfalso; first | omega | bv_omega)')
    out.append('')
out.append('end Airbender.Reference.Sail')
print('\n'.join(out))
print(len(order), 'lemmas', file=sys.stderr)
