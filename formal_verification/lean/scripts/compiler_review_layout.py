"""Keep generated compiler bindings separate from supporting row proofs."""
import re


def split_row(name, text):
    case = name.rsplit('.', 1)[1]
    owner = 'Airbender.Compiler.' + name.split('.')[-2] + '.' + case
    start = text.index('/-- The same canonical source frame')
    stop = text.index('/-- A complete native graph witness', start)
    fields = text[start:stop].split('  sourceValue : ', 1)[1]
    source_type = fields.splitlines()[0].removesuffix(' → Source.BaseField')
    count_type = fields.split('  counts : ', 1)[1].splitlines()[0].removesuffix(' → Source.BaseField')
    frame = fields.split('  frame : ', 1)[1].split('  arithmetic : ', 1)[0].strip()
    address = re.search(r'physical \((.*?) wire\)', frame)[1]
    assigned = frame.split(' =', 1)[1].strip().removesuffix(' wire')
    arithmetic = fields.split('  arithmetic : ', 1)[1].split('  helpers : ', 1)[0].strip()
    helpers = fields.split('  helpers : ', 1)[1].split('  authored : ', 1)[0].strip()
    authored = fields.split('  authored : ', 1)[1].split('  active : ', 1)[0].strip().removesuffix(' sourceValue')
    active = fields.split('  active : ', 1)[1].strip()
    row_start = text.index('def row (cert : Certificate)')
    row_stop = text.index('\ntheorem ', row_start)
    row = text[row_start:row_stop]
    dependencies = ['Airbender.Review.Compiler.NativeRow', 'Airbender.Review.Compiler.RowFrame'] + [
        f'Airbender.Proofs.GKRProtocol.{part}.{case}' for part in
        ['CleanArithmeticNative', 'CounterFrameNative', 'HelperValidityNative', 'MaterializedWitnessNative']]
    dependencies.append('Airbender.Review.Helpers.Context.Registries.Pooled' if 'PooledRowNative' in name
                        else 'Airbender.Review.Helpers.UnifiedReduced.Registry')
    binding = ''.join('import ' + module + '\n' for module in dependencies)
    binding += f'\nnamespace {owner}\nopen Airbender Airbender.Compiler\n\n'
    execute = active.split(').get', 1)[1].strip()
    binding += f'''abbrev Certificate :=
  RowFrame (S := {source_type}) (C := {count_type})
    {address}
    (fun sourceValue counts => {assigned})
    (fun physical => {arithmetic})
    (fun physical => {helpers})
    {authored}
    (fun physical => {active})

/-- Physical native arithmetic and the execution mask. Logical lookup matching
derives all helper ranges and retained Clean obligations without a canonical
borrow or source-assignment frame. -/
abbrev Input :=
  PhysicalRowInput
    (fun physical => {arithmetic})
    (fun physical => (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.{case}.native.bank.address
      (Airbender.Compiler.CleanArithmeticNative.{case}.native.placement index)) physical)
    {execute})

{row}
end {owner}
'''
    text = text[:row_start] + text[row_stop:]
    text = text[:start] + text[stop:]
    binding_name = 'Airbender.Import.Compiler.Rows.' + case
    return {binding_name: binding, name: 'import ' + binding_name + '\n' + text}


def pooled_execution_proof(text):
    start = text.index('/-- Each physical row')
    stop = text.index('theorem row_active', start)
    boundary_start = text.index('/-- Public starting state')
    boundary_stop = text.index('theorem boot_inputs', boundary_start)
    text = text[:boundary_start] + text[boundary_stop:]
    text = text[:start] + text[stop:]
    return 'import Airbender.Review.Compiler.Pooled\n' + text
