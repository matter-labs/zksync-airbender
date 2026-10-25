#!/usr/bin/env python3
"""Compose the two unified compiler frames, actual decoder and public setup."""
import argparse
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_pooled_row_instances import module as pooled_module


def module(case):
    # Reuse the certificate/frame syntax; all names still denote the actual
    # unified capture and its checked canonical witness.
    _,text=pooled_module(case,'addSub')
    text=text.replace('PooledRowNative.'+case,'UnifiedRowNative.'+case)
    text=text.replace('Airbender.AddSub.','Airbender.UnifiedReduced.')
    text=text.replace('Trace.PooledFamily','Trace.UnifiedFamily').replace('⟨.addSub,','⟨.machine,')
    text=text.replace('import Airbender.Review.Helpers.Decoder.PooledProgram',
                      'import GKRProtocol.UnifiedProgramProfile\nimport GKRProtocol.UnifiedPublicConstraints')
    for unused in ['PublicConstraints','ROMNative.WordFullPublic','ROMNative.SubwordPublic']:
        text=text.replace('import GKRProtocol.'+unused+'\n','')
    text='import GKRProtocol.WindowedNative.'+case+'Public\n'+text
    windowed=f'''/-- The actual independently chosen initialization windows preserve the same
source frame used by execution. Their native products remain in the witness. -/
def ofWindowedWitness (publicTops : Nat → Nat) {{R : Type}} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.{case}.native.inputs.length → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.{case}.native.multiplicityColumns.length → Source.BaseField)
    (index : Fin Airbender.Compiler.MaterializedNative.{case}.native.model.imported.data.length)
    (fallback physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (native : Airbender.Compiler.WindowedNative.{case}.CompleteActualRowWitness publicTops hom challenges gamma sourceValue counts index fallback physical values)
    (authored : Airbender.Compiler.MaterializedWitnessNative.{case}.AuthoredLookupValid sourceValue)
    (active : (Airbender.Compiler.CleanArithmeticNative.{case}.native.environment physical (fun _ _ => #[])).get
      Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1) : Certificate := by
  rcases native.1 with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩
  exact ⟨sourceValue, counts, physical, inputsAt, arithmetic, helpers, authored, active⟩

'''
    text=text.replace('def row (cert : Certificate)',windowed+'def row (cert : Certificate)')
    # Unified uses its own ten-column public table and native setup.
    a=text.index('theorem constraints');b=text.index('theorem decoded',a)
    prefix=text[a:b];body=prefix[prefix.index('  have native :='):]
    native=f'Airbender.Compiler.CleanClosedNative.{case}.nativeSetup'
    replacement=f'''theorem native_constraints (cert : Certificate) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row cert).assignment)
      ((row cert).constraints {native}) := by
'''+body
    text=text[:a]+replacement+text[b:]
    text=text.replace('Trace.NativeDecoder.pooledProgram','Trace.NativeDecoder.unifiedProgram')
    marker='\nend Airbender.Compiler.UnifiedRowNative.'+case
    public=f'''
theorem constraints (cert : Certificate) {{before : Reference.RiscV.Sail.State}}
    (image : Trace.ROM.ImportedImage before)
    (typed : (row cert).decoderQuery[0].val < 65536) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row cert).assignment)
      ((row cert).constraints (UnifiedReduced.Setup.table before)) := by
  have member := decoded cert typed
  have operation := UnifiedProgramProfile.query_operation (row cert).assignment member
  exact UnifiedPublicConstraints.transport _ _ _ (native_constraints cert) (active cert) operation
    (fun _ present guard => ROMNative.UnifiedFullPublic.public_table_refinement image present guard)
'''
    text=text.replace(marker,'\n'+public+marker)
    return 'GKRProtocol.UnifiedRowNative.'+case,text


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for mode in ['Uncached','Cached']:
        name,text=module('Unified'+mode);path=LEAN/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified compiler row changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        print(name,flush=True)
        if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,
            env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)

if __name__=='__main__':main()
