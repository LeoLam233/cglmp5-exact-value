#!/usr/bin/env python3
"""Check source-map reference coverage by the direct type/axiom inventory.

This is a static coverage/consistency check, not proof or Lean name resolution.
The final inspection's #check and #print axioms resolve every recorded name.
"""
import sys
sys.dont_write_bytecode = True
import argparse, hashlib, json, pathlib, re
ROOT = pathlib.Path(__file__).resolve().parents[2]
DOCUMENTS = ['SOURCE_MAP.md', 'docs/LEAN_ATTAINMENT_SOURCE_MAP.md', 'docs/LEAN_SOS_SOURCE_MAP.md']
SYMBOL = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
SPECIAL = {'phase_step_0..18'}
FIXED_NONDECLARATIONS = {
    'namespace': {'CGLMP5', 'CGLMP5.Attainment'},
    'library_or_metavariable': {'Commute','R','Ring','StarRing','Fin.cases'},
    'tactic': {'linear_combination','native_decide'},
    'module_family': {'CertificateChunkXXCYY','SOSPhasePairNN','SOSIntegerResidualNNN'},
    'suffix_family': {'_text_decode'},
}

def document_symbols(root):
    found = {}
    for doc in DOCUMENTS:
        for number, line in enumerate((root/doc).read_text().splitlines(), 1):
            for token in re.findall(r'`([^`\n]+)`', line):
                if SYMBOL.fullmatch(token) or token in SPECIAL:
                    found.setdefault(token, []).append(f'{doc}:{number}')
    return found

def check(root=ROOT, manifest=None, inventory=None):
    manifest = manifest if manifest is not None else json.loads((root/'verification/lean/mapped_declarations.json').read_text())
    inventory = inventory if inventory is not None else json.loads((root/'verification/lean/declaration_inventory.json').read_text())
    errors = []
    symbols = document_symbols(root)
    refs = manifest.get('references', [])
    if not isinstance(refs,list) or not all(isinstance(r,dict) for r in refs):
        return {'status':'INCONSISTENT','errors':['Malformed mapped reference list'],'scientific_pass_inferred':False}
    refs_by_symbol = {r.get('symbol'):r for r in refs}
    if len(refs_by_symbol) != len(refs): errors.append('Duplicate mapped symbol')
    if manifest.get('documents') != DOCUMENTS: errors.append('Changed source-map document scope')
    errors += ['Unclassified mapped symbol: '+s for s in sorted(set(symbols)-set(refs_by_symbol))]
    errors += ['Stale mapped symbol: '+s for s in sorted(set(refs_by_symbol)-set(symbols))]
    entries = inventory.get('declarations', [])
    if not isinstance(entries,list) or not all(isinstance(d,dict) for d in entries):
        return {'status':'INCONSISTENT','errors':['Malformed inventory declaration list'],'scientific_pass_inferred':False}
    by_name = {d.get('name'):d for d in entries}
    if len(by_name) != len(entries): errors.append('Duplicate inventory declaration')
    targets = {}
    for ref in refs:
        symbol = ref.get('symbol', '?')
        if ref.get('category') in ('declaration', 'theorem_family'):
            resolved = ref.get('targets')
            if not isinstance(resolved,list) or not all(isinstance(t,dict) for t in resolved):
                errors.append('Malformed declaration target list: '+symbol); continue
            if not resolved: errors.append('Empty declaration target: '+symbol)
            if len({t.get('name') for t in resolved}) != len(resolved):
                errors.append('Duplicate resolved declaration target: '+symbol)
            if ref.get('category') == 'declaration' and len(resolved) != 1:
                errors.append('Ordinary reference must name exactly one declaration; qualify its namespace: '+symbol)
            if ref.get('category') == 'theorem_family':
                if symbol == 'phase_linear_e_k':
                    expected = {f'CGLMP5.SOSFinite.phase_linear_{e}_{k}' for e in range(20) for k in range(24)}
                elif symbol == 'phase_step_0..18':
                    expected = {f'CGLMP5.SOSFinite.phase_step_{e}' for e in range(19)}
                else:
                    expected = set(); errors.append('Unknown theorem family: '+symbol)
                if {t.get('name') for t in ref.get('targets', [])} != expected:
                    errors.append('Incomplete or changed theorem family: '+symbol)
            for target in ref.get('targets', []):
                name, module = target.get('name'), target.get('module')
                if not all(isinstance(v,str) and re.fullmatch(r'CGLMP5(?:\.[A-Za-z_][A-Za-z_0-9]*)+',v) for v in (name,module)):
                    errors.append('Invalid mapped declaration target: '+repr(target)); continue
                if ref.get('category') == 'declaration' and not (name == symbol or name.endswith('.'+symbol)):
                    errors.append('Symbol does not resolve to recorded declaration: '+symbol+' / '+name)
                if name in targets and targets[name] != target: errors.append('Inconsistent repeated target: '+name)
                targets[name] = target
                entry = by_name.get(name)
                if not entry or entry.get('status') != 'ready' or entry.get('module') != module:
                    errors.append('Mapped declaration missing from ready exact inspection: '+name)
                source = root/'lean'/pathlib.Path(*module.split('.')).with_suffix('.lean')
                if not source.is_file(): errors.append('Missing mapped source: '+module)
                elif hashlib.sha256(source.read_bytes()).hexdigest() != target.get('source_sha256'):
                    errors.append('Mapped source changed; re-resolve reference: '+module)
                if target.get('kind') not in ('theorem','lemma','def','abbrev','structure','inductive'):
                    errors.append('Unclassified declaration kind: '+name)
        elif ref.get('category') in ('module','module_family','library_or_metavariable','tactic','namespace','suffix_family','document'):
            if not ref.get('reason'): errors.append('Missing nondeclaration classification reason: '+symbol)
            if ref.get('targets'): errors.append('Nondeclaration classification has targets: '+symbol)
            category = ref.get('category')
            if category in FIXED_NONDECLARATIONS and symbol not in FIXED_NONDECLARATIONS[category]:
                errors.append('Unreviewed nondeclaration exemption: '+symbol)
            elif category == 'module':
                filename = symbol if symbol.endswith('.lean') else symbol+'.lean'
                if not (root/'lean/CGLMP5'/filename).is_file(): errors.append('Missing referenced module: '+symbol)
            elif category == 'document':
                if not (root/symbol).is_file(): errors.append('Missing referenced document: '+symbol)
        else: errors.append('Unknown mapped-reference category: '+symbol)
    if not targets: errors.append('Empty mapped declaration coverage')
    return {'status':'CONSISTENT' if not errors else 'INCONSISTENT','errors':errors,
            'documents':DOCUMENTS,'symbol_count':len(symbols),'mapped_declaration_count':len(targets),
            'inventory_count':len(entries),'scope':'Static source-map and inventory coverage only. Final Lean type/axiom capture and kernel replay remain mandatory.',
            'scientific_pass_inferred':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=pathlib.Path);a=p.parse_args()
    result=check()
    if a.output:
        out=a.output.resolve()
        if out.is_relative_to(ROOT): raise SystemExit('Coverage output must be external to the candidate tree')
        out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2));return 0 if result['status']=='CONSISTENT' else 1
if __name__=='__main__':raise SystemExit(main())
