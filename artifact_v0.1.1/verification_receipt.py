"""Versioned execution receipts: identify bytes and exact enforced target.

A receipt is a reproducibility record, not a signature, proof of unseen history,
or a semantic verification of the prose documents whose hashes it records.
"""
from __future__ import annotations
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import sys
from strict_schema import require_normal_python, POLYNOMIAL_DESCENDING

VERSION='cglmp5-verifier-v0.1.1'
THEOREM_ID='CGLMP5.STANDARD.LOCAL-BOUND-2.ARBITRARY-DIMENSION.LOCAL-5-POVM.EXACT-MAXIMUM.v1'
TARGET={
    'theorem_id':THEOREM_ID,
    'mu_polynomial_coefficients':POLYNOMIAL_DESCENDING,
    'polynomial_coefficient_order':'descending powers t^6 through t^0',
    'root_selector':'unique real root mu>3; p(3)<0; p strictly increasing on [3,infinity)',
    'scalar_basis':'n[a+2*b+6*c+12*e]*s^a*(5*mu)^b*u^c*i^e / d; a,c,e in {0,1}; b in {0,1,2}',
    'actual_embedding':{'s':'positive sqrt(5)','u':'positive sqrt(10+2*s)','i':'positive imaginary unit','zeta':'(u+i*(s-1))/4=exp(i*pi/10)'},
    'operator_relations':'U_r^5=I; U_r*=U_r^-1; only cross-party (even/odd) commutation',
    'standard_events':{
        'outcomes':'0,1,2,3,4; all equalities modulo 5','k':[0,1],'weight':'1-k/2',
        'positive':['A0=B0+k','B0=A1+k+1','A1=B1+k','B1=A0+k'],
        'negative':['A0=B0-k-1','B0=A1-k','A1=B1-k-1','B1=A0-k-1'],
        'local_bound':2,
    },
    'scope':'arbitrary local Hilbert dimensions and local five-outcome POVMs; explicit C^5 tensor C^5 attainer',
    'analytic_bridge':'POVM_BRIDGE.md; same fixed local J for both settings; this analytic proof is not machine-formalized',
}


def _sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def receipt(checker, root, inputs, checked_claims):
    require_normal_python()
    source=Path(__file__).resolve().parent
    sources={p.name:_sha(p) for p in sorted(source.glob('*.py'))}
    docs={}
    for name in ('PROOF.md','ROOT_EMBEDDING.md','POVM_BRIDGE.md','SCHEMA.md','README.md'):
        path=Path(root)/name
        if path.is_file():docs[name]=_sha(path)
    encoded=json.dumps(TARGET,sort_keys=True,separators=(',',':')).encode()
    return {
        'schema':'cglmp5.verification-receipt.v1','checker_version':VERSION,'checker_entrypoint':checker,
        'enforced_target':TARGET,'enforced_target_sha256':hashlib.sha256(encoded).hexdigest(),
        'checked_claims':checked_claims,
        'inputs':inputs,'source_sha256':sources,
        'document_sha256':docs,
        'document_hash_scope':'bytes bound for comparison only; no machine verification of arbitrary prose or historical claims',
        'annotation_policy':'Only required mathematical inputs and fixed declarations are enforced. Cached statuses, display spectra, stored universes/enclosures, discovery metadata and unknown annotations are not mathematical premises; see SCHEMA.md.',
        'execution':{'utc':datetime.now(timezone.utc).isoformat(),'python':sys.version,'implementation':platform.python_implementation(),'platform':platform.platform(),'dependencies':'Python standard library only','optimize':sys.flags.optimize,'PYTHONOPTIMIZE':os.environ.get('PYTHONOPTIMIZE'),'argv':list(sys.argv),'cwd':str(Path.cwd()),'input_root':str(Path(root).resolve())},
        'limits':'This receipt does not establish external validation, human peer review, formal verification, independent model ancestry, or a trustworthy execution history by itself.',
    }


def write_result(result, output=None):
    text=json.dumps(result,indent=2,allow_nan=False)+'\n'
    if output is not None:
        output=Path(output)
        # Replace only once a complete semantic result exists. A failed run
        # must never be mistaken for an earlier PASS left at this destination.
        output.write_text(text,encoding='utf-8')
    print(text,end='',flush=True)


def run_cli(fn, output=None):
    """Nonzero on failure; overwrite a requested stale receipt with FAIL."""
    try:
        require_normal_python()
        result=fn()
        if result.get('status') not in ('PASS','UPPER_BOUND_ONLY_PASS','ALL_TESTS_PASSED'):
            raise ArithmeticError('missing expected semantic success status')
    except Exception as exc:
        result={'status':'FAIL','checker_version':VERSION,'error_type':type(exc).__name__,'error':str(exc)}
        write_result(result,output)
        return 1
    write_result(result,output)
    return 0
