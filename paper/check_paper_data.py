#!/usr/bin/env python3
"""Check/reproduce all printed paper data against the immutable certificate.

This is a data-correspondence check using the published cyclotomic arithmetic;
it is NOT an independent arithmetic implementation. No solver is used.
Normal mode only verifies generated tables; --write regenerates them first.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent / "artifact_v0.1.1"
sys.path.insert(0, str(ROOT))
import verify_independent as v
from strict_schema import load_document, require_normal_python

def require(condition, message):
    if not condition:
        raise ArithmeticError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def scalar_lines(obj, real=False):
    ns = obj["n"][:12] if real else obj["n"]
    if sum(int(n) != 0 for n in ns[1:]) == 0:
        return ["d = " + obj["d"], "n = (" + ", ".join(ns) + ")"]
    return ["d = " + obj["d"]] + [f"n[{i:02d}] = {n}" for i, n in enumerate(ns)]

def record(title, obj, real=False, kernel=False):
    if kernel:
        ns = obj["n"]
        lines = ["d = " + obj["d"]]
        for i in range(0,24,6):
            lines.append(f"n[{i:02d}:{i+6:02d}] = (" + ", ".join(ns[i:i+6]) + ")")
    else:
        lines = scalar_lines(obj,real)
    return ("\\par\\medskip\\noindent\\begin{minipage}{\\textwidth}\n"
            + "\\textbf{" + title + "}\n"
            + "\\begin{Verbatim}[fontsize=\\fontsize{8}{9.4}\\selectfont]\n"
            + "\n".join(lines) + "\n\\end{Verbatim}\n\\end{minipage}\n")

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write",action="store_true")
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    require_normal_python()
    files=["EXACT_KERNELS.json","EXACT_SOS_CANDIDATE.json","POSITIVITY_CERTIFICATE.json","SOS14.json"]
    A,C,P,S=[load_document(ROOT/f)[0] for f in files]
    ids=[1,6,7,8,9]
    require(A["blocks"]==C["blocks"]==ids,"block convention")
    alice=[()]+[((r,k),) for r in (0,2) for k in range(1,5)]
    bob=[()]+[((r,k),) for r in (1,3) for k in range(1,5)]
    q=[a+b for a in alice for b in bob]
    require(q==[tuple(map(tuple,w)) for w in A["Q"]],"explicit printed Q order")
    require(C["mu_polynomial"]==[5,0,-65,0,144,96,16],"polynomial")
    ib=v.interval_basis(P["embedding_boxes"])
    phase=[r"\begin{longtable}{@{}rrl@{}}",
           r"\caption{Nonzero phase-support pairs $(j,e)$ in column $\ell$ of $F_k$.}\label{tab:phases}\\",
           r"\toprule $k$ & $\ell$ & $(j,e)$ \\ \midrule\endfirsthead",
           r"\toprule $k$ & $\ell$ & $(j,e)$ \\ \midrule\endhead"]
    kernels=[]; minor_rows=[]; minor_records=[]; linkage=0; factor_count=0
    for k in ids:
        z=str(k); obj=A["kernels"][z]
        K=v.matrix(obj["K"]); E=v.matrix(obj["E"]); H=v.matrix(C["H"][z]); n=len(H)
        F=[[v.ZERO]*4 for _ in range(81)]
        for ell,row in enumerate(obj["exponents"]):
            pairs=[]
            for i,e in enumerate(row):
                if e is not None:
                    F[i][ell]=v.ZS[e];pairs.append(f"({i},{e})")
            require(len(pairs)==4,"phase support count")
            phase.append(f"{k} & {ell} & $"+r"\quad ".join(pairs)+r"$ \\")
        for i in range(81):
            for j in range(n):
                require(E[i][j]==sum(F[i][a]*K[a][j] for a in range(4)),"E = FK")
                factor_count+=1
        if k!=6:
            prefix=4-n
            for a in range(prefix):
                for b in range(n):
                    kernels.append(record(f"$K_{{{k}}}[{a},{b}]$",obj["K"][a][b],kernel=True))
            require(all(K[prefix+a][b]==(1 if a==b else 0) for a in range(n) for b in range(n)),"identity tail")
        else:
            require(all(K[a][b]==(1 if a==b else 0) for a in range(4) for b in range(4)),"K6 identity")
        # Reconstruct H from the 42 explicitly printed real parameter records.
        recovered=[[v.ZERO]*n for _ in range(n)]
        for meta,param in zip(C["meta"],C["parameters"]):
            block,a,b,t=meta
            if block!=k:continue
            require(all(int(x)==0 for x in param["n"][12:]),"parameter reality encoding")
            h=v.load_scalar(param); require(h==h.conjugate(),"real h")
            recovered[a][b]+=h*(v.I if t=="I" else 1)
            if a!=b:recovered[b][a]+=h*(-v.I if t=="I" else 1)
        require(recovered==H,"all Hermitian entries from printed h")
        L=v.matrix(P["blocks"][z]["L"]);D=list(map(v.load_scalar,P["blocks"][z]["D"]))
        for i in range(n):
            for j in range(n):
                require(H[i][j]==sum(L[i][r]*D[r]*L[j][r].conjugate() for r in range(n)),"exact LDL")
                if i<=j:require(L[i][j]==(1 if i==j else 0),"unit lower triangular")
        for r in range(n):
            term=next(t for t in S["terms"] if t["id"]==f"{k}:{r}")
            poly={tuple(map(tuple,p["word"])):v.load_scalar(p["coefficient"]) for p in term["polynomial"]}
            for i in range(81):
                require(poly.get(q[i],v.ZERO)==sum(E[i][a]*L[a][r] for a in range(n)).conjugate(),"canonical compact coefficient")
                linkage+=1
            require(v.load_scalar(term["weight"])==D[r],"canonical weight")
            v.positive(D[r],ib,"positive pivot")
        # Determinant expansion uses only + and *, no pivot division.
        for j in range(1,n+1):
            det=v.ZERO
            for perm in itertools.permutations(range(j)):
                sign=(-1)**sum(perm[a]>perm[b] for a in range(j) for b in range(a+1,j))
                value=v.ONE
                for a in range(j):value*=H[a][perm[a]]
                det+=sign*value
            lower,upper=v.positive(det,ib,f"leading minor {k},{j}")
            scale=10**15;lo=math.floor(lower*scale);hi=math.ceil(upper*scale)
            require(Fraction(lo,scale)<lower<=upper<Fraction(hi,scale),"strict outward bounds")
            minor_rows.append(f"{k} & {j} & {lo} & {hi}"+r" \\")
            minor_records.append({"block":k,"size":j,"lower_integer":lo,"upper_integer":hi,"denominator":scale,
                                 "exact_lower":str(lower),"exact_upper":str(upper)})
    phase.extend([r"\bottomrule",r"\end{longtable}"])
    assign=[r"\begin{longtable}{@{}rrrrcrrrrc@{}}",
        r"\caption{Parameter assignments. Each half-row is an independent record.}\label{tab:assignments}\\",
        r"\toprule $m$&$k$&$a$&$b$&type&$m$&$k$&$a$&$b$&type\\\midrule\endfirsthead",
        r"\toprule $m$&$k$&$a$&$b$&type&$m$&$k$&$a$&$b$&type\\\midrule\endhead"]
    for i in range(21):
        row=[]
        for j in [i,i+21]:row+=[str(j)]+list(map(str,C["meta"][j]))
        assign.append(" & ".join(row)+r" \\")
    assign.extend([r"\bottomrule",r"\end{longtable}"])
    params=[record(f"$h_{{{i}}}$",p,real=True) for i,p in enumerate(C["parameters"])]
    minors=[r"\begin{longtable}{@{}rrrr@{}}",
            r"\caption{Positive leading-minor enclosures, with common denominator $10^{15}$.}\label{tab:minors}\\",
            r"\toprule $k$&$j$&$l$&$r$\\\midrule\endfirsthead",
            r"\toprule $k$&$j$&$l$&$r$\\\midrule\endhead"]+minor_rows+[r"\bottomrule",r"\end{longtable}"]
    outputs={"phase_supports.tex":"\n".join(phase)+"\n","kernel_data.tex":"\n".join(kernels),
             "parameter_assignments.tex":"\n".join(assign)+"\n","parameter_data.tex":"\n".join(params),
             "minor_bounds.tex":"\n".join(minors)+"\n"}
    for filename,content in outputs.items():
        path=HERE/filename
        if args.write:path.write_text(content)
        require(path.read_text()==content,"printed TeX mismatch: "+filename)
    require(len(S["terms"])==14 and sum(len(t["polynomial"]) for t in S["terms"])==164,"term counts")
    word_info=v.verify_words(A,C)
    physical_info=v.verify_physical(A,ib)
    result={"status":"PASS","scope":"exact printed-data correspondence and full Gram/physical checks; shared canonical cyclotomic arithmetic",
      "source_hashes":{f:sha(ROOT/f) for f in files},"arithmetic_source_sha256":sha(ROOT/"verify_independent.py"),
      "paper_checker_sha256":sha(Path(__file__)),"printed_table_sha256":{f:sha(HERE/f) for f in outputs},
      "factorization_entries":factor_count,"compact_coefficient_positions":linkage,"compact_weights":14,
      "full_gram_identity":word_info,"physical_attainment":physical_info,
      "leading_minors":minor_records,"python":sys.version,"optimization":sys.flags.optimize}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:value for k,value in result.items() if k!="leading_minors"},indent=2))

if __name__=="__main__":main()
