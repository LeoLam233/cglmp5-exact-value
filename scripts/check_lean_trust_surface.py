#!/usr/bin/env python3
"""Conservative project-source trust scan; root axiom printing is a separate mandatory gate."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
root=Path(__file__).resolve().parents[1];paths=[root/'lean/CGLMP5.lean']+sorted((root/'lean/CGLMP5').rglob('*.lean'))
def code_only(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
   if s[i]=='\\':out.extend('  ');i+=2
   elif s[i]=='"':string=False;out.append(' ');i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  elif s[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
forbidden=re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|ofReduceNat|trustCompiler)\b|debug\.skipKernelTC|debug\.skipKernelChecks|\bdecide\s*\+\s*native\b')
review=re.compile(r'\b(opaque|elab|macro|macro_rules|syntax|run_elab|run_tac|run_term_elab|initialize|builtin_initialize|implemented_by|extern)\b')
issues=[];reviews=[];manifest=[]
for p in paths:
 raw=p.read_bytes();code=code_only(raw.decode());name=p.relative_to(root).as_posix();manifest.append({'path':name,'sha256':hashlib.sha256(raw).hexdigest()})
 for m in forbidden.finditer(code):issues.append({'path':name,'line':code.count('\n',0,m.start())+1,'token':m[0]})
 for m in review.finditer(code):reviews.append({'path':name,'line':code.count('\n',0,m.start())+1,'construct':m[1]})
receipt={'status':'PASS' if not issues and not reviews else 'REVIEW_REQUIRED','files':manifest,'forbidden':issues,'manual_review_constructs':reviews,'scope':'Project source only. Final exact #print axioms and pinned dependency/build replay are independent requirements.'};args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':receipt['status'],'files':len(paths),'forbidden':issues,'reviews':reviews},indent=2));raise SystemExit(0 if receipt['status']=='PASS' else 1)
