"""Independent parser of printed TeX, with shared published exact arithmetic.

Does not import the manuscript generator. Reads immutable v0.1 JSON for byte
correspondence, and reconstitutes matrices from the actual typeset-data sources.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re,sys
BASE=Path(__file__).resolve().parent.parent;PAPER=BASE/'repo'/'paper';FROZEN=BASE/'repo'/'artifact_v0.1'
sys.path.insert(0,str(BASE/'repo'/'artifact_v0.1.1'))
import verify_independent as v
from strict_schema import load_document

def need(cond,label):
 if not cond:raise ArithmeticError(label)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

A=load_document(FROZEN/'EXACT_KERNELS.json')[0];C=load_document(FROZEN/'EXACT_SOS_CANDIDATE.json')[0];P=load_document(FROZEN/'POSITIVITY_CERTIFICATE.json')[0];S=load_document(FROZEN/'SOS14.json')[0]
# Independent raw-numeral parser for both long and short Verbatim records.
def numerals(body,count):
 den=re.findall(r'^d = ([0-9]+)$',body,re.M);need(len(den)==1,'one denominator')
 nums={}
 for line in body.splitlines():
  if line.startswith('n = ('):
   ns=list(map(int,re.findall(r'-?\d+',line)));need(len(ns)==count,'short numerator list');nums.update(enumerate(ns))
  elif line.startswith('n['):
   lhs,rhs=line.split(' = ');ix=list(map(int,re.findall(r'\d+',lhs)));vals=list(map(int,re.findall(r'-?\d+',rhs)))
   inds=list(range(*ix)) if len(ix)==2 else ix;need(len(inds)==len(vals),'indexed record arity')
   for i,val in zip(inds,vals):need(i not in nums,'no duplicated numerator index');nums[i]=val
 need(sorted(nums)==list(range(count)),'all numerator indices')
 return {'n':[str(nums[i]) for i in range(count)]+['0']*(24-count),'d':den[0]}

kernel_text=(PAPER/'kernel_data.tex').read_text();params_text=(PAPER/'parameter_data.tex').read_text()
Krecords={}
for k,a,b,body in re.findall(r'\\textbf\{\$K_\{(\d+)\}\[(\d+),(\d+)\]\$\}\s*\\begin\{Verbatim\}[^\n]*\n(.*?)\\end\{Verbatim\}',kernel_text,re.S):
 key=(int(k),int(a),int(b));need(key not in Krecords,'unique K entry');Krecords[key]=numerals(body,24)
need(len(Krecords)==14,'14 complete nontrivial K records')
Hrecords={}
for m,body in re.findall(r'\\textbf\{\$h_\{(\d+)\}\$\}\s*\\begin\{Verbatim\}[^\n]*\n(.*?)\\end\{Verbatim\}',params_text,re.S):
 m=int(m);need(m not in Hrecords,'unique h record');Hrecords[m]=numerals(body,12)
need(sorted(Hrecords)==list(range(42)),'all42 h records')
for m,val in Hrecords.items():need(val==C['parameters'][m],'literal h record matches frozen scalar '+str(m))
for (k,a,b),val in Krecords.items():need(val==A['kernels'][str(k)]['K'][a][b],'literal K record matches frozen scalar')
assign={}
for line in (PAPER/'parameter_assignments.tex').read_text().splitlines():
 if re.match(r'^\d+ &',line):
  parts=[x.strip() for x in line.split('&')];parts[-1]=parts[-1].split('\\')[0].strip();need(len(parts)==10,'assignment columns')
  for offset in [0,5]:
   m,k,a,b=map(int,parts[offset:offset+4]);typ=parts[offset+4];need(m not in assign,'unique h assignment');assign[m]=[k,a,b,typ]
need(sorted(assign)==list(range(42)),'all42 assignments')
for m,x in assign.items():need(x==C['meta'][m],'literal assignment matches frozen meta')
phases={}
for line in (PAPER/'phase_supports.tex').read_text().splitlines():
 match=re.match(r'^(\d+) & (\d+) & (.*)',line)
 if match:
  k,ell=int(match[1]),int(match[2]);pairs=[tuple(map(int,x)) for x in re.findall(r'\((\d+),(\d+)\)',match[3])]
  need((k,ell) not in phases and len(pairs)==4,'phase unique four-entry column');phases[k,ell]=pairs
need(len(phases)==20,'20 F columns')
for (k,ell),pairs in phases.items():
 expected=[(j,e) for j,e in enumerate(A['kernels'][str(k)]['exponents'][ell]) if e is not None]
 need(pairs==expected,'printed phase list matches frozen column')
minors={}
for line in (PAPER/'minor_bounds.tex').read_text().splitlines():
 match=re.match(r'^(\d+) & (\d+) & (\d+) & (\d+)',line)
 if match:
  k,j,lo,hi=map(int,match.groups());need((k,j) not in minors,'unique minor row');minors[k,j]=(Fraction(lo,10**15),Fraction(hi,10**15))
need(len(minors)==14,'14 minor rows')
main=(PAPER/'main.tex').read_text();nums={name:int(re.search(r'^'+name+r' = (\d+)$',main,re.M)[1]) for name in ['M','S','U']};N=2**256
root_boxes={'mu':(Fraction(nums['M'],10*N),Fraction(nums['M']+1,10*N)),'sqrt5':(Fraction(nums['S'],N),Fraction(nums['S']+1,N)),'u':(Fraction(nums['U'],N),Fraction(nums['U']+2,N))}
for name,box in root_boxes.items():need(box==v.read_interval(P['embedding_boxes'][name]),'printed root box '+name)
ib=v.interval_basis(P['embedding_boxes']);q=[tuple(map(tuple,x)) for x in A['Q']];entries=compact=0
for k in [1,6,7,8,9]:
 size={'1':2,'6':4,'7':3,'8':3,'9':2}[str(k)];K=[[v.ZERO]*size for _ in range(4)];F=[[v.ZERO]*4 for _ in range(81)]
 if k==6:
  for i in range(4):K[i][i]=v.ONE
 else:
  for a in range(4-size):
   for b in range(size):K[a][b]=v.load_scalar(Krecords[k,a,b])
  for i in range(size):K[4-size+i][i]=v.ONE
 for ell in range(4):
  for j,e in phases[k,ell]:F[j][ell]=v.ZS[e]
 E=[[sum(F[i][ell]*K[ell][j] for ell in range(4)) for j in range(size)] for i in range(81)]
 need(E==v.matrix(A['kernels'][str(k)]['E']),'E reconstructed from printed F,K');entries+=81*size
 H=[[v.ZERO]*size for _ in range(size)]
 for m,(block,a,b,typ) in assign.items():
  if block!=k:continue
  val=v.load_scalar(Hrecords[m]);need(val==val.conjugate(),'h exactly real')
  if typ=='I':H[a][b]+=v.I*val;H[b][a]-=v.I*val
  else:
   H[a][b]+=val
   if a!=b:H[b][a]+=val
 need(H==v.matrix(C['H'][str(k)]),'H reconstructed from printed h')
 L=v.matrix(P['blocks'][str(k)]['L']);D=list(map(v.load_scalar,P['blocks'][str(k)]['D']))
 for r in range(size):
  need(H[r][r]==D[r]+sum(L[r][t]*L[r][t].conjugate()*D[t] for t in range(r)),'printed d recurrence after clearing no denominators')
  for j in range(r+1,size):
   need(L[j][r]*D[r]==H[j][r]-sum(L[j][t]*D[t]*L[r][t].conjugate() for t in range(r)),'printed L recurrence cleared')
  term=next(t for t in S['terms'] if t['id']==f'{k}:{r}');poly={tuple(map(tuple,x['word'])):v.load_scalar(x['coefficient']) for x in term['polynomial']}
  need(D[r]==v.load_scalar(term['weight']),'compact weight exactly same')
  for i in range(81):need(sum(E[i][a]*L[a][r] for a in range(size)).conjugate()==poly.get(q[i],v.ZERO),'printed R orientation');compact+=1
 for j in range(1,size+1):
  total=v.ZERO
  for perm in itertools.permutations(range(j)):
   prod=v.ONE
   for row,col in enumerate(perm):prod*=H[row][col]
   total+=(-1)**sum(perm[a]>perm[b] for a in range(j) for b in range(a+1,j))*prod
  lower,upper=v.positive(total,ib,'printed leading minor');lo,hi=minors[k,j];need(0<lo<lower<=upper<hi,'strict printed minor bounds')
# Check the manuscript's specifically named minimum weight and simple bracket.
w=[(t['id'],v.bounds(v.load_scalar(t['weight']),ib)[0]) for t in S['terms']];small=dict(w)['9:1']
need(Fraction(3584887,10**10)<small[0]<=small[1]<Fraction(3584888,10**10),'minimum named-weight rational bracket')
need(all(small[1]<box[0] for name,box in w if name!='9:1'),'9:1 is actual strict minimum')
out={'status':'PASS','scope':'independent parsing and algebraic transcription/orientation check of printed TeX; shares published exact arithmetic, not a new arithmetic engine','phase_columns':len(phases),'kernel_scalar_records':len(Krecords),'real_parameter_records':len(Hrecords),'parameter_assignments':len(assign),'factorization_entries':entries,'compact_positions':compact,'compact_weights':14,'strict_leading_minor_bounds':len(minors),'printed_root_boxes':3,'minimum_weight_bracket':True,'source_sha256':sha(Path(__file__)),'paper_sha256':{p.name:sha(p) for p in [PAPER/n for n in ['main.tex','phase_supports.tex','kernel_data.tex','parameter_assignments.tex','parameter_data.tex','minor_bounds.tex']]},'frozen_input_sha256':{p.name:sha(p) for p in [FROZEN/n for n in ['EXACT_KERNELS.json','EXACT_SOS_CANDIDATE.json','POSITIVITY_CERTIFICATE.json','SOS14.json']]}}
(BASE/'hardening_work'/'PRINTED_CERTIFICATE_REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
