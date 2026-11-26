from pathlib import Path
from sys import argv
import subprocess
root=Path(__file__).parent
order=argv[1]; sec=int(argv[2]);case=argv[3]
assert order.count('N')==1 and order.count('A') in (2,4) and len(order)==order.count('A')+1
one=order.count('A')==2; ninputs=6 if one else 9
n=0; C=[]
def new():
 global n
 n+=1;return n
T=new();C.append((T,));F=-T
def clause(ls):
 s=set(ls)
 if T in s or any(-a in s for a in s):return
 s.discard(F);C.append(tuple(sorted(s)))
def land(a,b):
 if a==F or b==F or a==-b:return F
 if a==T or a==b:return b
 if b==T:return a
 u=new();clause([-u,a]);clause([-u,b]);clause([u,-a,-b]);return u
def lor(items):
 s=set(items);s.discard(F)
 if T in s:return T
 if not s:return F
 if len(s)==1:return next(iter(s))
 u=new();clause([-u,*s]);
 for t in s:clause([-t,u])
 return u
sel=[[[new() for _ in range(1+ninputs+i)] for _ in range(1 if op=='N' else 2)] for i,op in enumerate(order)]
out=[[new() for _ in range(1+ninputs+len(order))] for _ in range(1 if one else 2)]
rows=0
for x in range(1<<ninputs):
 a,b,c=x&7,x>>3&7,x>>6&7;target=[bool(a&b)] if one else [bool(a&b),bool(a&c)]
 if not one and case=='small' and b and c and x.bit_count()>3 and not (a.bit_count()==1 and target[0]!=target[1] and b.bit_count()+c.bit_count()<=3):continue
 w=[T]+[T if x>>i&1 else F for i in range(ninputs)];rows+=1
 for op,ss in zip(order,sel):
  z=[lor(land(bit,signal) for bit,signal in zip(s,w)) for s in ss];w.append(-z[0] if op=='N' else land(*z))
 for flag,s in zip(target,out):
  u=lor(land(bit,signal) for bit,signal in zip(s,w));clause([u if flag else -u])
fn=root/f'free-{order}-{case}.cnf';fn.write_text(f'p cnf {n} {len(C)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in C));p=subprocess.run(['/root/.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical','-q','--lrat','--no-binary','-t',str(sec),fn,fn.with_suffix('.lrat')],capture_output=True,text=True,timeout=sec+5);print(order,case,rows,n,len(C),p.returncode,p.stdout[:50],flush=True)
if p.returncode==10:
 m={int(v) for l in p.stdout.splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0};print('found',[(op,[[i for i,b in enumerate(s) if b in m] for s in ss]) for op,ss in zip(order,sel)],[[i for i,b in enumerate(s) if b in m] for s in out])
