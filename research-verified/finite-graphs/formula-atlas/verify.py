"""Independent check of a full Fin 3 × Fin 5 tree atlas, without relabeling symmetry."""
import gzip
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
with gzip.open(HERE/'formula-atlas.json.gz','rt') as f: db=json.load(f)
assert len(db)==32768 and all(v is not None for v in db)
# Literal mask lookup made directly in row-major convention.
raw=[31, 31<<5, 31<<10] + [1057<<j for j in range(5)]
levels=[set(raw)]; reached=set(raw); paircount=0
assert {k for k,v in enumerate(db) if v[0]==0}==reached
while len(reached)<32768:
    k=len(levels); new=set()
    for i in range((k-1)//2+1):
        j=k-1-i
        for a in levels[i]:
            for b in levels[j]:
                new.add(a&b);new.add(a|b);paircount+=1
    new-=reached
    assert new=={m for m,v in enumerate(db) if v[0]==k},k
    levels.append(new);reached|=new
for i,(k,t,a,b) in enumerate(db):
    if t==-1:
        assert k==0 and raw[a]==i
    else:
        assert t in [0,1] and db[a][0]+db[b][0]+1==k and (a&b if t==0 else a|b)==i
p=HERE/'candidate-3239.json';c=json.loads(p.read_text()); cols=raw.copy()
for t,a,b in c['gates']:
    assert t in ['and','or'] and a<len(cols) and b<len(cols)
    cols.append(cols[a]&cols[b] if t=='and' else cols[a]|cols[b])
assert len(c['gates'])==6 and cols[c['output']]==3239
print('all 32768 minimal sizes matched unoptimized DP;',len(levels),'levels,',paircount,'operand pairs checked, all 32768 predecessor records verified; six-gate witness gives',cols[c['output']])
