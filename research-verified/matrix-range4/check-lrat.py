from pathlib import Path
from sys import argv
for file in argv[1:]:
    f=Path(file); cls=[None];nv=0
    for line in f.with_suffix('.cnf').open():
        w=line.split()
        if w[0]=='p':nv,expected=map(int,w[2:]);continue
        a=list(map(int,w)); assert a.pop()==0 and all(0<abs(x)<=nv for x in a)
        cls.append(a)
    assert len(cls)==expected+1
    count=0;empty=False
    for line in f.open():
        v=line.split();i=int(v[0]);del v[0]
        if v[0]=='d':
            assert v[-1]=='0'
            for key in map(int,v[1:-1]):assert 0<key<len(cls) and cls[key] is not None;cls[key]=None
            continue
        u=list(map(int,v)); k=u.index(0);clause=u[:k];hints=u[k+1:-1]
        assert u[-1]==0 and all(0<abs(x)<=nv for x in clause)
        assert len(cls)<=i and hints
        assignment={-x for x in clause}; conflict=False
        for h in hints:
            assert 0<h<len(cls) and cls[h] is not None and not conflict
            free=None
            for l in cls[h]:
                assert l not in assignment
                if -l not in assignment:
                    assert free is None or l==free
                    free=l
            if free is None:conflict=True
            else:assignment.add(free)
        assert conflict
        cls.extend([None]*(i-len(cls)));cls.append(clause)
        count+=1;empty|=not clause
    assert empty
    print(f.name, count, 'reverse-unit-propagation steps; empty clause proved',flush=True)
