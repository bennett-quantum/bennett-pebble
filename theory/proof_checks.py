#!/usr/bin/env python3
"""Finite sanity checks of analytic inverses, ordinary pebble cutoff and ghosts."""
from collections import deque
from math import sqrt
import json

def ordinary(n,T):
    todo=deque([0]);seen={0};best=0
    while todo:
        mask=todo.popleft()
        if mask:best=max(best,mask.bit_length())
        for j in range(T):
            if j and not mask>>(j-1)&1:continue
            nxt=mask^(1<<j)
            if nxt.bit_count()<=n and nxt not in seen:seen.add(nxt);todo.append(nxt)
    return best,len(seen)

def main():
    checked=0
    for n in range(1,7):
        mod=1<<n
        for u in range(mod):
            for c in range(n+3):
                v=(u>>c) if c<n else 0
                residue=u&((1<<c)-1) if c<n else u
                rec=(v<<c)|residue if c<n else residue
                assert rec==u;checked+=1
                v=(u<<c)&(mod-1) if c<n else 0
                residue=u>>(n-c) if c<n else u
                rec=(v>>c)|(residue<<(n-c)) if c<n else residue
                assert rec==u;checked+=1
                signed=u if u<mod//2 else u-mod
                v=(signed>>c)&(mod-1) if c<n else 0
                residue=u&((1<<c)-1) if c<n else u
                rec=((v&((1<<(n-c))-1))<<c)|residue if c<n else residue
                assert rec==u;checked+=1
            for c in range(1,mod,2):
                inv=pow(c,-1,mod)
                assert ((u*c)%mod*inv)%mod==u;checked+=1
    ordinary_checks=[]
    for n in range(5):
        best,count=ordinary(n,1<<n)
        assert best==(1<<n)-1
        ordinary_checks.append(dict(n=n,board=1<<n,max_reached=best,states=count))
    # Unnormalised vector after X measurement, arbitrary complex amplitudes.
    ghost=0
    for width in range(1,4):
        for control in (False,True):
            q=1<<width
            data=list(range(8 if control else 4))
            amplitudes=[complex(i+1,2-i)/10 for i in data]
            for z in range(q):
                def g(i):
                    x=i//2 if control else i
                    c=i%2 if control else 1
                    return c*((3*x+1)%q)
                phases=[-1 if (z&g(i)).bit_count()%2 else 1 for i in data]
                branch=[amplitudes[i]*phases[i]/sqrt(q) for i in data]
                corrected=[branch[i]*phases[i] for i in data]
                assert all(abs(corrected[i]-amplitudes[i]/sqrt(q))<1e-12 for i in data)
                ghost+=1
    out=dict(residue_inverse_checks=checked,ordinary_cutoff_checks=ordinary_checks,ghost_branch_checks=ghost)
    with open('theory/proof_check_results.json','w') as f:json.dump(out,f,indent=2)
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
