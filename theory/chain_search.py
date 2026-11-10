#!/usr/bin/env python3
"""Exact finite-game Dijkstra and a separately specified nested-strategy DP.
No third-party packages. Run --quick for the reproducible report.
Space includes tokens and residues, not temporary evaluator gates.
"""
from heapq import heappush, heappop
from functools import lru_cache
import argparse, json, math

def successors(state,T,m,r,S,a=1,k=1):
    tok,E=state
    used=m*len(tok)+r*E.bit_count()
    for j in sorted(set(tok)):
        q=list(tok); q.remove(j)
        if j<T and not (E>>j)&1 and used+r<=S:
            yield (tuple(sorted(q+[j+1])),E|(1<<j)),a
        if j and (E>>(j-1))&1:
            yield (tuple(sorted(q+[j-1])),E^(1<<(j-1))),a
        if used+m<=S:
            yield (tuple(sorted(tok+(j,))),E),k
        if tok.count(j)>=2:
            yield (tuple(q),E),k

def exact(T,m,r,S,a=1,k=1):
    if S<m: return None,0
    root=((0,),0); dist={root:0}; queue=[(0,root)]
    while queue:
        d,v=heappop(queue)
        if dist[v]!=d: continue
        if T in v[0]: return d,len(dist)
        for w,c in successors(v,T,m,r,S,a,k):
            nd=d+c
            if nd<dist.get(w,math.inf):
                dist[w]=nd; heappush(queue,(nd,w))
    return None,len(dist)

@lru_cache(None)
def nested(T,m,r,S,a=1,k=1):
    if S<m: return math.inf
    if T==0: return 0
    best=a*T if m+r*T<=S else math.inf
    for h in range(1,T):
        best=min(best,2*nested(h,m,r,S-m,a,k)+k+
                 nested(T-h,m,r,S-m,a,k))
    return best

def nested_capacity(m,r,S):
    if r==0: return math.inf if S>=m else -1
    return max([0]+[(1<<d)*((S-(d+1)*m)//r)
        for d in range(max(0,S//m)) if S-(d+1)*m>=r])

def balanced(d,L,m,r,a=1,k=1):
    return (2**d*L,(d+1)*m+L*r,a*L*3**d+k*(3**d-1)//2)

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--quick',action='store_true')
    parser.parse_args()
    cases=[]; gaps=[]; checked=0
    for m,r in [(1,1),(2,1),(3,1),(1,2),(3,2)]:
        for S in range(m,m+3*m+3*r+1):
            for T in range(0,8):
                opt,states=exact(T,m,r,S)
                n=nested(T,m,r,S)
                ni=None if math.isinf(n) else n
                assert opt is None or ni is None or opt<=ni
                if ni is not None: assert opt is not None
                cap=nested_capacity(m,r,S)
                assert (ni is not None)==(T<=cap)
                cases.append(dict(T=T,m=m,r=r,S=S,exact=opt,nested=ni,states=states))
                if ni!=opt: gaps.append(cases[-1])
                checked+=1
    checks=0
    for m,r in [(1,1),(2,1),(3,1),(1,2),(3,2)]:
        for d in range(3):
            for L in range(1,3):
                T,S,cost=balanced(d,L,m,r)
                opt,_=exact(T,m,r,S)
                n=nested(T,m,r,S)
                assert opt is not None and opt<=n<=cost
                checks+=1
    zero=[]
    for T in range(1,8):
        opt,_=exact(T,2,0,2)
        assert opt==T; zero.append(opt)
    one=[]
    for L in range(5):
        S=10+L
        for T in range(7):
            opt,_=exact(T,10,1,S)
            assert opt==(T if T<=L else None)
            one.append((T,L,opt))
    out=dict(cases=checked,balanced_checks=checks,zero_residue_checks=len(zero),
        one_token_checks=len(one),gap_count=len(gaps),first_gaps=gaps[:20],all=cases)
    with open('theory/search_results.json','w') as f: json.dump(out,f,indent=2)
    print(json.dumps({k:v for k,v in out.items() if k!='all'},indent=2))
if __name__=='__main__': main()
