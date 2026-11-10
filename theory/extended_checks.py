#!/usr/bin/env python3
"""Independent weighted/nonuniform graph search and checks of proved bounds."""
import json,math
from functools import lru_cache
from heapq import heappop,heappush
from chain_search import exact,nested,nested_capacity,balanced

def exact_varying(ms,rs,aa,kk,S):
    T=len(rs); root=((0,),0)
    if ms[0]>S: return None,0
    dist={root:0}; pq=[(0,root)]
    while pq:
        d,v=heappop(pq)
        if d!=dist[v]: continue
        tok,E=v
        if T in tok: return d,len(dist)
        used=sum(ms[j] for j in tok)+sum(rs[j] for j in range(T) if E>>j&1)
        edges=[]
        for j in set(tok):
            q=list(tok);q.remove(j)
            if j<T and not E>>j&1 and used-ms[j]+ms[j+1]+rs[j]<=S:
                edges.append(((tuple(sorted(q+[j+1])),E|1<<j),aa[j]))
            if j and E>>(j-1)&1 and used-ms[j]+ms[j-1]-rs[j-1]<=S:
                edges.append(((tuple(sorted(q+[j-1])),E^(1<<(j-1))),aa[j-1]))
            if used+ms[j]<=S: edges.append(((tuple(sorted(tok+(j,))),E),kk[j]))
            if tok.count(j)>1: edges.append(((tuple(q),E),kk[j]))
        for w,c in edges:
            nd=d+c
            if nd<dist.get(w,math.inf):dist[w]=nd;heappush(pq,(nd,w))
    return None,len(dist)

def nested_varying(ms,rs,aa,kk,S):
    @lru_cache(None)
    def F(i,j,s):
        if s<ms[i]: return math.inf
        if i==j:return 0
        cost=0;res=0;peak=ms[i]
        for e in range(i,j):
            res+=rs[e];cost+=aa[e];peak=max(peak,ms[e+1]+res)
        best=cost if peak<=s else math.inf
        for h in range(i+1,j):
            best=min(best,2*F(i,h,s-ms[h])+kk[h]+F(h,j,s-ms[i]))
        return best
    return F(0,len(rs),S)

def maximum_cost(m,r,S,a,k):
    R=nested_capacity(m,r,S)
    if R==0:return 0
    terms=[]
    if R==(S-m)//r:terms.append(a*R)
    if S>=2*m and R==2*nested_capacity(m,r,S-m):
        terms.append(3*maximum_cost(m,r,S-m,a,k)+k)
    return min(terms)

def main():
    records=[];gaps=[];capacitychecks=[]; maxchecks=0
    for m,r,S in [(1,1,5),(1,1,6),(2,1,7),(1,2,8),(3,1,10)]:
        for a,k in [(1,0),(2,3),(1,8)]:
            for T in range(0,9 if k==0 else 13):
                opt,states=exact(T,m,r,S,a,k);n=nested(T,m,r,S,a,k)
                n=None if math.isinf(n) else n
                L=(S-m)//r
                if opt is not None:
                    lb=a*max(T,2*T-L)+(k if T>L else 0)
                    assert lb<=opt
                assert n is None or (opt is not None and opt<=n)
                rec=dict(T=T,m=m,r=r,S=S,a=a,k=k,exact=opt,nested=n,states=states)
                records.append(rec)
                if opt!=n:gaps.append(rec)
    for m,r in [(1,1),(2,1),(1,2),(3,2)]:
        for S in range(m,m+3*m+3*r+1):
            R=nested_capacity(m,r,S)
            if R<=12:
                opt,_=exact(R,m,r,S)
                after,_=exact(R+1,m,r,S)
                capacitychecks.append(dict(m=m,r=r,S=S,nested_max=R,exact_at=opt,exact_after=after))
                assert opt is not None
                if after is not None:gaps.append(capacitychecks[-1])
            assert maximum_cost(m,r,S,1,1)==nested(R,m,r,S)
            maxchecks+=1
    varying=[]
    profiles=[([2,3,2,4,2],[1,0,2,1],[1,3,2,4],[2,1,3,2,1]),
              ([1,2,1,2,1,2],[2,1,0,1,2],[2,1,2,1,2],[1,2,1,2,1,2]),
              ([3,1,3,1,3],[1,2,1,0],[1,2,4,1],[0,3,1,2,1])]
    for ms,rs,aa,kk in profiles:
        for S in range(ms[0],11):
            opt,states=exact_varying(ms,rs,aa,kk,S)
            n=nested_varying(ms,rs,aa,kk,S);n=None if math.isinf(n) else n
            assert n is None or (opt is not None and opt<=n)
            varying.append(dict(ms=ms,rs=rs,S=S,exact=opt,nested=n,states=states))
    out=dict(weighted_count=len(records),weighted_gaps=gaps,capacity_count=len(capacitychecks),
             capacity_cost_checks=maxchecks,nonuniform_count=len(varying),
             nonuniform_gaps=[v for v in varying if v['exact']!=v['nested']],
             weighted=records,capacities=capacitychecks,nonuniform=varying)
    with open('theory/extended_results.json','w') as f:json.dump(out,f,indent=2)
    print(json.dumps({k:v for k,v in out.items() if k not in ('weighted','capacities','nonuniform')},indent=2))
if __name__=='__main__':main()
