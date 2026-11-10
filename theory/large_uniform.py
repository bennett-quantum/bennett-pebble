#!/usr/bin/env python3
"""Balanced nested upper bounds and continuous-envelope analysis, not optima."""
import json, math
T=10**9

def balanced_cost(n,d,a=1,k=0):
    if d==0: return a*n
    h=n//2
    return 2*balanced_cost_cached(h,d-1,a,k)+balanced_cost_cached(n-h,d-1,a,k)+k
from functools import lru_cache
balanced_cost_cached=lru_cache(None)(balanced_cost)

def main():
    out=[]
    for m in (10**3,10**5,10**7):
        for r in (1,10,10**3):
            options=[]
            for d in range(T.bit_length()):
                L=(T+(1<<d)-1)//(1<<d)
                options.append(( (d+1)*m+L*r,d,L,balanced_cost_cached(T,d),balanced_cost_cached(T,d,1,m)))
            S,d,L,C,Ccopy=min(options)
            out.append(dict(m=m,r=r,depth=d,max_leaf=L,space=S,forward_no_copy_cost=C,
                oracle_step_factor=2*C/T,forward_if_k_equals_m=Ccopy))
    with open('theory/large_uniform_results.json','w') as f: json.dump(out,f,indent=2)
    print(json.dumps(out,indent=2))
if __name__=='__main__': main()
