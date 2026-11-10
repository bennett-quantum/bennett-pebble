"""k-ary balanced nested schedules for the uniform chain game (owner's check).

Family: L levels, fan-out k, history leaves of length l.
  T = l*k^L,  compute cost C = a*l*(2k-1)^L + copies,  peak S = m*(1+L*(k-1)) + l*r
It is inside THEORY's nested class N (a split whose right routine splits again),
so the exact class-N DP (B7) can only do better. We compare against that DP at
small T, then tabulate the family's frontier at T = 1e9.
"""
import sys, math, json
from functools import lru_cache
sys.setrecursionlimit(100000)

def nested_dp(T, m, r, S, a=1, k=0):
    INF = float('inf')
    @lru_cache(None)
    def F(t, s):
        if s < m: return INF
        if t == 0: return 0
        best = a*t if m + r*t <= s else INF
        for h in range(1, t):
            left = F(h, s-m)
            if left == INF: continue
            right = F(t-h, s-m)
            if right == INF: continue
            c = 2*left + k + right
            if c < best: best = c
        return best
    return F(T, S)

@lru_cache(None)
def family_cost(n, L, k):
    """exact cost of the rounded k-ary schedule on n steps, a=1, copies free"""
    if L == 0 or n <= 1: return n, n          # (cost, longest leaf)
    q, rem = divmod(n, k)
    big = family_cost(q+1, L-1, k) if rem else (0, 0)
    small = family_cost(q, L-1, k) if q > 0 else (0, 0)
    nbig, nsmall = rem, (k-rem if q > 0 else 0)
    # the last segment is run once; put a small one last when there is one
    if nsmall > 0:
        cost = 2*nbig*big[0] + 2*(nsmall-1)*small[0] + small[0]
    else:
        cost = 2*(nbig-1)*big[0] + big[0]
    return cost, max(big[1], small[1])

def family_best(T, m, r, S):
    best = None
    for L in range(0, 40):
        for k in range(2, 4097):
            if L == 0 and k > 2: break
            if k**L > T and L > 0: break
            c, leaf = family_cost(T, L, k)
            s = m*(1 + L*(k-1)) + leaf*r
            if s <= S and (best is None or c < best[0]): best = (c, L, k, leaf, s)
        if L == 0: continue
    return best

if __name__ == '__main__':
    out = {'small': [], 'frontier': []}
    worst = 1.0
    for (m, r) in [(4,1),(8,1),(16,1),(8,2)]:
        for T in (40, 80, 120):
            for S in range(2*m, 12*m+1, m):
                dp = nested_dp(T, m, r, S)
                fb = family_best(T, m, r, S)
                if dp == float('inf'): continue
                ratio = (fb[0]/dp) if fb else None
                if ratio: worst = max(worst, ratio)
                out['small'].append(dict(m=m, r=r, T=T, S=S, dp=dp, family=fb[0] if fb else None, ratio=ratio))
    infeasible = sum(1 for e in out['small'] if e['family'] is None)
    print(f"small instances: {len(out['small'])}, family infeasible where DP feasible: {infeasible}, worst family/DP cost ratio: {worst:.3f}")
    T = 10**9
    print(f"\nT = 1e9, full-oracle replay factor 2C/T (copies not priced)")
    print(f"{'m':>9} {'r':>5} {'qubit cap S':>13} {'L':>3} {'k':>5} {'leaf':>11} {'peak':>13} {'2C/T':>9}")
    for (m, r) in [(10**3,1),(10**3,10),(10**3,100),(10**5,1),(10**5,10),(10**5,100),(10**7,1),(10**7,100)]:
        for mult in (30, 100, 300, 1000, 3000, 10000):
            S = mult*m
            fb = family_best(T, m, r, S)
            if not fb: continue
            c, L, k, leaf, s = fb
            out['frontier'].append(dict(m=m, r=r, S=S, L=L, k=k, leaf=leaf, peak=s, factor=2*c/T))
            print(f"{m:>9} {r:>5} {S:>13,} {L:>3} {k:>5} {leaf:>11,} {s:>13,} {2*c/T:>9.2f}")
    json.dump(out, open(__import__('pathlib').Path(__file__).with_name('kary_frontier.json'),'w'), indent=1)
