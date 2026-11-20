"""Symbolic and direct six-setting checks for FourLevelPairing.md."""
from itertools import combinations

import numpy as np
import sympy as sp

from check_four_levels import PAIRS, squared_minors
from check_higher_dimension import P_STAR, RHO, basis, maximal_chain
from check_repeated_spectrum import MATCHINGS

EDGES = tuple(PAIRS)
VERTICES = [tuple(int(ij not in matching) for ij in EDGES) for matching in MATCHINGS]


def moments(d, t, m):
    """Return numerator and denominator for D against a positive diagonal T."""
    q = [weight/(t[i]*t[j]) for weight,(i,j) in zip(m,EDGES)]
    def pair_sum(f):
        return sum(w*f(i,j) for w,(i,j) in zip(q,EDGES))
    det_t = pair_sum(lambda i,j: (t[i]*t[j])**2)
    trace_d = pair_sum(lambda i,j: d[i]**2+d[j]**2)
    trace_dt = pair_sum(lambda i,j: d[i]*t[i]+d[j]*t[j])
    mixed = pair_sum(lambda i,j: t[i]**2*d[j]*t[j]+t[j]**2*d[i]*t[i])
    det_dt = pair_sum(lambda i,j: d[i]*t[i]*d[j]*t[j])
    trace_t = pair_sum(lambda i,j: t[i]**2+t[j]**2)
    return trace_d*det_t-trace_dt*mixed+det_dt*trace_t, sum(q)*det_t


def symbolic_coefficients():
    # D and T have eight independent diagonal symbols. T=D^5 is one specialization.
    d = sp.symbols("d:4", real=True)
    t = sp.symbols("t:4", positive=True)
    volume = sp.prod(t)
    def same(left, right):
        if sp.expand(left-right) != 0:
            raise ArithmeticError("Laurent polynomial identity failed")
    units = [tuple(int(i == j) for j in range(6)) for i in range(6)]
    for unit in units:
        n,b = moments(d,t,unit)
        same(n,0)
        same(b,1)
    adjacent_count = 0
    for i,j in combinations(range(6),2):
        differing = set(EDGES[i]) ^ set(EDGES[j])
        if len(differing) != 2:
            continue
        u,v = sorted(differing)
        pair = [x+y for x,y in zip(units[i],units[j])]
        n,b = moments(d,t,pair)
        same(n,(d[u]*t[v]-d[v]*t[u])**2/(t[u]*t[v]))
        same(b,2+t[u]/t[v]+t[v]/t[u])
        adjacent_count += 1

    def coefficients(matching, first_group):
        numerators, denominators = [], []
        for i,j in matching:
            if i not in first_group:
                i,j = j,i
            assert i in first_group and j not in first_group
            numerators.append(d[i]/t[i]-d[j]/t[j])
            denominators.append(1/t[i]+1/t[j])
        a,b = numerators
        s,r = denominators
        return s*r, a*r+b*s, a*b

    for i,j in combinations(range(3),2):
        # The two parts are the edges of the third matching.
        group = set(MATCHINGS[3-i-j][0])
        li,wi,vi = coefficients(MATCHINGS[i],group)
        lj,wj,vj = coefficients(MATCHINGS[j],group)
        ni,bi = moments(d,t,VERTICES[i])
        nj,bj = moments(d,t,VERTICES[j])
        same(bi,volume*li**2)
        same(bj,volume*lj**2)
        same(ni,volume*(wi**2-2*li*vi))
        same(nj,volume*(wj**2-2*lj*vj))
        cross = tuple(x+y for x,y in zip(VERTICES[i],VERTICES[j]))
        n,b = moments(d,t,cross)
        same(b-bi-bj,2*volume*li*lj)
        same(n-ni-nj,2*volume*(wi*wj-lj*vi-li*vj))
    assert adjacent_count == 12
    print("Symbolic identities passed for eight independent diagonal entries: "
          "six diagonals, twelve adjacent minor pairs, all six balanced coefficients.")


def tie_check():
    x = sp.symbols("x", real=True)
    d = (sp.Integer(1), sp.Integer(2), sp.Integer(3), x)
    def signed(i,j):
        a,b = d[i],d[j]
        return sp.cancel((a*b**5-b*a**5)/(a**5+b**5))
    scores = [sum(signed(i,j)**2 for i,j in m) for m in MATCHINGS]
    gap = sp.cancel(scores[0]-scores[1])
    lo,hi = sp.Rational(422,100),sp.Rational(423,100)
    def numerator(f):
        return sp.Poly(sp.cancel(f).as_numer_denom()[0],x)
    assert numerator(gap).count_roots(lo,hi)==1 and gap.subs(x,lo)*gap.subs(x,hi)<0
    # Use a common first group {1,4} in one-based labels.
    delta = signed(0,1)+signed(3,2)-signed(0,2)-signed(3,1)
    assert numerator(delta).count_roots(lo,hi)==0
    for f in [scores[0]-scores[2],scores[1]-scores[2]]:
        assert numerator(f).count_roots(lo,hi)==0 and f.subs(x,lo)>0
    print("Exact root counts isolate a tie for the top two pairings on (1,2,3,x), "
          "4.22 < x < 4.23. Interior graph mixing strictly lowers its score.")


def direct_checks():
    rng = np.random.default_rng(20261120)
    worst_identity = 0.
    for _ in range(160):
        d = np.exp(rng.uniform(-.85,.85,4))
        d /= np.linalg.norm(d)
        h = basis(rng.normal(size=(4,2))+1j*rng.normal(size=(4,2)))
        n,b = moments(d,d**5,squared_minors(h))
        zero,value = maximal_chain(d,basis(h/d[:,None]**2.5))
        worst_identity = max(worst_identity,zero,abs(value-n/b))
        scores = [sum(((d[i]*d[j]**5-d[j]*d[i]**5)/(d[i]**5+d[j]**5))**2 for i,j in m)
                  for m in MATCHINGS]
        k = int(np.argmax(scores))
        control = np.zeros((4,2))
        for column,(i,j) in enumerate(MATCHINGS[k]):
            control[i,column],control[j,column] = d[j]**2.5,d[i]**2.5
        zero,attained = maximal_chain(d,basis(control))
        worst_identity = max(worst_identity,zero,abs(attained-scores[k]),max(0,value-scores[k]))
    assert worst_identity < 1e-10
    # An irrational, full-rank spectrum with four distinct coefficients attains p*.
    q = RHO**-2
    d = np.array([1.,q,2.,2*q])
    d /= np.linalg.norm(d)
    assert len(set(d))==4
    h = basis(np.array([[1.,0.],[1.,0.],[0.,1.],[0.,1.]]))
    zero,p = maximal_chain(d,basis(h/d[:,None]**2.5))
    assert zero < 1e-20 and abs(p-P_STAR)<1e-13
    print(f"160 complex six-setting and matching controls passed (largest error {worst_identity:.3g}); "
          f"distinct full-rank equality control {p:.12f}.")


if __name__ == "__main__":
    symbolic_coefficients()
    tie_check()
    direct_checks()
