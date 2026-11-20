"""Four-level Hardy certificates. Run with Python, NumPy, SciPy and SymPy."""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations, permutations

import numpy as np
import sympy as sp
from scipy.optimize import minimize

from check_higher_dimension import P_STAR, basis, chart_objective, maximal_chain

INDICES = tuple(range(4))
PAIRS = tuple(combinations(INDICES, 2))
MATCHINGS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))


def cost(x, y):
    return Fraction(x*y**5 - y*x**5, x**5+y**5)**2


def bounds(d):
    edges = {(i, j): cost(d[i], d[j]) for i, j in PAIRS}
    block = max(edges[p] + edges[q] for p, q in MATCHINGS)
    first = max(edges.values())
    second = min(max(w for pair, w in edges.items() if k not in pair) for k in INDICES)
    norm = sum(x*x for x in d)
    return block/norm, (first+second)/norm


def repeated_optimum(a, b, c):
    return max(cost(a, b) + cost(a, c), cost(b, c))/(2*a*a+b*b+c*c)


def pattern_weights(unitary):
    # The first two indices in each eigenbasis are the exceptional labels.
    c = unitary[:2, :2]
    m = {(i, j): sp.expand_complex(abs(c[i, j])**2) for i in range(2) for j in range(2)}
    q = sp.expand_complex(abs(c.det())**2)
    direct = min(q, m[0, 0], m[1, 1])
    crossed = q-direct
    weights = {(): 1-sum(m.values())+q, ((0, 0), (1, 1)): direct,
               ((0, 1), (1, 0)): crossed}
    for edge, value in m.items():
        weights[(edge,)] = value - (direct if edge[0] == edge[1] else crossed)
    assert min(weights.values()) >= 0 and sum(weights.values()) == 1
    return weights


def exact_pencils():
    # Includes a complex, genuinely mixing change of basis, and singular and
    # unitary exceptional blocks as endpoint cases. No eigensolver is used.
    w = sp.Matrix([[-1,4,2,2], [4,1,2,-2], [2,2,-4,1], [2,-2,1,4]])/5
    h = sp.Matrix([1, 1+sp.I, 2-sp.I, sp.I])
    householder = sp.eye(4) - 2*h*h.H/h.dot(h.conjugate())
    controls = [sp.eye(4), sp.eye(4)[[2,3,0,1], :], w, w*householder]
    x, y = (2, 5, 3, 3), (4, 1, 2, 2)
    for U in controls:
        U = U.applyfunc(sp.simplify)
        assert (U.H*U - sp.eye(4)).applyfunc(sp.simplify) == sp.zeros(4)
        weights = pattern_weights(U)
        representatives = {}
        for pi in permutations(INDICES):
            pattern = tuple((i, pi[i]) for i in range(2) if pi[i] < 2)
            representatives[pattern] = pi
        # Both sides are polynomials of degree at most four; five points suffice.
        for z in (-2, -1, 0, 1, 2):
            left = [v**4-z*v**5 for v in x]
            right = [-v**4-z*v**5 for v in y]
            actual = (sp.diag(*left) + U*sp.diag(*right)*U.H).det()
            predicted = sum(weights[pattern]*sp.prod(left[i]+right[pi[i]] for i in INDICES)
                            for pattern, pi in representatives.items())
            assert sp.simplify(actual-predicted) == 0
    # A full minors mixture would impose this inequality even on distinct labels.
    def separator(M):
        return (abs(M[0,0])**2 + abs(M[2,3])**2
                - abs(M.extract([0,1], [0,2]).det())**2
                + abs(M.extract([0,3], [2,3]).det())**2)
    assert all(separator(sp.eye(4)[list(pi), :]) >= 0 for pi in permutations(INDICES))
    assert separator(w) == -sp.Rational(14,625)
    print("Four exact pencil identities and the 24-permutation obstruction passed.")


def exact_spectra():
    lower_rho = Fraction(1324717957, 10**9)
    assert lower_rho > 1 and lower_rho**3 < lower_rho+1
    lower_p = (8*lower_rho**2+lower_rho-11)/25
    counts = [0,0,0]
    for d in combinations(range(1,17), 4):
        low, high = bounds(d)
        assert low <= high
        counts[0] += 1
        counts[1] += (low == high)
        counts[2] += (high < lower_p)
    assert counts == [1820,286,1426]
    assert repeated_optimum(1,2,3) == Fraction(2028,15125)
    assert bounds((2,3,4,5)) == (Fraction(98392400,579046347),)*2
    print(f"{counts[0]} increasing integer spectra, {counts[1]} exact optima, "
          f"{counts[2]} certified strictly below the ceiling.")


def direct_witness(d, pairing, target):
    spectrum = np.array(d, dtype=float)
    spectrum /= np.linalg.norm(spectrum)
    frame = np.zeros((4,2))
    for k, (i,j) in enumerate(pairing):
        frame[i,k], frame[j,k] = spectrum[j]**2.5, spectrum[i]**2.5
    forbidden, achieved = maximal_chain(spectrum, basis(frame))
    assert forbidden < 1e-22 and abs(achieved-float(target)) < 1e-12


def exploratory_search():
    rng = np.random.default_rng(20261120)
    max_excess = -np.inf
    for _ in range(100):
        d = np.sort(np.exp(rng.uniform(-1.5, 1.5, 4)))
        d /= np.linalg.norm(d)
        def e(i, j):
            x, y = d[i], d[j]
            return ((x*y**5-y*x**5)/(x**5+y**5))**2
        pairing = max(e(*i)+e(*j) for i,j in MATCHINGS)
        for _ in range(10):
            permuted = d[rng.permutation(4)]
            logs = np.log(permuted[1:]/permuted[0])
            def objective(z):
                f, g = chart_objective(np.r_[logs,z,np.zeros(4)],4,2)
                return f,g[3:7]
            result = minimize(objective,rng.normal(0,1.1,4),jac=True,method="L-BFGS-B",
                              bounds=[(-8,8)]*4, options={"ftol":1e-13,"gtol":1e-8,"maxiter":250})
            max_excess = max(max_excess,-result.fun-pairing)
    print(f"1,000 local starts on 100 spectra: greatest excess over best pairing {max_excess:.3g}.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--search", action="store_true", help="also run exploratory local optimization")
    args = parser.parse_args()
    exact_pencils()
    exact_spectra()
    direct_witness((1,1,2,3), ((0,1),(2,3)), Fraction(2028,15125))
    direct_witness((2,3,4,5), ((0,2),(1,3)), Fraction(98392400,579046347))
    r = 1.324717957244746
    direct_witness((1,1,r**-2,r**2), ((0,2),(1,3)), P_STAR)
    print("Three direct six-setting controls passed.")
    if args.search:
        exploratory_search()
