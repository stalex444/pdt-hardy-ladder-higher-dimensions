"""Check the four-level complex-to-real Hardy reduction. Requires NumPy and SciPy."""
from itertools import combinations, product
from fractions import Fraction

import numpy as np

from check_higher_dimension import maximal_chain

PAIRS = tuple(combinations(range(4), 2))
DIRECTION = (1, -1, 0, 0, -1, 1)


def projected_score(spectrum, minors):
    """Squared Hardy score divided by the total squared Schmidt norm."""
    entries = [(w, spectrum[i], spectrum[j]) for w, (i, j) in zip(minors, PAIRS)]

    def trace(k):
        return sum(w * (x**k + y**k) for w, x, y in entries)

    def determinant(k):
        return sum(w * (x*y)**k for w, x, y in entries)

    mixed = sum(w * (x**10*y**6 + y**10*x**6) for w, x, y in entries)
    return (trace(2) - (trace(6)*mixed - determinant(6)*trace(10))/determinant(10)) / sum(x*x for x in spectrum)


def triangle_test(p):
    a, b, c = p[0]*p[5], p[1]*p[4], p[2]*p[3]
    return 2*c*(a+b) - c*c - (a-b)**2


def squared_minors(frame):
    return np.array([abs(np.linalg.det(frame[[i, j], :]))**2 for i, j in PAIRS])


def first_boundary(p, direction):
    length = min(-w/v for w, v in zip(p, direction) if v < 0)
    if triangle_test(p + length*direction) >= 0:
        return p + length*direction
    # The test along this line is quadratic. With opposite endpoint signs
    # there is a single sign-changing root on the interval.
    lo, hi = 0., length
    for _ in range(70):
        mid = (lo + hi) / 2
        if triangle_test(p + mid*direction) >= 0:
            lo = mid
        else:
            hi = mid
    return p + lo*direction


def recover_real_frame(p):
    lengths = np.sqrt(np.maximum(p, 0))
    def relation(z):
        return z[0]*z[5] - z[1]*z[4] + z[2]*z[3]
    choices = [lengths * [x, y, z, 1, 1, 1] for x, y, z in product((-1, 1), repeat=3)]
    bivector = min(choices, key=lambda z: abs(relation(z)))
    skew = np.zeros((4, 4))
    for value, (i, j) in zip(bivector, PAIRS):
        skew[i, j], skew[j, i] = value, -value
    i, j = PAIRS[int(np.argmax(lengths))]
    return np.linalg.qr(skew[:, [i, j]], mode="reduced")[0]


def exact_controls():
    p = tuple(Fraction(i, 7) for i in (1, 1, 1, 1, 1, 2))
    ends = [tuple(u+t*v for u, v in zip(p,DIRECTION)) for t in (Fraction(-2,21), Fraction(2,49))]
    assert triangle_test(p) > 0 and all(triangle_test(q) == 0 and min(q) >= 0 for q in ends)
    assert projected_score((1,2,3,4), p) == Fraction(16719678830,291596771893)
    assert projected_score((1,2,3,4), ends[1]) > projected_score((1,2,3,4), p)
    impossible = (Fraction(1,2),0,0,0,0,Fraction(1,2))
    assert triangle_test(impossible) < 0
    assert projected_score((1,3,2,2), impossible) == Fraction(167762,44305)


def main():
    exact_controls()
    rng = np.random.default_rng(20261120)
    worst = 0.
    for _ in range(250):
        d = rng.uniform(.35, 1.4, 4)
        d /= np.linalg.norm(d)
        frame = np.linalg.qr(rng.normal(size=(4,2)) + 1j*rng.normal(size=(4,2)), mode="reduced")[0]
        p = squared_minors(frame)
        null, direct = maximal_chain(d, frame)
        candidates = [first_boundary(p, sign*np.array(DIRECTION)) for sign in (1,-1)]
        end = max(candidates, key=lambda q: projected_score(d, q))
        real = recover_real_frame(end)
        null_real, achieved = maximal_chain(d, real)
        errors = (null, null_real, abs(direct-projected_score(d,p)), max(0, direct-achieved),
                  abs(achieved-projected_score(d,end)), np.max(np.abs(squared_minors(real)-end)),
                  np.max(np.abs(np.sum(abs(frame)**2, axis=1)-np.sum(real**2, axis=1))))
        worst = max(worst, *errors)
    assert worst < 2e-9, worst
    print(f"Exact controls passed. 250 complex-to-real reconstructions; largest check error {worst:.3g}.")


if __name__ == "__main__":
    main()
