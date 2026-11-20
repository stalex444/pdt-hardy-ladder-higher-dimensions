"""Check the exact Hardy K=2 subspace reduction. Requires NumPy and SciPy."""
import numpy as np
from scipy.linalg import eigvalsh
from scipy.optimize import minimize

RHO = 1.32471795724474602596
P_STAR = (8 * RHO**2 + RHO - 11) / 25


def basis(x):
    return np.linalg.qr(x, mode="reduced")[0]


def complement(x):
    return np.linalg.qr(x, mode="complete")[0][:, x.shape[1]:]


def probability(a, d, b):
    """The Bob subspace has already been conjugated in the Schmidt basis."""
    return np.linalg.norm(a.conj().T @ (d[:, None] * b), "fro") ** 2


def score(d, u):
    u = basis(u)
    v = complement(d[:, None]**5 * u)
    return probability(u, d, v)


def doubled_score(d, u):
    """Trace quotient after diagonalizing the swap; the trace doubles with the state."""
    h = basis(d[:, None]**2.5*u)
    w = 2*(h @ h.conj().T) - np.eye(len(d))
    delta = np.diag(d**-4) - (w*d**-4) @ w
    total = np.diag(d**-5) + (w*d**-5) @ w
    eigenvalues = eigvalsh(delta, total)
    return np.dot(eigenvalues, eigenvalues)/2


def pair_error(x, y):
    return abs(x*y**5 - y*x**5) / (x**5 + y**5)


def maximal_chain(d, u):
    """Start at A0=D²U. Each space has orthonormal columns."""
    col = d[:, None]
    a0 = basis(col**2 * u)
    b0 = complement(col * a0)
    a1, b1 = basis(b0 / col), basis(a0 / col)
    a2, b2 = basis(b1 / col), basis(a1 / col)
    forbidden = [probability(a0, d, b0),
                 probability(a1, d, complement(b0)),
                 probability(complement(a0), d, b1),
                 probability(a2, d, complement(b1)),
                 probability(complement(a1), d, b2)]
    return max(forbidden), probability(a2, d, b2)


def validate(rng):
    largest_zero, largest_diff, largest_rank_one_excess = 0., 0., 0.
    for n in range(2, 9):
        for rank in range(1, n):
            for _ in range(15):
                d = np.exp(rng.uniform(-1.2, 1.2, n))
                d /= np.linalg.norm(d)
                u = basis(rng.normal(size=(n, rank)) + 1j*rng.normal(size=(n, rank)))
                p = score(d, u)
                zero, direct = maximal_chain(d, u)
                v = complement(d[:, None]**5 * u)
                largest_zero = max(largest_zero, zero)
                largest_diff = max(largest_diff, abs(p-direct), abs(p-score(d, v)), abs(p-doubled_score(d, u)))
                if rank in (1, n-1):
                    errors = [[pair_error(x, y) for y in d] for x in d]
                    i, j = np.unravel_index(np.argmax(errors), (n, n))
                    exact = errors[i][j]**2
                    witness = np.zeros((n, 1))
                    witness[i, 0], witness[j, 0] = d[j]**2.5, d[i]**2.5
                    largest_diff = max(largest_diff, abs(score(d, witness)-exact))
                    largest_rank_one_excess = max(largest_rank_one_excess, p-exact, exact-P_STAR)
    assert largest_zero < 1e-17 and largest_diff < 1e-8 and largest_rank_one_excess < 1e-10
    print(f"420 random direct-chain checks: largest forbidden probability {largest_zero:.3g}")
    print(f"largest identity/witness discrepancy {largest_diff:.3g}, rank-one excess {largest_rank_one_excess:.3g}")


def optimize_rank_two(rng, starts=12):
    """Finite exploratory searches on a dense chart of Gr(2,4); no upper-bound certificate."""
    def negative_score(x):
        d = np.exp(np.r_[0., x[:3]])
        z = (x[3:7] + 1j*x[7:]).reshape(2, 2)
        return -score(d / np.linalg.norm(d), np.vstack([np.eye(2), z]))

    best = 0.
    for _ in range(starts):
        x = rng.uniform(-1, 1, 11)
        result = minimize(negative_score, x, method="L-BFGS-B",
                          bounds=[(-1.5, 1.5)]*3 + [(-3., 3.)]*8,
                          options={"ftol": 2e-14, "gtol": 2e-8, "maxiter": 400})
        best = max(best, -result.fun)
    print(f"{starts} local four-dimensional complex rank-two searches: best {best:.12f}; two-qubit value {P_STAR:.12f}")


def chart_objective(x, n, rank):
    """Negative trace residual and its analytic gradient in a complex graph chart."""
    m = (n-rank)*rank
    d = np.exp(np.r_[0., x[:n-1]])
    b = (x[n-1:n-1+m] + 1j*x[n-1+m:]).reshape(n-rank, rank)
    u = np.vstack([np.eye(rank), b])
    h_inv = np.linalg.inv(u.conj().T @ u)
    image = d[:, None]**5*u
    target = d[:, None]*u
    # QR least squares avoids forming the condition-number-squaring normal equations.
    coeff = np.linalg.lstsq(image, target, rcond=None)[0]
    residual = target-image@coeff
    e = residual@h_inv
    raw = np.vdot(residual, e).real
    norm2 = np.dot(d, d)
    f = raw/norm2
    y = e@coeff.conj().T
    du = 2*(d[:, None]*e - d[:, None]**5*y - u@h_inv@(residual.conj().T@e))/norm2
    dd = 2*np.real(np.sum(u.conj()*(e-5*d[:, None]**4*y), axis=1))
    dlog = (d*dd-2*d**2*f)/norm2
    g = np.r_[dlog[1:], du[rank:].real.ravel(), du[rank:].imag.ravel()]
    return -f, -g


def twelve_dimensional(rng):
    # Six copies of an optimal pair with deliberately unequal Schmidt masses.
    # All 12 Schmidt coefficients are nonzero, and the spectrum is simple.
    q = RHO**-2
    shift = np.array([1., 2., 3., 5., 7., 11.])
    shift = np.sqrt(shift/np.sum(shift))
    a, b = 1/np.sqrt(1+q*q), q/np.sqrt(1+q*q)
    d = np.ravel(np.c_[a*shift, b*shift])
    u = np.kron(np.eye(6), np.array([[b**2.5], [a**2.5]]))
    assert len(np.unique(d)) == 12
    zero, control = maximal_chain(d, basis(u))
    assert zero < 1e-17 and abs(control-P_STAR) < 1e-12
    print(f"rank-12 pure state, six qubit blocks, direct-chain score {control:.12f}")
    for rank in (2, 3, 6):
        n, starts = 12, 12
        variables = n-1+2*(n-rank)*rank
        test = rng.normal(0., .4, variables)
        direction = rng.normal(size=variables)
        direction /= np.linalg.norm(direction)
        eps = 1e-6
        plus = chart_objective(test+eps*direction, n, rank)[0]
        minus = chart_objective(test-eps*direction, n, rank)[0]
        _, grad = chart_objective(test, n, rank)
        assert abs((plus-minus)/(2*eps)-np.dot(grad, direction)) < 2e-8
        best = 0.
        for _ in range(starts):
            init = rng.uniform(-.8, .8, variables)
            result = minimize(chart_objective, init, args=(n, rank), jac=True,
                              method="L-BFGS-B",
                              bounds=[(-1.5, 1.5)]*(n-1)+[(-3., 3.)]*(variables-n+1),
                              options={"maxiter": 450, "ftol": 1e-13, "gtol": 2e-7})
            best = max(best, -result.fun)
        print(f"dimension 12, subspace rank {rank}, {starts} local searches: best {best:.12f}")


if __name__ == "__main__":
    rng = np.random.default_rng(20261120)
    validate(rng)
    optimize_rank_two(rng)
    twelve_dimensional(rng)
