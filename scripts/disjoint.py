"""Where #131's H^2 >= H has slack: the disjoint-pair term D of mix:expansion.

Run from the repository root:
    python scripts/disjoint.py [NMAX] [MAXSTATES]
Computes D = sum over ordered disjoint pairs (a, b) of h_a h_b directly, checks the identity
H^2 = sum_T H_T^2 - (n-3) H + D to 1e-9, and reports the least eigenvalue on centered functions
of D - H, D - 2(I - Pi), sum_T (H_T^2 - H_T) and H^2 - 2H. Prints PASS and exits 0 when all four
are >= -1e-9 on every sequence with at most MAXSTATES realizations. Finite numerical evidence.
Use --nmin 9 to check only the extension and --workers to limit parallel memory use.
"""

import os
import sys
import argparse

for var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(var, "2")

from itertools import combinations  # noqa: E402
from multiprocessing import Pool  # noqa: E402
from time import perf_counter  # noqa: E402

import numpy as np  # noqa: E402
import scipy.sparse as sp  # noqa: E402
from scipy.sparse.linalg import LinearOperator, eigsh  # noqa: E402

from sweep import fibers, realizations, sequences  # noqa: E402

TOL = 1e-9
NAMES = ("D-H", "D-2(I-Pi)", "triples", "H^2-2H")


def least_centered(X, shift=0.0):
    """Least centered eigenvalue, capped at 10 by lifting the constant direction."""
    m = X.shape[0]
    if m <= 100:
        return float(np.linalg.eigvalsh(
            X.toarray() - shift * np.eye(m) + (10 + shift) / m)[0])
    op = LinearOperator(X.shape, matvec=lambda v: X @ v - shift * v
                        + (10 + shift) * np.mean(v), dtype=float)
    v0 = np.random.default_rng(131).normal(size=m)
    values, vectors = eigsh(op, k=1, which="SA", tol=1e-11, v0=v0)
    residual = np.linalg.norm(op @ vectors[:, 0] - values[0] * vectors[:, 0])
    assert residual < 1e-8, ("eigenpair residual", residual)
    return float(values[0])


def analyse(arg):
    d, cap = arg
    n, states = len(d), realizations(d, cap=cap)
    m = len(states)
    if m <= 1 or m > cap:
        return None
    eye = sp.identity(m, format="csr")
    h = {}
    for i, j in combinations(range(n), 2):
        rows, cols, vals = [], [], []
        for ids in fibers(states, n, i, j):
            for x in ids:
                rows += [x] * len(ids)
                cols += ids
                vals += [1.0 / len(ids)] * len(ids)
        h[(i, j)] = eye - sp.csr_matrix((vals, (rows, cols)), shape=(m, m))
    H = sum(h.values())
    D = sp.csr_matrix((m, m))
    for a, b in combinations(h, 2):
        if not set(a) & set(b):
            prod = h[a] @ h[b]
            D = D + prod + prod.T
    triples = sp.csr_matrix((m, m))
    for T in combinations(range(n), 3):
        HT = sum(h[p] for p in combinations(T, 2))
        triples = triples + HT @ HT - HT
    H2 = H @ H
    error = H2 - (triples + H + D)
    gap = max(abs(error.data), default=0.0)
    assert gap < TOL, (d, "mix:expansion identity", gap)
    least = [least_centered(D - H), least_centered(D, shift=2),
             least_centered(triples), least_centered(H2 - 2 * H)]
    return d, m, least


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("nmax", type=int, nargs="?", default=8)
    parser.add_argument("cap", type=int, nargs="?", default=2000)
    parser.add_argument("--nmin", type=int, default=4)
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    nmax, cap = args.nmax, args.cap
    t0 = perf_counter()
    todo = [(d, cap) for n in range(args.nmin, nmax + 1) for d in sequences(n)]
    with Pool(args.workers) as pool:
        rows = [r for r in pool.map(analyse, todo, chunksize=1) if r]
    print(f"{len(rows)} of {len(todo)} sequences have 2..{cap} realizations, "
          f"{args.nmin} <= n <= {nmax}")
    for k, name in enumerate(NAMES):
        worst = min(rows, key=lambda r: r[2][k])
        tight = [r for r in rows if r[2][k] < 1e-6]
        print(f"{name:10s} least eigenvalue {worst[2][k]: .2e} at {worst[0]}; "
              f"equality in {len(tight)}, e.g. {[r[0] for r in tight[:3]]}")
    ok = all(x >= -TOL for r in rows for x in r[2])
    print(f"{'PASS' if ok else 'FAIL'}: wall {perf_counter() - t0:.1f}s")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
