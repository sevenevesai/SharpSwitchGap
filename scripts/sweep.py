"""Switch-Laplacian and pair-heat-bath gaps for every graphical degree sequence, n <= NMAX.

Run from the repository root: python scripts/sweep.py [NMAX]
Floating-point (numpy/scipy). Prints PASS and exits 0 when, for every sequence with more than one
realization, gap(L) >= 2, gap(H) >= 2 and H <= L, all to 1e-9. Degrees are >= 1, since isolated
vertices change neither L nor H, and complements are skipped, since complementation maps fibers
and switches onto those of the complementary sequence.
"""

import os
import sys
import argparse

for var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(var, "1")
from collections import defaultdict
from itertools import combinations
from multiprocessing import Pool
from time import perf_counter

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh

TOL = 1e-9


def sequences(n):
    """Nonincreasing graphical sequences with all degrees in [1, n-1], up to complement."""
    def rec(prefix, hi):
        if len(prefix) == n:
            if sum(prefix) % 2 == 0 and erdos_gallai(prefix):
                yield tuple(prefix)
            return
        for x in range(hi, 0, -1):
            yield from rec(prefix + [x], x)

    seen = set()
    for d in rec([], n - 1):
        if tuple(sorted((n - 1 - x for x in d), reverse=True)) not in seen:
            seen.add(d)
            yield d


def erdos_gallai(d):
    n = len(d)
    return all(sum(d[:k]) <= k * (k - 1) + sum(min(x, k) for x in d[k:])
               for k in range(1, n + 1))


def realizations(d, cap=None):
    """Labeled realizations; stop at cap+1 so exceeding the cap is unambiguous."""
    n, out, adj, res = len(d), [], [0] * len(d), list(d)

    def rec(v):
        if cap is not None and len(out) > cap:
            return
        if v == n:
            out.append(tuple(adj))
            return
        remaining = sorted(res[v:], reverse=True)
        if not erdos_gallai(remaining):
            return
        need = res[v]
        for chosen in combinations([w for w in range(v + 1, n) if res[w] > 0], need):
            for w in chosen:
                res[w] -= 1
                adj[v] |= 1 << w
                adj[w] |= 1 << v
            res[v] = 0
            rec(v + 1)
            res[v] = need
            for w in chosen:
                res[w] += 1
                adj[v] &= ~(1 << w)
                adj[w] &= ~(1 << v)
            if cap is not None and len(out) > cap:
                return

    rec(0)
    return out


def fibers(states, n, i, j):
    """Partition of state indices into {i,j}-fibers, keyed by setup.tex's three items."""
    ab = (1 << i) | (1 << j)
    out = defaultdict(list)
    for s, g in enumerate(states):
        ni, nj = g[i] & ~ab, g[j] & ~ab
        rest = tuple(g[w] & ~ab for w in range(n) if w != i and w != j)
        out[(rest, ni & nj, ni ^ nj, (g[i] >> j) & 1)].append(s)
    return list(out.values())


def switch_laplacian(states, n):
    index = {g: s for s, g in enumerate(states)}
    rows, cols = [], []
    for s, g in enumerate(states):
        for i, j in combinations(range(n), 2):
            ab = (1 << i) | (1 << j)
            one = (g[i] ^ g[j]) & ~ab
            for u in range(n):
                if not (one & g[i]) >> u & 1:
                    continue
                for v in range(n):
                    if not (one & g[j]) >> v & 1:
                        continue
                    h = list(g)
                    h[i] ^= (1 << u) | (1 << v)
                    h[j] ^= (1 << u) | (1 << v)
                    h[u] ^= ab
                    h[v] ^= ab
                    rows.append(s)
                    cols.append(index[tuple(h)])
    m = len(states)
    A = sp.coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(m, m)).tocsr()
    A.data[:] = 1.0  # each switch is reached through both of its pairs
    return sp.diags(np.asarray(A.sum(axis=1)).ravel()) - A


def heat_bath(states, n):
    m = len(states)
    rows, cols, vals = [], [], []
    for i, j in combinations(range(n), 2):
        for ids in fibers(states, n, i, j):
            if len(ids) > 1:
                for x in ids:
                    rows += [x] * (len(ids) + 1)
                    cols += ids + [x]
                    vals += [-1.0 / len(ids)] * len(ids) + [1.0]
    return sp.coo_matrix((vals, (rows, cols)), shape=(m, m)).tocsr()


def low_spectrum(X):
    if X.shape[0] <= 2500:
        return np.linalg.eigvalsh(X.toarray())
    return np.sort(eigsh(X, k=3, which="SA", tol=1e-10)[0])


def top_eigenvalue(X):
    if X.shape[0] <= 2500:
        return np.linalg.eigvalsh(X.toarray())[-1]
    return eigsh(X, k=1, which="LA", tol=1e-8)[0][0]


def analyse(d):
    n, states = len(d), realizations(d)
    if len(states) <= 1:
        return None
    L, H = switch_laplacian(states, n), heat_bath(states, n)
    el, eh = low_spectrum(L), low_spectrum(H)
    assert abs(el[0]) < 1e-7 < el[1] and abs(eh[0]) < 1e-7 < eh[1], (d, el[:3], eh[:3])
    return d, len(states), float(el[1]), float(eh[1]), float(top_eigenvalue(H - L))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("nmax", type=int, nargs="?", default=8)
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    nmax = args.nmax
    t0 = perf_counter()
    with Pool(args.workers) as pool:
        rows = [r for r in pool.map(analyse, [d for n in range(4, nmax + 1)
                                              for d in sequences(n)]) if r]
    for n in range(4, nmax + 1):
        rn = [r for r in rows if len(r[0]) == n]
        gl, gh = min(rn, key=lambda r: r[2]), min(rn, key=lambda r: r[3])
        print(f"n={n}: {len(rn)} sequences, max states {max(r[1] for r in rn)}; "
              f"min gap(L) {gl[2]:.6f} at {gl[0]}; min gap(H) {gh[3]:.6f} at {gh[0]}; "
              f"max eig(H-L) {max(r[4] for r in rn):.1e}")
    attained = [r for r in rows if r[2] < 2 + 1e-6]
    print(f"gap(L) = 2 in {len(attained)} sequences; state counts "
          f"{sorted({r[1] for r in attained})}")
    ok = all(r[2] >= 2 - TOL and r[3] >= 2 - TOL and r[4] <= TOL for r in rows)
    print(f"{'PASS' if ok else 'FAIL'}: {len(rows)} sequences, wall {perf_counter() - t0:.1f}s")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
