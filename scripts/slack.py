"""Build both disjoint-pair slack decompositions directly on small graph spaces.

Run from the root: python scripts/slack.py
Checks identities to 1e-9, PSD terms numerically, and reports norms and least
eigenvalues of each term. These finite checks are evidence, not a universal proof.
"""

import os

for var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(var, "1")

from collections import defaultdict
from itertools import combinations
from time import perf_counter

import numpy as np

from sweep import fibers, realizations, switch_laplacian

TOL = 1e-9


def pair_data(states, a):
    n, m = len(states[0]), len(states)
    i, j = a
    ab = (1 << i) | (1 << j)
    E = np.zeros((m, m))
    blocks = []
    for ids in fibers(states, n, i, j):
        E[np.ix_(ids, ids)] = 1 / len(ids)
        g = states[ids[0]]
        singles = (g[i] ^ g[j]) & ~ab
        N, q = singles.bit_count(), (singles & g[i]).bit_count()
        p = (q * (q - 1) + (N - q) * (N - q - 1)) / (N * (N - 1)) if N > 1 else 0
        blocks.append((ids, singles, N, q, p))
    return E, blocks


def error_projection(states, a, b, blocks):
    R, weighted = np.zeros((len(states), len(states))), np.zeros((len(states), len(states)))
    bm = sum(1 << v for v in b)
    for ids, singles, _, _, p in blocks:
        if singles & bm != bm:
            continue
        z = np.array([float(bool(states[t][a[0]] >> b[0] & 1)
                            == bool(states[t][a[0]] >> b[1] & 1)) for t in ids])
        assert abs(z.mean() - p) < TOL
        z -= z.mean()
        norm = z @ z
        if norm > TOL:
            block = np.outer(z, z) / norm
            R[np.ix_(ids, ids)] = block
            weighted[np.ix_(ids, ids)] = p * block
    return R, weighted


def cells(states, a, b):
    outside = [v for v in range(len(states[0])) if v not in a + b]
    om = sum(1 << v for v in outside)
    am, bm = sum(1 << v for v in a), sum(1 << v for v in b)
    groups = defaultdict(list)
    for t, g in enumerate(states):
        key = (tuple(g[w] & om for w in outside), g[a[0]] >> a[1] & 1,
               g[b[0]] >> b[1] & 1, tuple((g[w] & am).bit_count() for w in outside),
               tuple((g[w] & bm).bit_count() for w in outside))
        groups[key].append(t)
    return groups.values()


def cross_projection(states, a, b, index):
    gop = np.zeros((len(states), len(states)))
    am, bm = sum(1 << v for v in a), sum(1 << v for v in b)
    for t, g in enumerate(states):
        if all((g[v] & bm).bit_count() == 1 for v in a) and all(
                (g[v] & am).bit_count() == 1 for v in b):
            h = list(g)
            for v in a:
                h[v] ^= bm
            for v in b:
                h[v] ^= am
            gop[t, t], gop[t, index[tuple(h)]] = .5, -.5
    return gop


def cell_terms(states, ids, a, b, Ea, Eb):
    """P_J from the two ranges, Phi independently from the event-correlation plane."""
    ix = np.ix_(ids, ids)
    ev, vectors = np.linalg.eigh(Ea[ix] + Eb[ix])
    kernel = vectors[:, ev < TOL]
    pj = kernel @ kernel.T
    phi = np.zeros_like(pj)
    am, bm = sum(1 << v for v in a), sum(1 << v for v in b)
    totals = {sum((states[t][v] & bm).bit_count() for v in a) for t in ids}
    assert len(totals) == 1
    if totals == {2}:
        dr = np.array([(states[t][a[0]] & bm).bit_count() != 1 for t in ids], dtype=float)
        dc = np.array([(states[t][b[0]] & am).bit_count() != 1 for t in ids], dtype=float)
        pr, pc = dr.mean(), dc.mean()
        if pr > TOL and pc > TOL:
            assert pr + pc < 1 - TOL
            u = (dc - pc) / np.sqrt(len(ids) * pc * (1 - pc))
            v = (dr - pr) / np.sqrt(len(ids) * pr * (1 - pr))
            rho = np.sqrt(pc * pr / ((1 - pc) * (1 - pr)))
            basis = np.column_stack((u, v))
            dual = np.linalg.solve(basis.T @ basis, basis.T)
            form = np.array([[0, rho * (1 - rho**2)], [rho * (1 - rho**2), 0]])
            phi = dual.T @ form @ dual
    return pj, phi


def check(d):
    states = realizations(d)
    m, n = len(states), len(d)
    index = {g: t for t, g in enumerate(states)}
    pairs = list(combinations(range(n), 2))
    data = {a: pair_data(states, a) for a in pairs}
    h = {a: np.eye(m) - data[a][0] for a in pairs}
    H, L = sum(h.values()), switch_laplacian(states, n).toarray()
    zero = np.zeros((m, m))
    D, G, R, W, B, C, CW = [zero.copy() for _ in range(7)]
    largest_error, noncommuting = 0., 0
    for a, b in combinations(pairs, 2):
        if set(a) & set(b):
            continue
        interaction = h[a] @ h[b] + h[b] @ h[a]
        noncommuting += np.linalg.norm(h[a] @ h[b] - h[b] @ h[a]) > TOL
        D += interaction
        g = cross_projection(states, a, b, index)
        ra, wa = error_projection(states, a, b, data[a][1])
        rb, wb = error_projection(states, b, a, data[b][1])
        pj, phi = zero.copy(), zero.copy()
        for ids in cells(states, a, b):
            pblock, fblock = cell_terms(states, ids, a, b, data[a][0], data[b][0])
            pj[np.ix_(ids, ids)] = pblock
            phi[np.ix_(ids, ids)] = fblock
        largest_error = max(largest_error, np.max(np.abs(interaction - 2 * pj - phi)))
        for term in (pj - g, phi + ra + rb, phi + wa + wb):
            assert np.linalg.eigvalsh(term)[0] >= -TOL, (d, a, b, "cell PSD")
        G += 2 * g
        R += ra + rb
        W += wa + wb
        B += 2 * (pj - g)
        C += phi + ra + rb
        CW += phi + wa + wb
    A, AW = G - R - H, G - W - H
    for x, y in ((G, L), (D - H, A + B + C), (D - H, AW + B + CW)):
        largest_error = max(largest_error, np.max(np.abs(x - y)))
    assert largest_error < TOL, (d, "identity", largest_error)
    for term in (B, C, AW, CW, D - H):
        assert np.linalg.eigvalsh(term)[0] >= -TOL, (d, "global PSD")
    types = sorted({(N, q) for _, blocks in data.values() for ids, _, N, q, _ in blocks
                    if len(ids) > 1})
    print(f"d={d}, M={m}, fibers={types}, noncommuting pairs={noncommuting}, "
          f"identity error={largest_error:.2e}")
    for label, term in (("G-S-H", A), ("2(P_J-g)", B), ("Phi+R+R'", C),
                        ("G-pS-H", AW), ("Phi+pR+p'R'", CW), ("D-H", D - H)):
        print(f"  {label:14s} norm={np.linalg.norm(term):.9f}, "
              f"least={np.linalg.eigvalsh(term)[0]:.9f}")


def main():
    start = perf_counter()
    for degree in ((2, 2, 1, 1), (2, 2, 2, 2), (4, 3, 3, 3, 3),
                   (3, 2, 2, 2, 1), (3, 3, 2, 2, 1, 1), (2, 2, 2, 2, 2),
                   (6, 6, 4, 4, 3, 3, 1, 1)):
        check(degree)
    print(f"PASS finite slack checks; wall {perf_counter() - start:.2f}s")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as error:
        print(f"FAIL: {error}")
        raise SystemExit(1)
