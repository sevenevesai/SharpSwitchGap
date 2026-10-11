"""Finite falsification search: one-edge perturbations of all threshold creation words.

Run from the root: python scripts/search.py
For n=9..12, test every such labeled seed for a unique switch neighbor; count its
realizations with cap 2 (three states would refute gap(L)>=2 by an indicator test).
For every distinct seed degree sequence with 2..128 states, also test L and H.
This deterministic family is not an exhaustive search of graphs or degree sequences.
PASS and exit 0 mean no counterexample within the stated finite search.
"""

import os

for var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(var, "1")

import argparse
from itertools import combinations
from multiprocessing import Pool
from time import perf_counter

import numpy as np

from disjoint import least_centered
from sweep import heat_bath, realizations, switch_laplacian


def switch_neighbors(g, limit=2):
    """Distinct neighbors, stopping at limit; each switch has two pair encodings."""
    n, found = len(g), set()
    for i, j in combinations(range(n), 2):
        ab = (1 << i) | (1 << j)
        one = (g[i] ^ g[j]) & ~ab
        left, right = one & g[i], one & g[j]
        while left:
            ub = left & -left
            left -= ub
            targets = right
            while targets:
                vb = targets & -targets
                targets -= vb
                u, v = ub.bit_length() - 1, vb.bit_length() - 1
                h = list(g)
                h[i] ^= ub | vb
                h[j] ^= ub | vb
                h[u] ^= ab
                h[v] ^= ab
                found.add(tuple(h))
                if len(found) >= limit:
                    return found
    return found


def seeds(n):
    for word in range(1 << (n - 1)):
        g = [0] * n
        for v in range(1, n):
            if word >> (v - 1) & 1:
                for u in range(v):
                    g[v] |= 1 << u
                    g[u] |= 1 << v
        for u, v in combinations(range(n), 2):
            h = g.copy()
            h[u] ^= 1 << v
            h[v] ^= 1 << u
            yield tuple(h)


def canonical_degree(g):
    d = tuple(sorted((row.bit_count() for row in g), reverse=True))
    dc = tuple(sorted((len(g) - 1 - x for x in d), reverse=True))
    return min(d, dc)


def search_seeds(n):
    degrees, leaves, counts = set(), set(), 0
    for g in seeds(n):
        counts += 1
        d = canonical_degree(g)
        degrees.add(d)
        if len(switch_neighbors(g)) == 1:
            leaves.add(d)
    for d in sorted(leaves):
        states = realizations(d, cap=2)
        # Exact obstruction: a leaf in M>=3 has centered Rayleigh quotient M/(M-1)<2.
        assert len(states) == 2, ("FAIL exact leaf obstruction", d, states)
    return n, counts, len(leaves), sorted(degrees)


def small_space(arg):
    d, cap = arg
    states = realizations(d, cap=cap)
    if not 2 <= len(states) <= cap:
        return None
    L, H = switch_laplacian(states, len(d)), heat_bath(states, len(d))
    gl, gh = least_centered(L), least_centered(H)
    assert gl >= 2 - 1e-9 and gh >= 2 - 1e-9, ("FAIL numerical candidate", d, gl, gh)
    return len(d), len(states), gl, gh, int(np.min(L.diagonal()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cap", type=int, default=128)
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    start = perf_counter()
    with Pool(args.workers) as pool:
        families = pool.map(search_seeds, range(9, 13))
        todo = [(d, args.cap) for _, _, _, degrees in families for d in degrees]
        rows = [r for r in pool.imap_unordered(small_space, todo, chunksize=8) if r]
    for n, tested, leaves, degrees in families:
        sub = [r for r in rows if r[0] == n]
        assert sub
        print(f"n={n}: {tested} seeds (with multiplicity); {len(degrees)} sequences; "
              f"{leaves} leaf sequences, all M=2; {len(sub)} spaces with M<= {args.cap}; "
              f"min gaps L={min(r[2] for r in sub):.9f}, H={min(r[3] for r in sub):.9f}; "
              f"min switch degree for M>=3: {min(r[4] for r in sub if r[1]>=3)}")
    print(f"PASS finite search; wall {perf_counter() - start:.1f}s")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as error:
        print(f"FAIL: {error}")
        raise SystemExit(1)
