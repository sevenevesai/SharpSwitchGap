"""Exact certificates for the weighted cell and slice inequalities in sharp.md.

Run from the root: python scripts/local.py
Uses Fraction and reconstructed LDL^T certificates (standard library only).
Full cell/slice matrices check the operator construction on selected instances;
compressed cell planes and slice eigenvalues cover the printed parameter ranges.
Finite certificates support, but do not replace, the symbolic proof.
"""

import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from time import perf_counter

from check import add, identity, multiply, psd_certificate, zero


def subsets(n, q):
    if not 0 <= q <= n:
        return []
    return [sum(1 << i for i in ids) for ids in combinations(range(n), q)]


def choose(n, q):
    return comb(n, q) if 0 <= q <= n else 0


def equality_probability(n, q):
    return F(q * (q - 1) + (n - q) * (n - q - 1), n * (n - 1)) if n >= 2 else F(0)


def expectation(groups, m):
    E = zero(m)
    for ids in groups.values():
        for i in ids:
            for j in ids:
                E[i][j] = F(1, len(ids))
    return E


def weighted_error(groups, events, eligible, m):
    W = zero(m)
    for ids in groups.values():
        if not eligible[ids[0]]:
            assert not any(eligible[t] for t in ids)
            continue
        assert all(eligible[t] for t in ids)
        p = F(sum(events[t] for t in ids), len(ids))
        z = [F(events[t]) - p for t in ids]
        norm = sum(x * x for x in z)
        if norm:
            for i, u in enumerate(ids):
                for j, v in enumerate(ids):
                    W[u][v] = p * z[i] * z[j] / norm
    return W


def full_cell(A, B, s, q0, q1):
    states = []
    for bits in range(16):
        if bits.bit_count() != s:
            continue
        r, c = (bits & 3).bit_count(), (bits & 5).bit_count()
        states.extend((bits, u, w, r, c) for u, w in
                      product(subsets(A, q0 - r), subsets(B, q1 - c)))
    m = len(states)
    if not m:
        return 0
    index = {state[:3]: t for t, state in enumerate(states)}
    X, Y = defaultdict(list), defaultdict(list)
    for t, (_, u, w, r, c) in enumerate(states):
        X[c, w].append(t)
        Y[r, u].append(t)
    ha = add(identity(m), expectation(X, m), -1)
    hb = add(identity(m), expectation(Y, m), -1)
    g = zero(m)
    for t, (bits, u, w, r, c) in enumerate(states):
        if s == 2 and r == c == 1:
            g[t][t] = F(1, 2)
            g[t][index[bits ^ 15, u, w]] = F(-1, 2)
    wa = weighted_error(X, [r != 1 for _, _, _, r, _ in states],
                        [s == 2 and c == 1 for _, _, _, _, c in states], m)
    wb = weighted_error(Y, [c != 1 for _, _, _, _, c in states],
                        [s == 2 and r == 1 for _, _, _, r, _ in states], m)
    interaction = add(multiply(ha, hb), multiply(hb, ha))
    slack = add(add(add(interaction, g, -2), wa), wb)
    pivots = psd_certificate(slack)
    print(f"  cell A={A},B={B},s={s},q0={q0},q1={q1}: M={m}, "
          f"PSD rank={sum(x > 0 for x in pivots)}")
    return m


def full_slice(n, q):
    states = subsets(n, q)
    m, index = len(states), {s: i for i, s in enumerate(states)}
    G, S = zero(m), zero(m)
    p = equality_probability(n, q)
    for i, j in combinations(range(n), 2):
        mask = (1 << i) | (1 << j)
        events = [int((s & mask).bit_count() != 1) for s in states]
        assert F(sum(events), m) == p
        # Integer centered vector; its normalization gives the same projection.
        z = [m * x - sum(events) for x in events]
        norm = sum(x * x for x in z)
        if norm:
            for a in range(m):
                for b in range(m):
                    S[a][b] += F(z[a] * z[b], norm)
        for a, state in enumerate(states):
            if not events[a]:
                G[a][a] += F(1, 2)
                G[a][index[state ^ mask]] -= F(1, 2)
    h = add(identity(m), [[F(1, m)] * m for _ in range(m)], -1)
    slack = add(add(G, S, -p), h, -1)
    pivots = psd_certificate(slack)
    assert (not any(pivots)) == (q in (0, 1, n - 1, n))
    return m


def plane_grid(bound):
    """All correlated s=2 count planes; other s are product laws symbolically."""
    count, independent = 0, 0
    for A, B in product(range(bound + 1), repeat=2):
        for q0, q1 in product(range(A + 3), range(B + 3)):
            dr = (choose(A, q0) + choose(A, q0 - 2)) * choose(B, q1 - 1)
            dc = choose(A, q0 - 1) * (choose(B, q1) + choose(B, q1 - 2))
            center = 2 * choose(A, q0 - 1) * choose(B, q1 - 1)
            total = dr + dc + center
            if not total:
                continue
            if not dr or not dc:
                independent += 1
                continue
            assert center > 0
            pr, pc, pz = F(dr, total), F(dc, total), F(center, total)
            alpha, beta = pr / (1 - pc), pc / (1 - pr)
            assert alpha == equality_probability(A + 2, q0)
            assert beta == equality_probability(B + 2, q1)
            rho2 = pr * pc / ((1 - pr) * (1 - pc))
            assert alpha * beta == rho2 < 1
            # Basis: centered, unnormalized Dc and Dr indicators.
            plane = [[beta * pc * (1 - pc) * (1 - rho2), pc * pr * (1 - rho2)],
                     [pc * pr * (1 - rho2), alpha * pr * (1 - pr) * (1 - rho2)]]
            assert plane == [[pz * beta**2, pz * alpha * beta],
                             [pz * alpha * beta, pz * alpha**2]]
            assert sum(x > 0 for x in psd_certificate(plane)) == 1
            count += 1
    print(f"  cell planes: {count} rank-one LDL certificates; {independent} independent "
          f"nonempty s=2 parameters; 0<=A,B<={bound}, all 0<=q0<=A+2, 0<=q1<=B+2")


def spectrum_grid(bound):
    count = 0
    for n in range(3, bound + 1):
        for q in range(1, n):
            r, p, M = n - q, equality_probability(n, q), comb(n, 2)
            nu1 = F((2 * q - n)**2, 2 * (n - 2))  # p*mu1
            assert F(n, 2) - nu1 - 1 == F(2 * (q - 1) * (r - 1), n - 2) >= 0
            if n >= 4:
                nu2 = (p * M - (n - 1) * nu1) / (M - n)
                assert nu2 == F(2 * (q - 1) * (r - 1), (n - 2) * (n - 3))
                assert 0 <= nu2 <= 1 and n - 1 - nu2 >= 1
            count += 1
    print(f"  slice spectra: {count} exact parameters, 3<=N<={bound}, all 1<=q<N")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-outside", type=int, default=24)
    parser.add_argument("--max-slice", type=int, default=256)
    args = parser.parse_args()
    start = perf_counter()
    specs = [(1, 1, s, 1 if s <= 2 else 2, 1 if s <= 2 else 2) for s in range(5)]
    specs += [(2, 2, 0, 1, 1), (2, 2, 4, 3, 3),
              (0, 0, 2, 1, 1), (0, 3, 2, 1, 2), (3, 0, 2, 2, 1),
              (2, 2, 2, 2, 2), (3, 3, 2, 2, 2), (1, 3, 2, 1, 1),
              (2, 1, 2, 0, 1), (2, 2, 1, 1, 1), (2, 2, 3, 2, 2)]
    for spec in specs:
        full_cell(*spec)
    slices = [(n, q) for n in range(2, 9) for q in range(1, n // 2 + 1)]
    slices += [(9, 2), (12, 1), (16, 1), (24, 1), (4, 0), (4, 4), (0, 0), (1, 0), (1, 1)]
    max_states = max(full_slice(n, q) for n, q in slices)
    print(f"  full slices: {len(slices)} rational LDL certificates, max M={max_states}")
    plane_grid(args.max_outside)
    spectrum_grid(args.max_slice)
    print(f"PASS exact finite certificates; wall {perf_counter() - start:.2f}s")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as error:
        print(f"FAIL: {error}")
        raise SystemExit(1)
