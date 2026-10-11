"""Exact, standard-library checks on two tiny switch-chain state spaces.

Run from the repository root: python scripts/check.py
Exit 0 and PASS certify the assertions for these instances, not the universal theorem.
"""

from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb
from time import perf_counter, process_time


def zero(m):
    return [[F(0) for _ in range(m)] for _ in range(m)]


def identity(m):
    return [[F(i == j) for j in range(m)] for i in range(m)]


def add(a, b, scale=1):
    return [[x + scale * y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def multiply(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def psd_certificate(a):
    """Construct and verify A = B diag(pivots) B^T over Q, pivots >= 0."""
    m = len(a)
    assert a == [list(col) for col in zip(*a)]
    b, pivots = identity(m), []
    for j in range(m):
        p = a[j][j] - sum(b[j][k] ** 2 * pivots[k] for k in range(j))
        assert p >= 0, ("negative LDL pivot", j, p)
        pivots.append(p)
        for i in range(j + 1, m):
            r = a[i][j] - sum(b[i][k] * b[j][k] * pivots[k] for k in range(j))
            if p:
                b[i][j] = r / p
            else:
                assert r == 0, ("nonzero column at zero pivot", j, i, r)
    assert all(
        a[i][j] == sum(b[i][k] * pivots[k] * b[j][k] for k in range(m))
        for i in range(m) for j in range(m)
    )
    return pivots


def edge(u, v):
    return tuple(sorted((u, v)))


def matchings(vertices):
    a, b, c, d = vertices
    return [frozenset((edge(a, b), edge(c, d))),
            frozenset((edge(a, c), edge(b, d))),
            frozenset((edge(a, d), edge(b, c)))]


def check(n, degree, expected_states):
    vertices = range(n)
    edges = tuple(combinations(vertices, 2))
    states = [frozenset(g) for g in combinations(edges, n * degree // 2)
              if all(sum(v in e for e in g) == degree for v in vertices)]
    m = len(states)
    assert m == expected_states
    index = {g: i for i, g in enumerate(states)}
    unit, laplacian, heat, swap_sum = identity(m), zero(m), zero(m), zero(m)

    # L: existing disjoint edge pairs, collecting distinct neighbors only.
    neighbors = []
    for i, g in enumerate(states):
        adjacent = set()
        for removed in combinations(sorted(g), 2):
            four = sorted(set(removed[0]) | set(removed[1]))
            if len(four) != 4:
                continue
            for inserted in matchings(four):
                if not (inserted & g):
                    adjacent.add(index[(g - set(removed)) | inserted])
        neighbors.append(adjacent)
        laplacian[i][i] = F(len(adjacent))
        for j in adjacent:
            laplacian[i][j] = F(-1)
    reached, pending = {0}, [0]
    while pending:
        new = neighbors[pending.pop()] - reached
        reached.update(new)
        pending.extend(new)
    assert len(reached) == m

    # Fibers: group by all three items of setup.tex, then average uniformly.
    fiber_types = Counter()
    for a, b in combinations(vertices, 2):
        outside = [w for w in vertices if w not in (a, b)]
        fibers = defaultdict(list)
        local_swap = zero(m)
        for i, g in enumerate(states):
            signature = (tuple(e for e in sorted(g) if a not in e and b not in e),
                         edge(a, b) in g,
                         tuple(int(edge(a, w) in g) + int(edge(b, w) in g)
                               for w in outside))
            fibers[signature].append(i)
            singles = [w for w in outside if (edge(a, w) in g) != (edge(b, w) in g)]
            for u, v in combinations(singles, 2):
                if (edge(a, u) in g) != (edge(a, v) in g):
                    toggled = {edge(a, u), edge(b, u), edge(a, v), edge(b, v)}
                    j = index[g ^ toggled]
                    local_swap[i][i] += 1
                    local_swap[i][j] -= 1
        expectation = zero(m)
        for ids in fibers.values():
            g = states[ids[0]]
            singles = [w for w in outside if (edge(a, w) in g) != (edge(b, w) in g)]
            q = sum(edge(a, w) in g for w in singles)
            size = len(singles)
            fiber_types[(size, q, len(ids))] += 1
            assignments = {frozenset(w for w in singles if edge(a, w) in states[i])
                           for i in ids}
            assert assignments == {frozenset(s) for s in combinations(singles, q)}
            assert len(ids) == comb(size, q)
            for i in ids:
                for j in ids:
                    expectation[i][j] = F(1, len(ids))
            block = [[local_swap[i][j] for j in ids] for i in ids]
            defect = add(identity(len(ids)), [[F(1, len(ids))] * len(ids)
                                               for _ in ids], -1)
            if len(ids) == 1:
                assert block == defect == [[0]]
            else:
                assert size >= 2
                psd_certificate(add(block, defect, -size))  # J >= N h
        assert multiply(expectation, expectation) == expectation
        heat = add(heat, add(unit, expectation, -1))
        swap_sum = add(swap_sum, local_swap)
    assert swap_sum == add(laplacian, laplacian)

    # P: enumerate all six ordered proposals for each four-set, including rejections.
    denominator = 12 * comb(n, 4)
    proposals = [p for four in combinations(vertices, 4)
                 for p in permutations(matchings(four), 2)]
    assert len(proposals) == 6 * comb(n, 4)
    kernel = zero(m)
    for i, g in enumerate(states):
        kernel[i][i] = F(1, 2)
        for removed, inserted in proposals:
            target = (g - removed) | inserted if removed <= g and not inserted & g else g
            kernel[i][index[target]] += F(1, denominator)
    assert kernel == [list(col) for col in zip(*kernel)]
    assert all(sum(row) == 1 and all(x >= 0 for x in row) for row in kernel)
    assert all(kernel[i][i] >= F(1, 2) for i in range(m))
    assert add(unit, kernel, -1) == [[x / denominator for x in row] for row in laplacian]
    assert {kernel[i][j] for i in range(m) for j in neighbors[i]} == {F(1, denominator)}
    assert heat == laplacian  # An instance-specific equality, not a general claim.

    centered_identity = add(unit, [[F(1, m)] * m for _ in range(m)], -1)
    certificates = {
        "H^2-H": psd_certificate(add(multiply(heat, heat), heat, -1)),
        "H-(I-Pi)": psd_certificate(add(heat, centered_identity, -1)),
        "L-H": psd_certificate(add(laplacian, heat, -1)),
    }
    print(f"n={n}, d={degree}^{n}: states={m}, switch_edges={sum(map(len, neighbors)) // 2}")
    print(f"  fibers (N,q,size): {dict(sorted(fiber_types.items()))}")
    print(f"  off_diagonal={F(1, denominator)}, min_holding={min(kernel[i][i] for i in range(m))}")
    print("  sum J=2L; H=L; I-P=L/(12 choose(n,4)); connected: exact")
    for label, pivots in certificates.items():
        print(f"  {label}: LDL rank={sum(p > 0 for p in pivots)}, D="
              + ",".join(map(str, pivots)))


if __name__ == "__main__":
    cpu, wall = process_time(), perf_counter()
    check(5, 2, 12)
    check(6, 1, 15)
    print(f"PASS; CPU={process_time() - cpu:.3f}s; wall={perf_counter() - wall:.3f}s")
