"""Independent finite audit of rows.tex and triples.tex; see triples.md.

Run from the repository root with --part fixed, counts, rows, graphs, or all.
Defaults cover all requested ranges, modulo explicitly checked relabelings:
fixed blocks exact |U|,|W|<=4, float <=6; counts m<=12, alpha_i<=6;
full matrices exact <=6 columns, float <=9; graphs n<=8, M<=2000.
Exact certificates use Fraction LDL^T with reconstruction, never float pivots.
Floating checks act on the full state space, with tolerance 1e-9.
No output files are written. PASS/exit 0 concerns finite checks, not the proof.
"""

import argparse
import os

for var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(var, "1")

from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from math import factorial, gcd, lcm
from multiprocessing import Pool
from time import perf_counter

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import LinearOperator, eigsh

from sweep import erdos_gallai, fibers, realizations

TOL = 1e-9


def compositions(n):
    return [(a, b, n - a - b) for a in range(n + 1) for b in range(n - a + 1)]


def certificate(matrix):
    """Schur LDL elimination, then independent entrywise reconstruction."""
    n = len(matrix)
    assert all(len(row) == n for row in matrix)
    assert all(matrix[i][j] == matrix[j][i] for i in range(n) for j in range(i))
    schur = [[F(x) for x in row] for row in matrix]
    lower = [[F(i == j) for j in range(n)] for i in range(n)]
    diagonal = []
    for k in range(n):
        pivot = schur[k][k]
        assert pivot >= 0, ("negative LDL pivot", k, pivot)
        diagonal.append(pivot)
        if not pivot:
            assert all(schur[i][k] == 0 for i in range(k + 1, n)), ("zero pivot", k)
            continue
        for i in range(k + 1, n):
            lower[i][k] = schur[i][k] / pivot
        for i in range(k + 1, n):
            if lower[i][k]:
                for j in range(k + 1, i + 1):
                    schur[i][j] -= lower[i][k] * schur[j][k]
    active = [k for k, p in enumerate(diagonal) if p]
    for i in range(n):
        for j in range(i + 1):
            reconstructed = sum(lower[i][k] * diagonal[k] * lower[j][k]
                                for k in active if k <= j)
            assert reconstructed == matrix[i][j], ("LDL reconstruction", i, j)
    return sum(p > 0 for p in diagonal)


def row_groups(states):
    out = [defaultdict(list) for _ in range(3)]
    for s, state in enumerate(states):
        for i in range(3):
            out[i][state[i]].append(s)
    return out


def projection_sum(states):
    n = len(states)
    matrix = [[F(0) for _ in states] for _ in states]
    for groups in row_groups(states):
        for ids in groups.values():
            p = F(1, len(ids))
            for i in ids:
                for j in ids:
                    matrix[i][j] += p
    assert all(sum(row) == 3 for row in matrix)
    return matrix


def exact_rows(states, square=False):
    n = len(states)
    p = projection_sum(states)
    q = [[F(2 * (i == j)) - p[i][j] + F(1, n) for j in range(n)]
         for i in range(n)]
    certificate(q)  # Direct full-state 2I - sum P_i + Pi.
    if square:
        # H=3I-P, so H^2-H=6I-5P+P^2. No commutation assumption.
        slack = [[F(6 * (i == j)) - 5 * p[i][j]
                  + sum(p[i][k] * p[k][j] for k in range(n))
                  for j in range(n)] for i in range(n)]
        certificate(slack)


def float_rows(states):
    n = len(states)
    rows, cols, vals, col = [], [], [], 0
    for groups in row_groups(states):
        for ids in groups.values():
            rows.extend(ids)
            cols.extend([col] * len(ids))
            vals.extend([len(ids) ** -0.5] * len(ids))
            col += 1
    incidence = sp.csr_matrix((vals, (rows, cols)), shape=(n, col))

    def act(v):
        return 2 * v - incidence @ (incidence.T @ v) + np.mean(v)

    if n <= 100:
        q = 2 * np.eye(n) - (incidence @ incidence.T).toarray() + 1 / n
        values, vectors = np.linalg.eigh(q)
        value, vector = values[0], vectors[:, 0]
    else:
        op = LinearOperator((n, n), matvec=act, dtype=float)
        values, vectors = eigsh(op, k=1, which="SA", tol=1e-12,
                               v0=np.random.default_rng(131).normal(size=n))
        value, vector = values[0], vectors[:, 0]
    residual = np.linalg.norm(act(vector) - value * vector)
    assert residual < 1e-8, ("eigenpair residual", residual)
    assert value >= -TOL, ("floating projection bound", value)
    return float(value)


@lru_cache(None)
def partitions(sizes):
    n = sum(sizes)
    full = (1 << n) - 1
    out = []
    for a in combinations(range(n), sizes[0]):
        am = sum(1 << x for x in a)
        for b in combinations([x for x in range(n) if not am >> x & 1], sizes[1]):
            bm = sum(1 << x for x in b)
            out.append((am, bm, full ^ am ^ bm))
    return tuple(out)


def fixed_states(spec):
    us, ws = zip(*spec)
    return [tuple(zip(u, w)) for u, w in product(partitions(us), partitions(ws))]


def transposition_audit(states, u, w):
    index = {state: s for s, state in enumerate(states)}
    adjacency = [set() for _ in states]
    for side, size in enumerate((u, w)):
        for a, b in combinations(range(size), 2):
            mask = (1 << a) | (1 << b)
            row_maps = [{} for _ in range(3)]
            for s, state in enumerate(states):
                swapped = []
                for i, pair in enumerate(state):
                    bits = pair[side]
                    newbits = bits ^ mask if (bits >> a & 1) != (bits >> b & 1) else bits
                    value = (newbits, pair[1]) if side == 0 else (pair[0], newbits)
                    assert row_maps[i].setdefault(pair, value) == value
                    swapped.append(value)
                swapped = tuple(swapped)
                assert sum(x != y for x, y in zip(state, swapped)) <= 2
                adjacency[s].add(index[swapped])
    # A connected transposition graph certifies that J has only constant kernel.
    seen, stack = {0}, [0]
    while stack:
        for t in adjacency[stack.pop()]:
            if t not in seen:
                seen.add(t)
                stack.append(t)
    assert len(seen) == len(states)


def fixed_worker(arg):
    spec, exact = arg
    states = fixed_states(spec)
    if exact:
        transposition_audit(states, sum(p[0] for p in spec), sum(p[1] for p in spec))
        exact_rows(states)
        return len(states), 0.0
    return len(states), float_rows(states)


def fixed_specs(bound):
    all_sizes = [c for n in range(bound + 1) for c in compositions(n)]
    specs = set()
    for u, w in product(all_sizes, repeat=2):
        specs.add(min(tuple(sorted(zip(u, w))), tuple(sorted(zip(w, u)))))
    return sorted(specs), len(all_sizes) ** 2


def run_fixed(args, pool):
    for bound, exact in ((args.fixed_exact, True), (args.fixed_float, False)):
        specs, covered = fixed_specs(bound)
        results = list(pool.imap(fixed_worker, [(s, exact) for s in specs]))
        print(f"fixed {'exact LDL' if exact else 'float'}: |U|,|W|<= {bound}; "
              f"{covered} size vectors, {len(specs)} relabeling classes, "
              f"max states {max(m for m, _ in results)}, "
              f"least {min(v for _, v in results):.3g}", flush=True)


def weights(total, alpha):
    raw = [F(1, np_prod(factorial(x) * factorial(x + a)
                        for x, a in zip(state, alpha))) for state in compositions(total)]
    denominator = lcm(*(p.denominator for p in raw))
    values = [p.numerator * (denominator // p.denominator) for p in raw]
    common = gcd(*values)
    return [v // common for v in values]


def np_prod(items):
    out = 1
    for x in items:
        out *= x
    return out


def coupling_audit(bound, alpha_bound):
    count, intervals = 0, 0
    for a, b in product(range(alpha_bound + 1), repeat=2):
        for s in range(1, bound + 1):
            laws = []
            for total in (s - 1, s):
                p = [F(1, factorial(y) * factorial(y + a) * factorial(total - y)
                       * factorial(total - y + b)) for y in range(total + 1)]
                norm = sum(p)
                laws.append([x / norm for x in p])
            old, new = laws
            ratios = [new[y] / old[y] for y in range(s)]
            assert all(x <= y for x, y in zip(ratios, ratios[1:]))
            assert all(ratios[y] * (s - y) * (s - y + b) == ratios[0] * s * (s + b)
                       for y in range(s))
            # The quantile joint law: overlap of the exact cumulative intervals.
            cdfs = []
            for law in laws:
                cdf = [F(0)]
                for p in law:
                    cdf.append(cdf[-1] + p)
                assert cdf[-1] == 1
                cdfs.append(cdf)
            joint = [[max(F(0), min(cdfs[0][y + 1], cdfs[1][z + 1])
                          - max(cdfs[0][y], cdfs[1][z])) for z in range(s + 1)]
                     for y in range(s)]
            assert [sum(row) for row in joint] == old
            assert [sum(col) for col in zip(*joint)] == new
            for y in range(s):
                for z in range(s + 1):
                    if joint[y][z]:
                        assert y <= z <= y + 1
                        assert (z - y) + ((s - z) - (s - 1 - y)) == 1
                        intervals += 1
            count += 1
    return count, intervals


def counts_worker(arg):
    total, alpha = arg
    states, mass = compositions(total), weights(total, alpha)
    norm = sum(mass)
    # Omit the last indicator of each marginal; their centered versions span.
    features = [(i, t) for i in range(3) for t in range(total)]
    marginal = [[sum(w for x, w in zip(states, mass) if x[i] == t)
                 for t in range(total + 1)] for i in range(3)]
    assert all(w > 0 for row in marginal for w in row)
    joint = Counter()
    for state, w in zip(states, mass):
        for i, j in product(range(3), repeat=2):
            joint[i, state[i], j, state[j]] += w
    matrix = []
    for i, t in features:
        row = []
        for j, v in features:
            cov = norm * joint[i, t, j, v] - marginal[i][t] * marginal[j][v]
            row.append(cov if i == j else -cov)
        matrix.append(row)
    # This is norm^2 times 2 diag(Cov_i) - Cov(sum), a congruence certificate
    # for 2I-A* A on the centered direct sum, including all possible b_i.
    certificate(matrix)
    # Check the adjoint/conditional equation on every marginal indicator.
    for i, t in product(range(3), range(total + 1)):
        for j in range(3):
            assert sum(joint[i, t, j, v] for v in range(total + 1)) == marginal[i][t]
            if i == j:
                assert joint[i, t, j, t] == marginal[i][t]
    return len(states), len(matrix)


def run_counts(args, pool):
    coupled, intervals = coupling_audit(args.count_m, args.count_alpha)
    specs = [(m, alpha) for m in range(args.count_m + 1)
             for alpha in combinations_with_replacement(range(args.count_alpha + 1), 3)]
    results = list(pool.imap(counts_worker, specs))
    print(f"counts exact: m<= {args.count_m}, 0<=alpha_i<= {args.count_alpha}; "
          f"{(args.count_m + 1) * (args.count_alpha + 1)**3} parameters, "
          f"{len(specs)} up to coordinate permutation; {coupled} quantile couplings, "
          f"{intervals} positive joint atoms; max states {max(x for x, _ in results)}, "
          f"max LDL dimension {max(x for _, x in results)}", flush=True)


@lru_cache(None)
def matrix_spaces(u, w):
    """Enumerate column bit patterns, without using a partition/count formula."""
    spaces = defaultdict(list)
    for columns in product(*([(1, 2, 4)] * u + [(3, 5, 6)] * w)):
        rows = tuple(sum(((c >> i) & 1) << t for t, c in enumerate(columns))
                     for i in range(3))
        spaces[tuple(r.bit_count() for r in rows)].append(rows)
    return {r: tuple(states) for r, states in spaces.items()}


def canonical_margin(u, w, r):
    return min((u, w, tuple(sorted(r))),
               (w, u, tuple(sorted(u + w - x for x in r))))


def margin_specs(bound):
    specs, covered = set(), 0
    for n in range(bound + 1):
        for u in range(n + 1):
            w = n - u
            for r in matrix_spaces(u, w):
                specs.add(canonical_margin(u, w, r))
                covered += 1
    return sorted(specs), covered


def count_decomposition_audit(states, u, w, r):
    delta = tuple(x - w for x in r)
    lower = tuple(max(0, -d) for d in delta)
    total = w - sum(lower)
    alpha = tuple(abs(d) for d in delta)
    assert total >= 0
    counts = Counter()
    conditional = defaultdict(lambda: [Counter() for _ in range(3)])
    umask, wmask = (1 << u) - 1, (1 << w) - 1
    for state in states:
        ub = tuple(row & umask for row in state)
        wb = tuple(wmask ^ (row >> u) for row in state)
        assert (ub[0] | ub[1] | ub[2]) == umask
        assert (wb[0] | wb[1] | wb[2]) == wmask
        assert all(not (ub[i] & ub[j] or wb[i] & wb[j]) for i, j in combinations(range(3), 2))
        k = tuple(b.bit_count() for b in wb)
        assert all(ub[i].bit_count() == k[i] + delta[i] for i in range(3))
        counts[k] += 1
        for i in range(3):
            conditional[k][i][(ub[i], wb[i])] += 1
    shifted = [tuple(x[i] + lower[i] for i in range(3)) for x in compositions(total)]
    assert set(counts) == set(shifted)
    expected = weights(total, alpha)
    assert len(states) * sum(expected) > 0
    marginal_by_ki = {}
    for k, weight in zip(shifted, expected):
        assert counts[k] * sum(expected) == weight * len(states)
        numerator = factorial(u) * factorial(w)
        denominator = np_prod(factorial(x) * factorial(x + d) for x, d in zip(k, delta))
        assert counts[k] == numerator // denominator and numerator % denominator == 0
        for i in range(3):
            law = {pair: F(count, counts[k]) for pair, count in conditional[k][i].items()}
            assert len(set(law.values())) == 1  # Uniform marginal block tuples.
            us = {pair[0] for pair in law}
            ws = {pair[1] for pair in law}
            assert len(law) == len(us) * len(ws)  # Independent marginal subsets.
            key = i, k[i]
            assert marginal_by_ki.setdefault(key, law) == law


def rows_worker(arg):
    spec, exact = arg
    u, w, r = spec
    states = matrix_spaces(u, w)[r]
    if exact:
        count_decomposition_audit(states, u, w, r)
        exact_rows(states, square=True)
        return len(states), 0.0
    return len(states), float_rows(states)


def run_rows(args, pool):
    for bound, exact in ((args.rows_exact, True), (args.rows_float, False)):
        specs, covered = margin_specs(bound)
        results = list(pool.imap(rows_worker, [(s, exact) for s in specs]))
        print(f"rows {'exact LDL (Q and H^2-H)' if exact else 'float Q'}: <= {bound} "
              f"nonconstant columns; {covered} margins before row/complement symmetry, "
              f"{len(specs)} classes; max states {max(m for m, _ in results)}; "
              f"least {min(v for _, v in results):.3g}; all 0/3-column paddings and "
              "column permutations transport the same operators", flush=True)


def degree_vectors(n):
    for increasing in combinations_with_replacement(range(n), n):
        d = increasing[::-1]
        complement = tuple(n - 1 - x for x in increasing)
        if d > complement or sum(d) % 2 or not erdos_gallai(d):
            continue
        yield d


def encode(g, triple, outside, e):
    rows = []
    internal = []
    for i in triple:
        s = sum(g[i] >> j & 1 for j in triple)
        internal.append(s)
        row = sum(((g[i] >> w) & 1) << t for t, w in enumerate(outside))
        if e in (1, 2):
            row |= (s if e == 1 else s - 1) << len(outside)
        rows.append(row)
    return tuple(rows), tuple(internal)


def decode(rows, original, triple, outside, e):
    g = [0] * len(original)
    for i in outside:
        g[i] = sum(((original[i] >> j) & 1) << j for j in outside)
    for t, i in enumerate(triple):
        for c, j in enumerate(outside):
            if rows[t] >> c & 1:
                g[i] |= 1 << j
                g[j] |= 1 << i
    for a, b in combinations(range(3), 2):
        marks = (rows[a] >> len(outside) & 1, rows[b] >> len(outside) & 1)
        present = e == 3 or (e == 1 and all(marks)) or (e == 2 and any(marks))
        if present:
            i, j = triple[a], triple[b]
            g[i] |= 1 << j
            g[j] |= 1 << i
    return tuple(g)


def normalized_encoding(rows, column_sums):
    active = sorted((t for t, c in enumerate(column_sums) if c in (1, 2)),
                    key=lambda t: column_sums[t])
    u = sum(c == 1 for c in column_sums)
    w = sum(c == 2 for c in column_sums)
    reduced = tuple(sum(((row >> t) & 1) << j for j, t in enumerate(active)) for row in rows)
    return u, w, reduced


def graph_worker(arg):
    degree, cap = arg
    n = len(degree)
    states = realizations(degree, cap=cap)
    if len(states) > cap:
        return None
    assert states and len(set(states)) == len(states)
    actual = {pair: {tuple(ids) for ids in fibers(states, n, *pair)}
              for pair in combinations(range(n), 2)}
    signatures = set()
    cell_count, triple_count, internal_counts, free_singletons = 0, 0, [0] * 4, 0
    for triple in combinations(range(n), 3):
        outside = tuple(i for i in range(n) if i not in triple)
        outside_mask = sum(1 << i for i in outside)
        cells = defaultdict(list)
        for t, g in enumerate(states):
            key = (tuple(g[w] & outside_mask for w in outside),
                   tuple(sum(g[w] >> i & 1 for i in triple) for w in outside))
            cells[key].append(t)
        row_partitions = [set() for _ in range(3)]
        for (_, external_sums), ids in cells.items():
            e2 = sum(degree[i] for i in triple) - sum(external_sums)
            assert e2 % 2 == 0 and 0 <= e2 <= 6
            e = e2 // 2
            column_sums = external_sums + ((2 if e == 1 else 1,) if e in (1, 2) else ())
            encoded, raw_rows, internals = set(), [], []
            for t in ids:
                rows, s = encode(states[t], triple, outside, e)
                assert decode(rows, states[t], triple, outside, e) == states[t]
                assert all(sum(row >> c & 1 for row in rows) == cs
                           for c, cs in enumerate(column_sums))
                subtract = 0 if e <= 1 else e - 1
                assert tuple(row.bit_count() for row in rows) == tuple(degree[i] - subtract for i in triple)
                u, w, reduced = normalized_encoding(rows, column_sums)
                encoded.add(reduced)
                raw_rows.append(rows)
                internals.append(s)
            assert len(encoded) == len(ids)
            r = tuple(row.bit_count() for row in next(iter(encoded)))
            # Surjectivity is checked against separately enumerated whole margin spaces.
            assert encoded == set(matrix_spaces(u, w)[r]), (degree, triple, e, r)
            signatures.add(canonical_margin(u, w, r))
            for i in range(3):
                groups = defaultdict(list)
                for pos, t in enumerate(ids):
                    groups[raw_rows[pos][i]].append(t)
                row_partitions[i].update(tuple(group) for group in groups.values())
                j, k = (v for v in triple if v != triple[i])
                for group in groups.values():
                    if sum(states[group[0]][triple[i]] >> v & 1 for v in (j, k)) == 1:
                        choices = {states[t][triple[i]] >> j & 1 for t in group}
                        free_singletons += len(choices) == 2
            cell_count += 1
            internal_counts[e] += 1
        for i in range(3):
            pair = tuple(v for v in triple if v != triple[i])
            # Identical partitions under the uniform law mean identical rational matrices,
            # including diagonal entries and transitions where i is a singleton label.
            assert row_partitions[i] == actual[pair], (degree, triple, pair)
        triple_count += 1
    return (len(states), triple_count, cell_count, internal_counts, free_singletons, signatures)


def run_graphs(args, pool):
    specs = [(d, args.graph_cap) for n in range(3, args.graph_n + 1) for d in degree_vectors(n)]
    results = [r for r in pool.imap(graph_worker, specs) if r is not None]
    signatures = set().union(*(r[5] for r in results))
    # Every encountered cell receives a reconstructed exact full-matrix square certificate.
    certs = list(pool.imap(rows_worker, [(s, True) for s in sorted(signatures)]))
    print(f"graphs exact: 3<=n<= {args.graph_n}, 1<=M<= {args.graph_cap}, isolates included; "
          f"{len(results)}/{len(specs)} degree classes up to complement; "
          f"{sum(r[0] > 1 for r in results)} nontrivial; "
          f"{sum(r[1] for r in results)} separate triples; "
          f"{sum(r[2] for r in results)} cells; "
          f"e=0,1,2,3 counts {[sum(r[3][e] for r in results) for e in range(4)]}; "
          f"{sum(r[4] for r in results)} row fibers exercising both singleton choices; "
          f"{len(signatures)} transported exact square certificates, "
          f"max cell states {max(m for m, _ in certs)}, "
          f"max graph states {max(r[0] for r in results)}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", choices=("all", "fixed", "counts", "rows", "graphs"), default="all")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--fixed-exact", type=int, default=4)
    parser.add_argument("--fixed-float", type=int, default=6)
    parser.add_argument("--count-m", type=int, default=12)
    parser.add_argument("--count-alpha", type=int, default=6)
    parser.add_argument("--rows-exact", type=int, default=6)
    parser.add_argument("--rows-float", type=int, default=9)
    parser.add_argument("--graph-n", type=int, default=8)
    parser.add_argument("--graph-cap", type=int, default=2000)
    args = parser.parse_args()
    assert args.workers >= 1 and args.graph_cap >= 1 and args.graph_n >= 3
    assert all(x >= 0 for x in (args.fixed_exact, args.fixed_float, args.count_m,
                               args.count_alpha, args.rows_exact, args.rows_float))
    started = perf_counter()
    with Pool(args.workers) as pool:
        for name, run in (("fixed", run_fixed), ("counts", run_counts),
                          ("rows", run_rows), ("graphs", run_graphs)):
            if args.part in ("all", name):
                start = perf_counter()
                run(args, pool)
                print(f"PASS {name}: wall {perf_counter() - start:.2f}s", flush=True)
    print(f"PASS requested finite audit: wall {perf_counter() - started:.2f}s", flush=True)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"FAIL: {error}", flush=True)
        raise
