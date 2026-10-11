# Finite checks

Exact and floating-point checks of the operator inequalities in the paper on small degree
sequences. They are evidence that supports the proofs, not part of them; the paper and the
Lean verification stand without them. Run every command from the repository root. Each script
prints `PASS` and exits 0 when its stated checks hold, and exits nonzero otherwise.

Recorded runs: Python 3.13.2, NumPy 2.1.3, SciPy 1.15.1 on Windows, wall times. `check.py` and
`local.py` use only the standard library and exact rational arithmetic; the others use numpy
and scipy with tolerance 1e-9.

| Script | Checks | Recorded run |
|---|---|---|
| `check.py` | Exact normalization identities and positive semidefiniteness on 12- and 15-state spaces, including the proposal normalization I − P = L/(12·C(n,4)). | 0.12 s |
| `sweep.py [NMAX]` | For every degree class through n = NMAX (default 8; 732 classes, up to 19,355 states): gap(L) ≥ 2, gap(H) ≥ 2 and H ⪯ L. | 41.9 s |
| `disjoint.py [NMAX] [MAXSTATES]` | The expansion H² = Σ_T H_T² − (n−3)H + D and the inequalities D ⪰ H, D ⪰ 2(I−Π), Σ_T(H_T² − H_T) ⪰ 0, H² ⪰ 2H on 693 classes through n = 8 with at most 2,000 states. With `9 5000 --nmin 9 --workers 4`: 1,723 classes at n = 9. | 30.3 s; 372.2 s |
| `local.py` | Exact rational LDLᵀ certificates for the weighted slice inequality: 16 full cells, 25 full slices, 104,976 compressed planes, and 32,639 exact slice spectral parameters through N = 256. | 7.30 s |
| `slack.py` | Weighted and unweighted decompositions on seven spaces, agreeing to 1e-14; shows the unweighted slice remainder fails (least eigenvalue −3 on (3,2,2,2,1)). | 0.07 s |
| `triples.py --workers 4` | The three-row and graph-triple inputs of Appendix A: 1,225 fixed-block size vectors and 4,459 count parameters by exact certificates, and 39,233 graph triples with 1,186,851 cells in 819 classes through n = 8. | 38.52 s |
| `search.py` | 223,744 threshold-perturbation seeds at n = 9 to 12 looking for small gaps; all 1,112 classes with a one-neighbor seed have two states. | 22.1 s |

`disjoint.py`, `slack.py`, `triples.py` and `search.py` import helpers from `sweep.py` and
`check.py`, so keep the directory together. Thread counts for BLAS are pinned inside the
scripts; use `--workers` to limit parallel memory.
