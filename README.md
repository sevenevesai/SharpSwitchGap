# SharpSwitchGap

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23295359.svg)](https://doi.org/10.5281/zenodo.23295359)

Sharp spectral gaps for the switch and Curveball chains on every graphical degree sequence:
the manuscript, its Lean 4 verification, and the finite numerical checks.

For every graphical degree vector *d* on *n* ≥ 4 labeled vertices with more than one
realization, the lazy chain that proposes switches uniformly on four vertices has spectral gap
at least 1/(6·C(n,4)), and the chain that performs a uniform undirected Curveball trade on a
uniformly chosen vertex pair has spectral gap at least 2/C(n,2). Both constants are the worst
case over *d* for every *n*: equality holds for every *d* with exactly two realizations.
Consequently the total-variation mixing times at distance 1/4 are at most n⁶/4 + 1 for the
switch chain and n⁴/16 + 1 for the Curveball chain.

The result sharpens the pair-resampling argument of the OpenAI Math Release manuscript
[openai-math#131](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026),
which proves polynomial mixing for every graphical degree sequence with gap bound
1/(24n²·C(n,4)) and mixing time 2n⁸. The new step is a weighted estimate on disjoint pair
resamplings; see the paper's introduction for the exact attribution.

## Key results

- Switch chain gap ≥ 1/(6·C(n,4)) and Curveball gap ≥ 2/C(n,2), best possible for every n.
- Mixing times t(1/4) ≤ n⁶/4 + 1 (switch) and n⁴/16 + 1 (Curveball).
- Both gap bounds, and a switch total-variation bound with prefactor √M/2, are kernel-checked
  in Lean 4 against the upstream manuscript's pinned definitions; the audited theorems depend
  only on `propext`, `Classical.choice` and `Quot.sound`.
- Exact rational certificates and floating-point sweeps confirm the operator inequalities on
  every degree class through n = 8 and on 1,723 classes at n = 9.

## Verification status

| Claim | Proof | Lean |
|---|---|---|
| Johnson comparison H ⪯ L | paper, Section 3 | checked |
| Weighted cell inequality | paper, Section 4 | checked |
| Weighted slice inequality | paper, Section 5 | checked |
| D ⪰ H, H² ⪰ 2H, constant kernel | paper, Section 6 | checked |
| Switch gap 1/(6·C(n,4)), Curveball gap 2/C(n,2) | paper, Theorem 1.1 | checked |
| Switch TV bound | paper, Section 6 | checked with prefactor √M/2 (paper: √(M−1)/2) |
| Equality for every d with two realizations | paper, Section 7 | not formalized |
| Mixing-time corollary, Curveball TV bound | paper, Corollary 1.2 | not formalized |
| Three-row and graph-triple inputs | paper, Appendix A | taken from the pinned upstream formalization |

The paper is a preprint and has not been peer reviewed. See the disclosure below.

## Repository layout

```
paper/        main.tex, sections/, sources/references.tex, and the built main.pdf (CC BY 4.0)
lean/         Lean 4 project: SharpSwitchGap/ (this work), vendor/ (pinned upstream files,
              Apache-2.0), verify_vendor.py, check scripts, evidence/ (recorded audit output)
scripts/      finite checks in Python (exact rational certificates and numpy/scipy sweeps)
CITATION.cff  citation metadata; .zenodo.json carries the Zenodo deposit metadata
```

## Prerequisites

- Lean: [elan](https://github.com/leanprover/elan) installs the pinned toolchain
  (`leanprover/lean4:v4.34.1`) from `lean/lean-toolchain`; Mathlib is pinned in
  `lean/lake-manifest.json` and fetched as a prebuilt cache.
- Python 3.11 or later with `numpy` and `scipy` for the sweeps (`scripts/requirements.txt`);
  `check.py` and `local.py` use only the standard library.
- A TeX engine for the paper: the PDF was built with [Tectonic](https://tectonic-typesetting.github.io)
  0.17; the sources use a plain pdfLaTeX-compatible preamble.

## Build the paper

```
cd paper
tectonic main.tex
```

Expected: `main.pdf`, 18 pages, no warnings in the log. The committed `main.pdf` is the
build of 2026-10-11.

## Verify the Lean proofs

```
cd lean
python verify_vendor.py          # vendored upstream files match the pinned commit (offline)
lake exe cache get               # prebuilt Mathlib, about 9,000 files
lake build                       # upstream modules plus this project
lake env lean SharpSwitchGap/B5Checks.lean
lake env lean SharpSwitchGap/B4Checks.lean
```

Success: every command exits 0, no `sorry` diagnostic, and each of the nine prints of
`B5Checks.lean` and four of `B4Checks.lean` reads `depends on axioms: [propext,
Classical.choice, Quot.sound]`. A from-scratch build of this repository on 2026-10-11 took
946 s with four threads after the Mathlib cache fetch; the audits take about 20 s each.
`lean/evidence/` holds the recorded output, and `lean/README.md` lists every checked
declaration and what is not formalized.

`python verify_vendor.py --fetch` additionally downloads each vendored file from GitHub at the
pinned commit and compares Git blob hashes. `check_fresh.sh` (or `check_fresh.ps1` on Windows)
deletes this project's own build artifacts and repeats the build and audit from scratch.

## Run the finite checks

```
pip install -r scripts/requirements.txt
python scripts/check.py
python scripts/sweep.py
python scripts/disjoint.py
python scripts/local.py
python scripts/slack.py
python scripts/triples.py --workers 4
python scripts/search.py
```

Each script prints `PASS` and exits 0 when its stated checks hold. `scripts/README.md`
states what each one covers and the recorded runtimes. These are finite checks that support
the proofs; the paper does not depend on them.

## Provenance and licensing

- `lean/vendor/` holds the 177 upstream Lean files that the proofs import, copied byte for byte
  from [openai/math](https://github.com/openai/math) at commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, with the upstream Apache-2.0 license and the
  Comparator challenge file whose definitions the contracts reuse. `lean/vendor/MANIFEST.txt`
  records each file's Git blob hash; `verify_vendor.py` checks it.
- Everything else written for this repository (the Lean files under `lean/SharpSwitchGap/`,
  the scripts, and the build tooling) is released under the MIT License (`LICENSE`).
- The manuscript in `paper/` is released under CC BY 4.0 (`paper/LICENSE`).

## Disclosure

The manuscript and its Lean verification were produced with AI assistance and reviewed by the
author. The upstream manuscript openai-math#131 is machine-checked but not peer reviewed. The
Lean kernel check covers the claims marked "checked" above; the remaining claims rest on the
written proofs in the paper.

## Citation

```bibtex
@misc{Short2026SharpSwitchGap,
  author       = {Mark T. Short},
  title        = {Sharp spectral gaps for the switch and {C}urveball chains on every graphical degree sequence},
  year         = {2026},
  howpublished = {Preprint, \url{https://github.com/sevenevesai/SharpSwitchGap}},
  doi          = {10.5281/zenodo.23295359}
}
```

`CITATION.cff` carries the same metadata for citation tools.
