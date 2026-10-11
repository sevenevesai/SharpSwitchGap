# Lean verification

Mathlib-only Lean 4 project that kernel-checks the sharp switch gap, the Curveball gap, and a
switch total-variation bound against the pinned definitions of openai-math#131. The paper's
Section 8 maps each intermediate result to the declaration that checks it; this file records
the layout, the reproduction commands, the recorded runs, and what is not formalized.

## Layout

```
lean-toolchain          leanprover/lean4:v4.34.1
lakefile.lean           package sharpSwitchGap; lean_lib OAI (srcDir vendor); lean_lib SharpSwitchGap
lake-manifest.json      Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and its dependencies
SharpSwitchGap.lean     root module importing the check files below
SharpSwitchGap/         this project's proofs (MIT)
  Statement.lean        the two switch contracts, importing only the pinned Definitions
  Main.lean             switch_chain_gap and switch_chain_tv_bound
  Baseline.lean         checks the verbatim Comparator types and the two contracts
  Curveball.lean        the uniform-pair Curveball kernel on the pinned graph space and its gap
  B1Checks ... B5Checks axiom audits for each milestone; PartialChecks audits intermediate lemmas
vendor/                 177 upstream files at the pin plus LICENSE (Apache-2.0) and MANIFEST.txt
verify_vendor.py        checks vendor/ against the manifest, the import closure, and the Comparator
check_fresh.sh, .ps1    delete this project's own artifacts, rebuild, and audit one check file
evidence/               recorded audit output
```

## What is checked

- `SharpSwitchGap.switch_chain_gap`: for `4 ≤ n`, degrees at most `n−1`, `Graphical n d` and
  `1 < stateCount n d`, the pinned predicate `hasSpectralGapAtLeast n d (1/(6·C(n,4)))` holds
  for the pinned `switchKernel`. The predicate is the Poincaré form (γ times the uniform
  variance is at most the Dirichlet energy), which equals 1 − λ₂ for this reversible kernel.
- `SharpSwitchGap.switch_chain_tv_bound`: the pinned `tvDistanceFrom` is at most
  `√M/2 · exp(−t/(6·C(n,4)))` from every starting graph, reusing upstream's gap-to-TV proof.
- `SharpSwitchGap.Baseline.sharp_gap` and `sharp_tv_bound`: the two contracts of
  `Statement.lean`, which imports only the pinned `Definitions`, are discharged by the proofs.
- `SharpSwitchGap.Curveball.gap`: the kernel `Curveball.kernel`, defined here on the pinned
  graph space from the pinned `fiberStates`, has uniform-variance gap `2/C(n,2)` for `n ≥ 4`.
  `kernel_apply` and `operator_average` identify it with `I − H/C(n,2)`; `kernel_nonneg`,
  `kernel_row_sum`, `kernel_symm` and `operator_nonneg` give stochasticity, symmetry and
  positive semidefiniteness. These definitions are new in this project, so their trusted base
  is larger than for the switch contracts, which reuse upstream definitions unchanged.
- Intermediate steps audited by `B1Checks` to `B3Checks`: the Johnson centered Poincaré bound
  and `H ≤ L` (`Johnson.centered_poincare`, `SharpComparison.generator_le_laplacian`), the
  weighted cell inequality on actual graph states (`WeightedCell.cell_bound`,
  `WeightedCell.actual_named_interaction`), the weighted slice inequality
  (`WeightedSlice.weighted_centered`), and the assembly `D ≥ H`, `H² ≥ 2H` and the centered
  gap two (`SharpAssembly.disjoint_ge_generator`, `generator_square`, `centered_poincare`).
- The three upstream Comparator endpoints (`OAI.Problem315.switch_chain_main`,
  `switch_chain_tv_bound`, `switch_connectivity`) also build and audit clean; `Baseline.lean`
  checks their verbatim types.

## Reproduce

Install [elan](https://github.com/leanprover/elan); it reads `lean-toolchain`. Then, from this
directory:

```
python verify_vendor.py
lake exe cache get
lake build
lake env lean SharpSwitchGap/B5Checks.lean
lake env lean SharpSwitchGap/B4Checks.lean
```

Success: every command exits 0 with no `sorry` diagnostic, and the nine prints of `B5Checks`
and four of `B4Checks` each end with `depends on axioms: [propext, Classical.choice,
Quot.sound]`. `./check_fresh.sh` (or `.\check_fresh.ps1` in PowerShell, both taking an optional
check file) removes only `SharpSwitchGap*` artifacts under `.lake/build`, rebuilds, and audits.
Set `LEAN_NUM_THREADS` to limit parallelism; `MATHLIB_CACHE_DIR` relocates the Mathlib cache.

## Recorded runs

- 2026-10-07: milestones B1 to B5 built fresh in 104 s to 298 s each after the upstream modules
  (`lake build OAI.Probability.SwitchChain.Main`, 745 s); every audit printed only the three
  axioms. The first Mathlib cache fetch took 189 s.
- 2026-10-11: `verify` sync exit 0; `check_fresh.ps1 -Audit SharpSwitchGap/B5Checks.lean`
  fresh `lake build` 625.86 s and audit 19.97 s, both exit 0; `B4Checks` exit 0; all 13 prints
  the three axioms, no `sorry`. Output: `evidence/audit-2026-10-11.txt`.
- 2026-10-11, this repository from scratch: `lake exe cache get` exit 0; `lake build` exit 0
  after 946 s with four threads (upstream modules and this project); `B5Checks` and `B4Checks`
  exit 0 with all 13 prints the three axioms. Output: `evidence/build-2026-10-11.txt`.

## Not formalized

- The equality cases of the paper's Section 7, including `(2,2,1,1,0,…,0)`, and the exact
  Johnson gap equality; the lower bounds do not need them.
- The `√(M−1)/2` prefactor of the paper's total-variation estimate; the checked contract uses
  `√M/2` with the same gap constant.
- The Curveball total-variation estimate and the mixing-time corollaries.
- The three-row and graph-triple inputs of Appendix A are taken from the pinned upstream
  formalization (`TripleActualRowBound.triple_square` through `ActualTripleSquare`), not
  re-proved here.

## Vendored upstream files

`vendor/` holds the import closure of `OAI.Probability.SwitchChain.Main` plus the modules this
project imports directly, copied as exact Git blobs from
[openai/math](https://github.com/openai/math) at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
together with the upstream `LICENSE` (Apache-2.0) and `ComparatorChallenges/SwitchChain.lean`,
the upstream challenge statement whose definitions `Statement.lean` reuses. The challenge file's
placeholder proofs are never imported. `MANIFEST.txt` lists each file's blob hash;
`verify_vendor.py` checks the hashes offline, re-downloads them with `--fetch`, or compares them
with `--checkout DIR` against a local clone. Their only external import is `Mathlib`.

## Notes for maintainers

- When a Gram-matrix application times out at `whnf`, pass the two factors and the vector
  argument explicitly; this fixed the slice range proof at the default heartbeat limit.
- When transporting a final inner product, rewrite `real_inner_comm` explicitly rather than
  adding it to a broad `simpa` set, which expanded graph projections and timed out.
- `autoImplicit` is off and the toolchain is fixed in `lakefile.lean`; do not bump Mathlib
  without re-running every audit.
