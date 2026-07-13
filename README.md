# Hamilton Cycles in the Noncrossing Partition Refinement Graph

This repository contains the manuscript and a Lean 4 formalization of its
complete classification theorem.

## Main result

For every natural number `n`, the noncrossing partition refinement graph is
Hamiltonian exactly when `n = 0`, `n = 1`, or `n` is even and `n >= 4`.
For the usual range `n >= 3`, this is equivalent to `n` being even.

Archive:

- Concept DOI: [10.5281/zenodo.21316750](https://doi.org/10.5281/zenodo.21316750)

## Contents

- `paper/gray_code_evolution.tex`: manuscript source.
- `paper/Li_Gray_Code_Evolution_2026.pdf`: public manuscript PDF.
- `paper/Anonymous_Gray_Code_Evolution_2026.pdf`: blind manuscript PDF.
- `paper/theorem-map.json`: selected paper-label to Lean-declaration navigation map.
- `scripts/verify_manuscript.py`: fail-closed public manuscript/map checker.
- `lean4/`: minimal transitive Lean source closure with semantic module names.

The formal source tree contains only modules required by the publication
entrypoints. Research logs, abandoned approaches, generated caches, and
finite-search programs are not part of this repository.

## Proof architecture

The odd case is excluded by block-count bipartiteness and an exact signed
count of noncrossing partitions. The even case uses canonical
matching/Boolean-mask coordinates, cyclic Gray codes inside each Boolean
block, a rooted tree of canonical matchings, explicit joining diamonds, and
recursive square switching. The theorem for all natural numbers is
`NCRefinementGraph_fin_isHamiltonian_iff`.

## Verification

```powershell
python scripts/verify_manuscript.py
cd lean4
lake exe cache get
lake build Hamilton.HamiltonianCycles
lake env lean Hamilton/HamiltonianCyclesTheoremMap.lean
lake env lean --trust=0 Hamilton/HamiltonianCyclesAxiomAudit.lean
python scripts/render_publication_readme.py --check
```

The expected audit output for every publication endpoint is exactly
`[propext, Classical.choice, Quot.sound]`. No project axiom or proof escape is
present in the publication closure.

Use the pinned manifest directly; do not run `lake update`. On Windows,
extract this package to a short path such as `C:\gray-proof` so Mathlib's
longest source paths remain below the Win32 path limit.

## Licensing

See `LICENSE.md`. Lean source and verification scripts are Apache-2.0; the
manuscript is CC BY 4.0.
