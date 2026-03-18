# Hamilton Cycles in the Noncrossing Partition Refinement Graph

[![DOI](https://img.shields.io/badge/DOI-10.5281/zenodo.18957708-blue?style=flat-square&logo=zenodo)](https://doi.org/10.5281/zenodo.18957708)
[![Status](https://img.shields.io/badge/status-under%20review%20(EJC)-yellow?style=flat-square)](https://www.combinatorics.org/)

Companion code for the paper:

> **Hamilton Cycles in the Noncrossing Partition Refinement Graph**
> Alex Chengyu Li, 2026
>
> Under review at *Electronic Journal of Combinatorics*

## Interactive Proof Explorer

An interactive visualization of the minimum degree theorem (Theorem 3) is available at:

**[proof-explorer.html](https://crabsatellite.github.io/gray-code-evolution/proof-explorer.html)**

## Quick start

```bash
pip install numpy
python verify_all.py
```

This verifies all results from the paper in a few minutes (n ≤ 12).
For the full verification including n = 14 (takes hours):

```bash
python verify_all.py --full
```

## What is verified

| Claim                                                    | Script                 | Time    |
| -------------------------------------------------------- | ---------------------- | ------- |
| Theorem 1: N\_{2m+1}(−1) = (−1)^{m+1} C_m for n = 2..100 | `verify_all.py`        | < 1s    |
| Table 1: Bipartite class counts for n = 2..30            | `verify_all.py`        | < 1s    |
| Table 2: Graph statistics for NC_R(n), n = 4..12         | `verify_all.py`        | minutes |
| Hamilton cycles for even n = 4, 6, 8, 10, 12             | `verify_all.py`        | minutes |
| Hamilton cycle for n = 14 (2,674,440 vertices)           | `verify_all.py --full` | hours   |

## Structure

```
src/
  narayana.py       Narayana numbers, parity identity, bipartite counts
  noncrossing.py    Generate noncrossing partitions, build NC_R(n)
  hamilton.py       Warnsdorff's heuristic + Posa rotation-closure
verify_all.py       One-click verification of all paper results
data/results/       Pre-computed cycle metadata for each even n
```

## Requirements

- Python ≥ 3.9
- NumPy ≥ 1.24 (only needed for `--full`)

## Citation

```bibtex
@article{li2026hamilton,
  title   = {Hamilton Cycles in the Noncrossing Partition Refinement Graph},
  author  = {Li, Alex Chengyu},
  year    = {2026},
  doi     = {10.5281/zenodo.18957708},
  note    = {Under review at Electronic Journal of Combinatorics}
}
```

## License

MIT
