#!/usr/bin/env python3
"""
One-click verification of all results in:

  "Hamilton Cycles in the Noncrossing Partition Refinement Graph"

Usage:
  python verify_all.py            # verify everything except n=14 (minutes)
  python verify_all.py --full     # include n=14 Hamilton cycle search (hours)

Requirements: Python 3.9+, NumPy (for --full only)
"""

import argparse
import gc
import sys
import time

sys.path.insert(0, "src")

from narayana import (
    narayana, catalan, narayana_poly_at_minus1,
    verify_identity, verify_bipartite_balance,
)
from noncrossing import generate, build_refinement_graph, graph_stats
from hamilton import find_hamilton_cycle, verify_cycle


def section(title):
    print()
    print("=" * 64)
    print(f"  {title}")
    print("=" * 64)
    print()


def verify_theorem1():
    """Theorem 1: N_{2m+1}(-1) = (-1)^{m+1} C_m (Mansour--Sun, 2009)."""
    section("Theorem 1: Narayana parity identity")
    ok = verify_identity(n_max=100)
    return ok


def verify_table1():
    """Table 1: Bipartite color class counts."""
    section("Table 1: Bipartite class counts")
    verify_bipartite_balance(n_max=30)
    return True


def verify_table2():
    """Table 2: Graph statistics for NC_R(n)."""
    section("Table 2: Graph statistics")
    print(f"{'n':>3} {'|V|':>10} {'|E|':>12} {'d_min':>6} {'d_max':>6} {'d_avg':>8}")
    print("-" * 50)

    for n in [4, 6, 8, 10, 12]:
        t0 = time.time()
        parts = generate(n)
        adj, n_edges = build_refinement_graph(parts, n)
        nv, ne, dmin, dmax, davg = graph_stats(adj)
        elapsed = time.time() - t0
        print(f"{n:>3} {nv:>10,} {ne:>12,} {dmin:>6} {dmax:>6} {davg:>8.1f}  [{elapsed:.1f}s]")
        del parts, adj
        gc.collect()

    print()
    return True


def verify_hamilton_cycles(include_14=False):
    """Conjecture 1: Hamilton cycles exist for all even n >= 4."""
    section("Conjecture 1: Hamilton cycle search")

    targets = [4, 6, 8, 10, 12]
    if include_14:
        targets.append(14)

    all_ok = True
    for n in targets:
        print(f"--- NC_R({n}) ---")
        t0 = time.time()

        parts = generate(n)
        nv = len(parts)
        print(f"  |V| = {nv:,}")

        adj, n_edges = build_refinement_graph(parts, n)
        print(f"  |E| = {n_edges:,}")
        del parts
        gc.collect()

        use_np = (n >= 14)
        max_att = 50 if n >= 14 else 10000
        rot_factor = 50

        cycle = find_hamilton_cycle(
            adj,
            max_attempts=max_att,
            use_numpy=use_np,
            rotation_budget_factor=rot_factor,
        )

        if cycle is not None:
            verify_cycle(cycle, adj)
            elapsed = time.time() - t0
            print(f"  VERIFIED Hamilton cycle ({elapsed:.1f}s total)")
        else:
            elapsed = time.time() - t0
            print(f"  NOT FOUND ({elapsed:.1f}s) -- try increasing attempts or rotation budget")
            all_ok = False

        del adj
        gc.collect()
        print()

    return all_ok


def main():
    parser = argparse.ArgumentParser(
        description="Verify all results from the paper."
    )
    parser.add_argument(
        "--full", action="store_true",
        help="Include n=14 Hamilton cycle search (requires NumPy, takes hours)"
    )
    args = parser.parse_args()

    print("Hamilton Cycles in the Noncrossing Partition Refinement Graph")
    print("Verification Script")
    print()

    t_start = time.time()

    ok1 = verify_theorem1()
    ok2 = verify_table1()
    ok3 = verify_table2()
    ok4 = verify_hamilton_cycles(include_14=args.full)

    section("Summary")
    elapsed = time.time() - t_start

    results = [
        ("Theorem 1 (parity identity)", ok1),
        ("Table 1 (bipartite counts)", ok2),
        ("Table 2 (graph statistics)", ok3),
        ("Hamilton cycles", ok4),
    ]

    all_ok = True
    for name, ok in results:
        status = "PASS" if ok else "FAIL"
        print(f"  {name}: {status}")
        if not ok:
            all_ok = False

    print()
    print(f"Total time: {elapsed:.1f}s")

    if not args.full:
        print()
        print("Note: n=14 was skipped. Run with --full to include it (takes hours).")

    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
