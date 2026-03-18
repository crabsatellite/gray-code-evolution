"""
Generate noncrossing partitions and build the refinement graph NC_R(n).

Two partitions are adjacent in NC_R(n) if one is obtained from the other
by merging two blocks into one (equivalently, splitting one block into two),
provided the result remains noncrossing.
"""

import math
import time


def catalan(n):
    """Catalan number C_n."""
    return math.comb(2 * n, n) // (n + 1)


def generate(n):
    """
    Generate all noncrossing partitions of [n].

    Uses the recursive structure: element 1 belongs to some block B.
    Elements between consecutive members of B form independent
    noncrossing sub-partitions.

    Returns a list of partitions, each a tuple of frozensets.
    """
    if n == 0:
        return [()]
    if n == 1:
        return [(frozenset([1]),)]

    results = []

    def _generate(elements):
        if not elements:
            yield ()
            return

        first = elements[0]
        rest = elements[1:]

        def blocks_containing_first(elems, block_so_far):
            yield frozenset(block_so_far)
            if not elems:
                return
            for idx, e in enumerate(elems):
                yield from blocks_containing_first(
                    elems[idx + 1:], block_so_far + [e]
                )

        for block in blocks_containing_first(list(rest), [first]):
            block_sorted = sorted(block)
            remaining = [e for e in elements if e not in block]
            gaps = []
            for i in range(len(block_sorted)):
                lo = block_sorted[i]
                hi = (block_sorted[i + 1]
                      if i + 1 < len(block_sorted)
                      else max(elements) + 1)
                gap = [e for e in remaining if lo < e < hi]
                if gap:
                    gaps.append(gap)

            def combine_gaps(gap_idx):
                if gap_idx == len(gaps):
                    yield (block,)
                    return
                for sub_part in _generate(gaps[gap_idx]):
                    for rest_parts in combine_gaps(gap_idx + 1):
                        yield sub_part + rest_parts

            yield from combine_gaps(0)

    for p in _generate(list(range(1, n + 1))):
        canon = tuple(sorted(p, key=lambda b: min(b)))
        results.append(canon)

    # Deduplicate
    seen = set()
    unique = []
    for p in results:
        key = tuple(tuple(sorted(b)) for b in p)
        if key not in seen:
            seen.add(key)
            unique.append(p)
    return unique


def build_refinement_graph(partitions, n):
    """
    Build the refinement graph NC_R(n).

    Returns adj (list of sorted neighbor lists) and the number of edges.
    """
    nv = len(partitions)

    part_to_idx = {}
    for i, p in enumerate(partitions):
        key = tuple(tuple(sorted(b)) for b in sorted(p, key=lambda b: min(b)))
        part_to_idx[key] = i

    adj = [[] for _ in range(nv)]

    for i, p in enumerate(partitions):
        blocks = list(p)
        nb = len(blocks)
        for a in range(nb):
            for b in range(a + 1, nb):
                merged = blocks[a] | blocks[b]
                new_blocks = [blocks[k] for k in range(nb) if k != a and k != b]
                new_blocks.append(merged)
                new_part = tuple(sorted(new_blocks, key=lambda bl: min(bl)))
                key = tuple(tuple(sorted(bl)) for bl in new_part)
                if key in part_to_idx:
                    j = part_to_idx[key]
                    adj[i].append(j)
                    adj[j].append(i)

    # Deduplicate
    for i in range(nv):
        adj[i] = sorted(set(adj[i]))

    n_edges = sum(len(a) for a in adj) // 2
    return adj, n_edges


def graph_stats(adj):
    """Return (vertices, edges, min_deg, max_deg, avg_deg)."""
    nv = len(adj)
    n_edges = sum(len(a) for a in adj) // 2
    degs = [len(a) for a in adj]
    return nv, n_edges, min(degs), max(degs), sum(degs) / nv


if __name__ == "__main__":
    print("Generating noncrossing partitions and verifying Catalan counts:")
    for n in range(1, 15):
        t0 = time.time()
        parts = generate(n)
        elapsed = time.time() - t0
        expected = catalan(n)
        ok = "OK" if len(parts) == expected else "FAIL"
        print(f"  n={n:2d}: |NC({n})| = {len(parts):>10,}  (C_{n} = {expected:>10,})  {ok}  [{elapsed:.2f}s]")
        if elapsed > 60:
            break
