"""
Hamilton cycle search via Warnsdorff's heuristic with Posa rotation-closure.

Algorithm:
1. Find a Hamilton PATH using Warnsdorff's rule (greedy, O(|V|) per attempt).
2. Close the path into a CYCLE via Posa rotation-extension:
   given path [v0, ..., v_{n-1}], if v_{n-1} ~ v_i, rotate to
   [v0, ..., v_i, v_{n-1}, v_{n-2}, ..., v_{i+1}] and check if the
   new endpoint closes the cycle.

For NC_R(n) with n <= 12, pure-Python rotation-closure suffices.
For NC_R(14) (2.67M vertices), NumPy-accelerated rotation is used.
"""

import random
import time

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False


def warnsdorff_path(adj, nv, rng):
    """
    Find a Hamilton path using Warnsdorff's rule.
    Returns a list of vertex indices, or None if the path gets stuck.
    """
    start = rng.randint(0, nv - 1)
    visited = bytearray(nv)
    visited[start] = 1
    path = [start]
    rem_deg = [len(adj[v]) for v in range(nv)]
    for nb in adj[start]:
        rem_deg[nb] -= 1

    while len(path) < nv:
        current = path[-1]
        best_deg = nv + 1
        best_list = []
        for nb in adj[current]:
            if not visited[nb]:
                d = rem_deg[nb]
                if d < best_deg:
                    best_deg = d
                    best_list = [nb]
                elif d == best_deg:
                    best_list.append(nb)
        if not best_list:
            return None
        chosen = best_list[rng.randint(0, len(best_list) - 1)]
        path.append(chosen)
        visited[chosen] = 1
        for nb in adj[chosen]:
            if not visited[nb]:
                rem_deg[nb] -= 1

    return path


def rotation_closure(path, adj, max_rotations):
    """
    Close a Hamilton path into a cycle via Posa rotation-extension.
    Pure-Python version; suitable for |V| up to ~200,000.
    """
    path = list(path)
    n = len(path)
    first = path[0]
    adj_sets = [set(adj[v]) for v in range(n)]
    rng = random.Random(12345)

    for rot in range(max_rotations):
        last = path[-1]
        if last in adj_sets[first]:
            return path

        candidates = []
        for i in range(1, n - 1):
            if path[i] in adj_sets[last]:
                candidates.append(i)

        if not candidates:
            return None

        i = candidates[rng.randint(0, len(candidates) - 1)]
        path[i + 1:] = path[i + 1:][::-1]

    return None


def rotation_closure_numpy(path, adj, max_rotations):
    """
    NumPy-accelerated rotation-closure for large graphs.
    Uses a position index for O(degree) candidate search instead of O(|V|).
    """
    if not HAS_NUMPY:
        raise ImportError("NumPy is required for large-scale rotation-closure")

    n = len(path)
    path_arr = np.array(path, dtype=np.int32)
    first = int(path_arr[0])
    adj_sets = [set(adj[v]) for v in range(n)]

    # Position index: pos[v] = index of vertex v in path
    pos = np.empty(n, dtype=np.int32)
    for i in range(n):
        pos[path_arr[i]] = i

    rng = random.Random(12345)
    t0 = time.time()

    for rot in range(max_rotations):
        last = int(path_arr[n - 1])
        if last in adj_sets[first]:
            return path_arr.tolist()

        candidates = []
        for nb in adj[last]:
            p = int(pos[nb])
            if 1 <= p <= n - 2:
                candidates.append(p)

        if not candidates:
            return None

        i = candidates[rng.randint(0, len(candidates) - 1)]
        path_arr[i + 1:] = path_arr[i + 1:][::-1]
        pos[path_arr[i + 1:]] = np.arange(i + 1, n, dtype=np.int32)

        if (rot + 1) % 100000 == 0:
            elapsed = time.time() - t0
            rate = (rot + 1) / elapsed
            print(f"    {rot + 1:,} rotations ({elapsed:.0f}s, {rate:.0f}/s)", flush=True)

    return None


def find_hamilton_cycle(adj, max_attempts=10000, seed=42, use_numpy=False,
                        rotation_budget_factor=50, verbose=True):
    """
    Search for a Hamilton cycle in the graph defined by adj.

    Parameters
    ----------
    adj : list of lists
        Adjacency list (adj[v] = sorted list of neighbors of v).
    max_attempts : int
        Maximum number of Warnsdorff path attempts.
    seed : int
        Random seed for reproducibility.
    use_numpy : bool
        Use NumPy-accelerated rotation for large graphs.
    rotation_budget_factor : int
        Max rotations = |V| * this factor.
    verbose : bool
        Print progress messages.

    Returns
    -------
    list or None
        Hamilton cycle as a vertex list, or None if not found.
    """
    nv = len(adj)
    rng = random.Random(seed)
    rot_fn = rotation_closure_numpy if use_numpy else rotation_closure
    rot_budget = nv * rotation_budget_factor
    t0 = time.time()

    for attempt in range(max_attempts):
        path = warnsdorff_path(adj, nv, rng)
        if path is None:
            continue

        cycle = rot_fn(path, adj, max_rotations=rot_budget)
        if cycle is not None:
            elapsed = time.time() - t0
            if verbose:
                print(f"  Hamilton cycle found on attempt {attempt + 1} ({elapsed:.1f}s)")
            return cycle

        if verbose and (attempt + 1) % 100 == 0:
            elapsed = time.time() - t0
            print(f"  {attempt + 1} attempts ({elapsed:.1f}s)", flush=True)

    return None


def verify_cycle(cycle, adj):
    """Verify that a cycle is a valid Hamilton cycle."""
    nv = len(adj)
    assert len(cycle) == nv, f"Cycle length {len(cycle)} != {nv}"
    assert len(set(cycle)) == nv, f"Cycle has repeated vertices"
    for i in range(nv):
        v, w = cycle[i], cycle[(i + 1) % nv]
        assert w in adj[v], f"Missing edge {v}-{w}"
    return True
