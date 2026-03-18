"""Narayana numbers and the parity identity (Mansour--Sun, 2009)."""

import math


def narayana(n, k):
    """Narayana number N(n, k) = (1/n) C(n,k) C(n, k-1)."""
    if k < 1 or k > n:
        return 0
    return math.comb(n, k) * math.comb(n, k - 1) // n


def catalan(n):
    """Catalan number C_n = C(2n, n) / (n + 1)."""
    return math.comb(2 * n, n) // (n + 1)


def narayana_poly_at_minus1(n):
    """Evaluate N_n(-1) = sum_{k=1}^{n} N(n,k) (-1)^k."""
    return sum(narayana(n, k) * ((-1) ** k) for k in range(1, n + 1))


def verify_identity(n_max=100):
    """
    Verify Theorem 1 (cf. Mansour--Sun, Example 2.2):
      N_{2m}(-1)   = 0                  for all even n
      N_{2m+1}(-1) = (-1)^{m+1} C_m    for all odd n
    """
    print(f"Verifying Narayana parity identity for n = 2 .. {n_max}")
    print()

    failures = 0
    for n in range(2, n_max + 1):
        val = narayana_poly_at_minus1(n)
        if n % 2 == 0:
            expected = 0
        else:
            m = (n - 1) // 2
            expected = ((-1) ** (m + 1)) * catalan(m)
        ok = val == expected
        if not ok:
            print(f"  FAIL n={n}: got {val}, expected {expected}")
            failures += 1

    if failures == 0:
        print(f"  All {n_max - 1} values verified.")
    return failures == 0


def bipartite_class_counts(n):
    """
    Compute |even-rank| and |odd-rank| for NC(n).
    Rank = number of blocks; bipartite classes are even-block vs odd-block.
    """
    even_count = sum(narayana(n, k) for k in range(2, n + 1, 2))
    odd_count = sum(narayana(n, k) for k in range(1, n + 1, 2))
    return even_count, odd_count


def verify_bipartite_balance(n_max=30):
    """
    Verify Table 1: for even n the two classes are equal,
    for odd n they differ by |N_n(-1)|.
    """
    print(f"Bipartite class counts for n = 2 .. {n_max}")
    print()
    print(f"{'n':>3} {'C_n':>12} {'Even-block':>12} {'Odd-block':>12} {'Equal':>6} {'Diff':>10}")
    print("-" * 60)

    for n in range(2, n_max + 1):
        c_n = catalan(n)
        even_ct, odd_ct = bipartite_class_counts(n)
        assert even_ct + odd_ct == c_n
        eq = "YES" if even_ct == odd_ct else "no"
        diff = abs(even_ct - odd_ct)
        print(f"{n:>3} {c_n:>12,} {even_ct:>12,} {odd_ct:>12,} {eq:>6} {diff:>10,}")

    print()


if __name__ == "__main__":
    verify_identity()
    print()
    verify_bipartite_balance()
