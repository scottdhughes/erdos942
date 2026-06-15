#!/usr/bin/env python3
"""
Enumerate  h(n) = #{ powerful m : n^2 < m < (n+1)^2 }  and report its maximum.

A number m is *powerful* (squarefull) if every prime dividing it does so to power >= 2.
Every powerful number has a unique representation m = a^2 * b^3 with b squarefree, and m
is a perfect square iff b = 1; so the powerful numbers strictly inside (n^2, (n+1)^2) are
exactly those with b >= 2 squarefree. We enumerate all such m < (N+1)^2 and bucket by
n = isqrt(m), giving h(n) for every n <= N exactly (integer arithmetic only -- no floats).

Usage:  python3 h942_count.py [N]        # default N = 10**7

Reproduces the empirical claim   max_{n <= 10^7} h(n) = 9,  first attained at n = 524827.
"""
import sys
from math import isqrt
from collections import Counter


def squarefree_sieve(limit):
    """sf[b] == 1  iff  b is squarefree, for 0 <= b <= limit."""
    sf = bytearray([1]) * (limit + 1)
    p = 2
    while p * p <= limit:
        sq = p * p
        for k in range(sq, limit + 1, sq):
            sf[k] = 0
        p += 1
    return sf


def count_h(N):
    """cnt[n] = h(n) for 0 <= n <= N, via the a^2 b^3 enumeration (exact)."""
    cnt = [0] * (N + 1)
    bound = (N + 1) * (N + 1)                     # enumerate powerful m with m < bound
    bmax = 1
    while (bmax + 1) ** 3 < bound:
        bmax += 1
    sf = squarefree_sieve(bmax)
    for b in range(2, bmax + 1):
        if not sf[b]:
            continue
        b3 = b * b * b
        amax = isqrt((bound - 1) // b3)
        while amax * amax * b3 >= bound:          # exact boundary trim
            amax -= 1
        for a in range(1, amax + 1):
            m = a * a * b3
            n = isqrt(m)                          # n^2 <= m < (n+1)^2; b>=2 squarefree => m != n^2
            if n <= N:
                cnt[n] += 1
    return cnt


def is_powerful(m):
    """Independent test: trial-factor m; powerful iff every prime exponent is >= 2."""
    x = m
    d = 2
    while d * d <= x:
        if x % d == 0:
            e = 0
            while x % d == 0:
                x //= d
                e += 1
            if e < 2:
                return False
        d += 1 if d == 2 else 2
    return x == 1                                  # any leftover prime occurs to power 1


def brute_h(n):
    """h(n) by direct test of every m in (n^2, (n+1)^2)."""
    lo, hi = n * n + 1, (n + 1) * (n + 1)
    return sum(1 for m in range(lo, hi) if is_powerful(m))


def selftest(cnt, upto=3000):
    """Cross-check the enumeration against direct factorization for 1 <= n <= upto."""
    for n in range(1, min(upto, len(cnt) - 1) + 1):
        b = brute_h(n)
        if cnt[n] != b:
            raise AssertionError(f"MISMATCH at n={n}: enumeration {cnt[n]} vs brute {b}")
    print(f"self-test passed: enumeration matches direct factorization for all 1 <= n <= {upto}")


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 7
    cnt = count_h(N)
    selftest(cnt, upto=min(3000, N))
    mx = max(cnt)
    arg = cnt.index(mx)
    dist = Counter(cnt[1:N + 1])
    records = [n for n in range(1, N + 1) if cnt[n] == mx]
    print(f"N = {N}")
    print(f"max_{{n <= {N}}} h(n) = {mx}, first attained at n = {arg}")
    print(f"distribution of h(n) over 1 <= n <= {N}: {dict(sorted(dist.items()))}")
    head = records[:10]
    print(f"all n with h(n) = {mx}: {head}{' ...' if len(records) > 10 else ''} ({len(records)} total)")


if __name__ == "__main__":
    main()
