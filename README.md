# Erdős Problem #942: bounds on powerful numbers between consecutive squares

A note and an accompanying Lean 4 / Mathlib formalization, by Scott D. Hughes.

A number `m` is *powerful* (squarefull) if every prime dividing `m` does so to the
power at least `2`. [Erdős Problem #942](https://www.erdosproblems.com/942) asks for
the order of `h(n)`, the number of powerful numbers in the open interval
`(n², (n+1)²)`; the conjectured truth is `(log n)^{1+o(1)}`.

This repository records **two complementary bounds** on `h(n)`, with their elementary
cores machine-checked in Lean 4 / Mathlib:

- **Frequency lower bound.** `#{ n ≤ x : h(n) ≥ V } ≥ x^{1−o(1)}` uniformly for
  `2 ≤ V ≤ (log x)^{1/2−ε}` (with an effective form for larger `V`). To the author's
  knowledge this is the first counting bound valid as `V → ∞`; prior distribution
  results are for fixed `ℓ`.
- **Upper bound.** `h(n) ≪_ε n^{6/25+ε}`, sharpening the elementary `n^{2/5}` and the
  recorded unconditional `O(n/log n)`.

Neither the lower-bound construction (De Koninck–Luca–Shparlinski, with the standard
primorial modulus) nor the upper-bound method (the classical *integer points close to
a curve* technology of Swinnerton-Dyer and Filaseta–Trifonov) is new. The
contributions are the reduction of the frequency question to simultaneous
equidistribution of the multiquadratic directions `{1/√d}` (made effective by a
Liouville bound), and the explicit worst-case (`θ = 0`, length `≍ √x`) upper exponent,
which the literature — having optimized the asymptotic `θ > 0` regime — did not record.
Both sides leave a gap to the conjectured `(log n)^{1+o(1)}`, governed in each case by
an equidistribution input beyond current technology.

The infinitely-often lower bound `h(n) ≫ log n / (log log n · log log log n)` (the
folklore sharpening of De Koninck–Luca–Shparlinski via Dirichlet + a primorial
modulus) is **not new**; it is retained here as context, and its general-`κ`
formalization remains in `Erdos942/Rate.lean`.

## Papers

- **Current (this work):** [`paper/main.pdf`](paper/main.pdf) — *Powerful numbers
  between consecutive squares* (the two-sided result above).
- **Original note (v1):** [`paper/erdos942.pdf`](paper/erdos942.pdf) — *Many powerful
  numbers between consecutive powers* (the infinitely-often lower bound, general `κ`).
  This is the version linked from the erdosproblems.com/942 forum and is kept here
  unchanged; the `v0.1.0` tag is the corresponding repository snapshot.

## What is formalized

Every elementary and algebraic step below is checked with zero `sorry`, no
`native_decide`, on the standard axioms `{propext, Classical.choice, Quot.sound}`
(Mathlib `v4.30.0`). Three classical theorems that are **not presently in Mathlib**
are recorded as explicit, documented axioms (listed at the end); each headline counting
theorem is checked *relative to* exactly one of them.

### Lower side — the construction and the frequency bound

**Rate / construction / arithmetic core** (`Erdos942/Rate.lean`,
`Erdos942/Construction.lean`, `Erdos942/Core.lean`) — fully proved on standard axioms:

| Theorem | Statement |
|---|---|
| `powerful_count_rate_general` | for every fixed `κ ≥ 2`, `c·log n/(log log n · log log log n)` many `κ`-full numbers in `(n^κ,(n+1)^κ)` for infinitely many `n` |
| `powerful_count_rate` | the `κ = 2` case (Erdős #942) |
| `box_principle_simultaneous` / `box_principle_quantitative` | simultaneous Dirichlet with the denominator bound |
| `placement_kfull_window(_general)` | the constructed `d·D^κ·r^κ` is `κ`-full and lands in a window between consecutive powers |
| `kfull_construction`, `construction_injective` | powerfulness (Lemma 2.1) and distinctness (Lemma 2.2) |
| `log_primorial_le`, `nth_prime_upper` | `log ∏_{i<h} pᵢ ≪ h log h` via `Chebyshev.pi_ge` |

**Frequency** (`Erdos942/Frequency.lean`):

| Item | Status |
|---|---|
| exact window criterion, powerfulness, distinctness, `h(Dq) ≥ ℓ` from a box hit | proved, standard axioms |
| `liouville_from_nonzero_int_norm`, `int_norm_ne_zero` (the Liouville mechanism) | proved, standard axioms |
| `multiquadratic_liouville_bound` (`‖a·α‖ ≥ M^{−ℓ}`) | proved **modulo** the axiom `multiquadratic_liouville` (`[K:ℚ]=2^h`) |
| `frequency_lower_bound` (the frequency bound) | proved **modulo** the axiom `simultaneous_equidistribution_count` (Erdős–Turán–Koksma) |

### Upper side — the reduction (`Erdos942/UpperBound.lean`)

| Theorem | Status |
|---|---|
| `powerful_rep` (`m = a²b³`, `b` squarefree) | proved, standard axioms |
| `at_most_one_per_b`, `at_most_one_per_a` (≤1 admissible parameter per window) | proved, standard axioms |
| `min_pow_le` (the split `min(a,b)^5 ≤ (n+1)²`) | proved, standard axioms |
| `hUp_le_aspects` (the reduction inequality) | proved, standard axioms |
| `upper_bound` (`h(n) ≪_ε n^{6/25+ε}`) | proved **modulo** the axiom `ft_curve_count` (Filaseta–Trifonov) |

### The three classical axioms (not in Mathlib)

Each is a classical, provable theorem, documented in place and reported by
`Erdos942/AxiomAudit.lean`:

1. `simultaneous_equidistribution_count` — the Erdős–Turán–Koksma discrepancy estimate
   for the sequence `(q·α)` (Weyl sums + the ETK inequality).
2. `multiquadratic_liouville` — `[ℚ(√p₁,…,√p_h):ℚ] = 2^h` and the `ℚ`-linear
   independence of the `√d`, giving the Liouville exponent `ℓ` (CAS-verified).
3. `ft_curve_count` — the Filaseta–Trifonov "integer points close to a curve" count
   (PLMS (3) 73 (1996), Thm 4.1), applied dyadically; the worst block `a ≍ b ≍ n^{2/5}`
   yields the `6/25` exponent.

Everything else — both elementary cores, the Liouville mechanism, and the entire
infinitely-often/rate development — is proved outright.

## Verifying

```sh
lake exe cache get
lake build
```

Toolchain: `leanprover/lean4:v4.30.0`, Mathlib pinned in `lake-manifest.json`. The build
compiles every module with zero `sorry`, no `native_decide`, and `Erdos942/AxiomAudit.lean`
prints the axiom footprint of each theorem above.

## The empirical maximum

The value `max_{n ≤ 10⁷} h(n) = 9` (first attained at `n = 524827`), quoted in the paper,
is reproduced by [`scripts/h942_count.py`](scripts/h942_count.py) — pure-Python, exact
integer arithmetic (no floats), self-testing against direct factorization:

```sh
python3 scripts/h942_count.py 10000000
```

It enumerates every powerful `m = a²b³` (`b` squarefree, `b ≥ 2`) with `m < (N+1)²`, buckets
by `n = ⌊√m⌋`, cross-checks the counts against brute-force factorization for `n ≤ 3000`, and
reports `max h(n)`, its argmax, and the full distribution.

## Related

Formalizations for Erdős Problem #367 (powerful parts of consecutive integers) by the
same author: [erdos367](https://github.com/scottdhughes/erdos367).

## License

Apache-2.0.
