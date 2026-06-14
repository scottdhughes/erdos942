# Erdős Problem #942: a formalized lower bound

A short note and an accompanying Lean 4 / Mathlib formalization, by S. D. Hughes.

A number `m` is *powerful* (squarefull) if every prime dividing `m` does so to
the power at least `2`, and `κ`-full if to the power at least `κ`. Erdős
Problem #942 (see erdosproblems.com/942) asks for the order of
`h(n)`, the number of powerful numbers in the interval `(n², (n+1)²)`. The
note proves that for every fixed `κ ≥ 2` there are infinitely many `n` with
at least `c·log n / (log log n · log log log n)` many `κ`-full numbers in
`(n^κ, (n+1)^κ)`, sharpening the exponent in the lower bound of
De Koninck–Luca and De Koninck–Luca–Shparlinski from `1/3` to `1 − o(1)`.

**This lower bound — the full Theorem 1.1, for every fixed `κ ≥ 2` — is
formalized and machine-checked in Lean 4 / Mathlib** (`powerful_count_rate_general`
below; `κ = 2` is Erdős #942 itself).

## The note

The 4-page write-up is in [`paper/erdos942.pdf`](paper/erdos942.pdf) (LaTeX
source alongside it in [`paper/`](paper/)). It proves the quantitative bound
`h_κ(n) ≫ log n / (log log n · log log log n)` infinitely often, for every fixed
`κ ≥ 2`, and that statement is formalized in full (next section).

## What is formalized

Three layers, all with zero `sorry`, no `native_decide`, and standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`). Requires Mathlib `v4.30.0` (the
Chebyshev lower bound `Chebyshev.pi_ge` it uses was added there).

**1. The rate (`Erdos942/Rate.lean`).** The full quantitative lower bound — the
complete Theorem 1.1, for every fixed `κ ≥ 2`, not merely unboundedness:

| Theorem | Statement |
|---|---|
| `powerful_count_rate_general` | for every fixed `κ ≥ 2`, there is `c > 0` such that for infinitely many `n`, at least `c · log n / (log log n · log log log n)` many `κ`-full numbers lie in `(n^κ, (n+1)^κ)` |
| `powerful_count_rate` | the `κ = 2` case (Erdős #942), as a corollary |

Supporting lemmas in the same module: `placement_kfull_window_general` (the
general-`κ` window placement), `nth_prime_upper` (the `h`-th prime is `O(h log h)`,
via `Chebyshev.pi_ge`), `box_principle_quantitative` (simultaneous Dirichlet with
the denominator bound), `squarefree_many_divisors` (a primorial with `h` prime
factors has `2^h − 1` squarefree divisors `> 1`), `log_primorial_le`
(`log ∏_{i<h} pᵢ ≪ h log h`), and `rate_inversion` (inverting the size bound).

**2. The construction, qualitative form (`Erdos942/Construction.lean`).** The
construction mechanism — the simultaneous Dirichlet box principle, the placement
of the constructed numbers in a window between consecutive squares, and the
pigeonhole assembly — packaged as unboundedness:

| Theorem | Statement |
|---|---|
| `box_principle_simultaneous` | for reals `α i` and tolerances `δ i > 0` (finite `i`), some `q ≥ 1` has `‖q·α i‖ ≤ δ i` for all `i` |
| `placement_kfull_window` | for `d ∣ D` squarefree, `d ≥ 2`, and `q` well-approximating `1/√d`, the number `d·D²·round(q/√d)²` is powerful and lies strictly in `((Dq−1)², (Dq)²)` or `((Dq)², (Dq+1)²)` |
| `powerful_count_unbounded` | for every `ℓ` there is an `n` with at least `ℓ` powerful numbers strictly in `(n², (n+1)²)` |

`powerful_count_unbounded` gives `lim sup h(n) = ∞` constructively (via the box
principle rather than Kronecker's theorem); `powerful_count_rate` strengthens
this to the explicit rate.

**3. The arithmetic core (`Erdos942/Core.lean`).** The elementary facts the
construction rests on, stated for general `κ`:

| Theorem | Statement | Note |
|---|---|---|
| `kfull_construction` | `d ∣ D` ⟹ `d · D^κ · r^κ` is `κ`-full | Lemma 2.1 |
| `construction_injective` | `κ ≥ 2`, `d₁, d₂` squarefree, `d₁r₁^κ = d₂r₂^κ` ⟹ `d₁ = d₂` and `r₁ = r₂` | Lemma 2.2 |
| `two_powerful_between_2909_2910` | two distinct powerful numbers lie strictly between `2909²` and `2910²` | Remark 2.1 |

The last is the note's hand-checkable instance (`D = 6`, `q = 485`):
`8467200 = 3·6²·280²` and `8468064 = 6·6²·198²`, both powerful, both in
`(8462281, 8468100)`, derived through `kfull_construction` rather than by
brute-force evaluation.

## Verifying

```sh
lake exe cache get
lake build
```

Toolchain: `leanprover/lean4:v4.30.0`, Mathlib pinned in `lake-manifest.json`.
The build compiles every module with zero `sorry` and prints an axiom report
(`Erdos942/AxiomAudit.lean`): every theorem above (the rate, the construction, and the arithmetic core) depends only on
`propext`, `Classical.choice`, `Quot.sound`. No `native_decide` is used.

## Related

Formalizations for Erdős Problem #367 (powerful parts of consecutive
integers) by the same author: [erdos367](https://github.com/scottdhughes/erdos367).

## License

Apache-2.0.
