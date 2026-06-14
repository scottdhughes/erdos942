# Erdős Problem #942: a lower bound, with a formalized construction

A short note and an accompanying Lean 4 / Mathlib formalization, by S. D. Hughes.

A number `m` is *powerful* (squarefull) if every prime dividing `m` does so to
the power at least `2`, and `κ`-full if to the power at least `κ`. Erdős
Problem #942 (see erdosproblems.com/942) asks for the order of
`h(n)`, the number of powerful numbers in the interval `(n², (n+1)²)`. The
note proves that for every fixed `κ ≥ 2` there are infinitely many `n` with
at least `c·log n / (log log n · log log log n)` many `κ`-full numbers in
`(n^κ, (n+1)^κ)`, sharpening the exponent in the lower bound of
De Koninck–Luca and De Koninck–Luca–Shparlinski from `1/3` to `1 − o(1)`.

## The note

The 4-page write-up is in [`paper/erdos942.pdf`](paper/erdos942.pdf) (LaTeX
source alongside it in [`paper/`](paper/)). It proves the quantitative bound
`h_κ(n) ≫ log n / (log log n · log log log n)` infinitely often. The explicit
*rate* is established there classically and is **not** formalized below — it
requires an upper bound on the `n`-th prime that is not currently in Mathlib.

## What is formalized

Two layers, both with zero `sorry`, no `native_decide`, and standard axioms only.

**1. The construction (`Erdos942/Construction.lean`).** The construction itself —
the simultaneous Dirichlet box principle, the placement of the constructed
numbers in a window between consecutive squares, and the pigeonhole assembly —
yielding that the powerful-number count is unbounded:

| Theorem | Statement |
|---|---|
| `box_principle_simultaneous` | for reals `α i` and tolerances `δ i > 0` (finite `i`), some `q ≥ 1` has `‖q·α i‖ ≤ δ i` for all `i` |
| `placement_kfull_window` | for `d ∣ D` squarefree, `d ≥ 2`, and `q` well-approximating `1/√d`, the number `d·D²·round(q/√d)²` is powerful and lies strictly in `((Dq−1)², (Dq)²)` or `((Dq)², (Dq+1)²)` |
| `powerful_count_unbounded` | for every `ℓ` there is an `n` with at least `ℓ` powerful numbers strictly in `(n², (n+1)²)` |

`powerful_count_unbounded` is the qualitative form of the lower bound: it gives
`lim sup h(n) = ∞` constructively, via the box principle rather than via
Kronecker's theorem. The quantitative exponent is **not** captured here (see
above); this layer certifies the mechanism and the unboundedness conclusion, not
the rate.

**2. The arithmetic core (`Erdos942/Core.lean`).** The elementary facts the
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

Toolchain: `leanprover/lean4:v4.28.0`, Mathlib pinned in `lake-manifest.json`.
The build compiles every module with zero `sorry` and prints an axiom report
(`Erdos942/AxiomAudit.lean`): each of the six theorems above depends only on
`propext`, `Classical.choice`, `Quot.sound`. No `native_decide` is used.

## Related

Formalizations for Erdős Problem #367 (powerful parts of consecutive
integers) by the same author: [erdos367](https://github.com/scottdhughes/erdos367).

## License

Apache-2.0.
