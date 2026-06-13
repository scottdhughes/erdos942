# Erdős Problem #942: a lower bound, with formalized arithmetic core

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
source alongside it in [`paper/`](paper/)). The lower bound itself —
the box-principle choice of the denominator `q`, the placement of the
constructed numbers in the window, and the pigeonhole count — is proved there
classically. **Lean is not used for that argument.** What is formalized is the
elementary arithmetic core the construction rests on, described next.

## What is formalized

The construction produces the candidate numbers `m = d · D^κ · r^κ` with `d` a
squarefree divisor of a primorial `D`. The module `Erdos942/Core.lean`
certifies the three arithmetic facts about these numbers:

| Theorem | Statement | Paper |
|---|---|---|
| `kfull_construction` | `d ∣ D` ⟹ `d · D^κ · r^κ` is `κ`-full | Lemma 2.1 |
| `construction_injective` | `κ ≥ 2`, `d₁, d₂` squarefree, `d₁r₁^κ = d₂r₂^κ` ⟹ `d₁ = d₂` and `r₁ = r₂` | Lemma 2.2 |
| `two_powerful_between_2909_2910` | two distinct powerful numbers lie strictly between `2909²` and `2910²` | Remark 2.1 |

The third statement is the note's hand-checkable instance (`D = 6`, `q = 485`):
`8467200 = 3·6²·280²` and `8468064 = 6·6²·198²`, both powerful, both in
`(8462281, 8468100)`. Its proof goes through `kfull_construction` rather than
brute-force evaluation.

These are the elementary inputs to the construction; the analytic content of
the theorem (the simultaneous-approximation and counting argument) lives in the
note, not here.

## Verifying

```sh
lake exe cache get
lake build
```

Toolchain: `leanprover/lean4:v4.28.0`, Mathlib pinned in `lake-manifest.json`.
The build compiles every module with zero `sorry` and prints an axiom report
(`Erdos942/AxiomAudit.lean`): each theorem above depends only on
`propext`, `Classical.choice`, `Quot.sound`. No `native_decide` is used.

## Related

Formalizations for Erdős Problem #367 (powerful parts of consecutive
integers) by the same author: [erdos367](https://github.com/scottdhughes/erdos367).

## License

Apache-2.0.
