# Erdős Problem #942: formalized construction core

Lean 4 / Mathlib formalization accompanying the paper *Many powerful numbers
between consecutive powers* (S. D. Hughes).

A number `m` is *powerful* (squarefull) if every prime dividing `m` does so to
the power at least `2`, and `κ`-full if to the power at least `κ`. Erdős
Problem #942 (see erdosproblems.com/942) asks for the order of
`h(n)`, the number of powerful numbers in the interval `(n², (n+1)²)`. The
paper proves that for every fixed `κ ≥ 2` there are infinitely many `N` with
at least `c·log N / (log log N · log log log N)` many `κ`-full numbers in
`(N^κ, (N+1)^κ)`, improving the lower bound of De Koninck–Luca–Shparlinski.

## Contents

The construction underlying the theorem produces the candidate numbers
`m = d · D^κ · r^κ` with `d` a squarefree divisor of `D`. The module
`Erdos942/Core.lean` certifies its arithmetic core:

| Theorem | Statement | Paper |
|---|---|---|
| `kfull_construction` | `d ∣ D` ⟹ `d · D^κ · r^κ` is `κ`-full | Lemma 2.1 |
| `construction_injective` | `κ ≥ 2`, `d₁, d₂` squarefree, `d₁r₁^κ = d₂r₂^κ` ⟹ `d₁ = d₂` and `r₁ = r₂` | Lemma 2.2 |
| `two_powerful_between_2909_2910` | two distinct powerful numbers lie strictly between `2909²` and `2910²` | Remark 2.1 |

The third statement is the paper's hand-checkable instance (`D = 6`, `q = 485`):
`8467200 = 3·6²·280²` and `8468064 = 6·6²·198²`, both powerful, both in
`(8462281, 8468100)`. Its proof goes through `kfull_construction` rather than
brute-force evaluation. The Dirichlet/pigeonhole part of the paper (the choice
of `q` and the placement of the `m_j` in the window) is analytic bookkeeping
and is proved in the paper, not in Lean.

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
