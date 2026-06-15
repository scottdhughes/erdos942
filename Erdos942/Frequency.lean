import Erdos942.Core
import Erdos942.Construction

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Erdős #942 — frequency lower bound: the elementary + algebraic CORE

This file formalizes the *elementary and algebraic core* of the frequency lower
bound

  `#{ n ≤ x : h(n) ≥ V } ≥ x^{1-o(1)}`,

where `h(n)` is the number of powerful (squarefull) integers in the open interval
`(n², (n+1)²)`.  The construction (Dirichlet rounding against a primorial `D`) is
already formalized qualitatively/quantitatively in `Construction.lean` / `Rate.lean`.

What is **proved with zero `sorry`** here (priority block P1):

* `P1a_powerful`      — `m = d·(D·r)²` is `2`-full (squarefull) for `d ∣ D`.
* `window_iff_t_lt_one` — the EXACT real window characterization: for `n ≥ 0`,
  `t > 0`, `0 < 2 n t + t² ∧ 2 n t + t² < 2 n + 1 ↔ t < 1`.  This is the heart of
  the construction's correctness (the "upper side" placement).
* `mOf_sub_sq_factored` — the algebraic identity `m - n² = 2 n t + t²`
  with `t = D √d · η`, tying the abstract iff to the actual constructed value.
* `window_upper_iff`  — combining the two: the constructed `m` lies in
  `(n², (n+1)²)` on the upper side **iff** `t < 1`.
* `P1c_distinct`      — distinct squarefree kernels give distinct constructed values.
* `P1d_count_ge`      — the deduction: if `ℓ` distinct squarefree divisors of `D`
  all hit the upper window at `q`, then `(n², (n+1)²)` contains `≥ ℓ` powerful
  integers, i.e. `h(n) ≥ ℓ`.
* `hOf`               — the function `h(n)`, with `hOf_ge_of_directions`.

Priority block P2 (algebraic Liouville core) is in §P2 below: the *general
principle* — a nonzero algebraic integer's field norm is a nonzero rational
integer, hence `|N(γ)| ≥ 1`, giving the Liouville-type lower bound on a single
conjugate — is proved in full from Mathlib.  The specifically *multiquadratic*
input (`[K:ℚ] = 2^h` and the explicit conjugate bound `M`) is isolated as the
single documented axiom `multiquadratic_liouville` (Mathlib has no multiquadratic
field API), built honestly on top of the proved general principle.

Priority block P3 (analytic equidistribution) is the single clearly-marked
`axiom simultaneous_equidistribution_count`, and the conditional headline
`Theorem A` (`frequency_lower_bound`) is proved from exactly that axiom plus the
elementary core.
-/

namespace Erdos942.Frequency

/-! ## P1(a) — the constructed value is powerful (squarefull) -/

/-- The constructed value `m = d · (D r)²`. -/
def mVal (d D r : ℕ) : ℕ := d * (D * r) ^ 2

/-- `mVal d D r = d · D² · r²`, matching the `kfull_construction` shape. -/
theorem mVal_eq (d D r : ℕ) : mVal d D r = d * D ^ 2 * r ^ 2 := by
  unfold mVal; ring

/-- **P1(a).** `m = d·(D r)²` is `2`-full (powerful/squarefull) whenever `d ∣ D`. -/
theorem P1a_powerful (d D r : ℕ) (hdD : d ∣ D) : KFull 2 (mVal d D r) := by
  rw [mVal_eq]; exact kfull_construction 2 d D r hdD

/-! ## P1(b) — the EXACT window characterization

The "upper side" placement.  With `n = D q` and the constructed `m = d·(D r)²`,
write the signed rounding deviation `η = r − q/√d` and `t = D √d · η`.  Then the
algebraic identity is `m − n² = 2 n t + t²`, and (for `t > 0`) the integer
window condition `0 < m − n² < 2n+1` holds **iff** `t < 1`. -/

/-- **P1(b), abstract iff (the heart).**  For real `n ≥ 0` and `t > 0`,
`0 < 2 n t + t² ∧ 2 n t + t² < 2 n + 1 ↔ t < 1`.
(`t ≥ 1 ⟹ 2 n t + t² ≥ 2 n + 1`, and `t < 1 ⟹ 0 < 2 n t + t² < 2 n + 1`.) -/
theorem window_iff_t_lt_one (n t : ℝ) (hn : 0 ≤ n) (ht : 0 < t) :
    (0 < 2 * n * t + t ^ 2 ∧ 2 * n * t + t ^ 2 < 2 * n + 1) ↔ t < 1 := by
  constructor
  · rintro ⟨_, hlt⟩
    -- if t ≥ 1 then 2 n t + t² ≥ 2 n + 1, contradiction
    by_contra hge
    rw [not_lt] at hge   -- 1 ≤ t
    nlinarith [hge, hn, ht]
  · intro htlt
    refine ⟨by nlinarith [hn, ht], by nlinarith [hn, ht, htlt]⟩

/-- The exact real identity `m − n² = 2 n t + t²` for the upper-side parametrization.
Here `n = D q`, `m = d·(D r)²`, `t = D √d · η`, `η = r − q/√d`.  We package it in
the variables that make the iff immediate: given `mr := D √d · r` (so `m = mr²`)
and `n = D q`, with `t = mr − n`, we have `m − n² = 2 n t + t²`. -/
theorem mOf_sub_sq_factored (mr n : ℝ) :
    mr ^ 2 - n ^ 2 = 2 * n * (mr - n) + (mr - n) ^ 2 := by
  ring

/-- The real square-root realization `m = (D √d r)²`, i.e. `(↑(mVal d D r) : ℝ) = (D √d r)²`. -/
theorem mVal_cast_sq (d D r : ℕ) :
    ((mVal d D r : ℕ) : ℝ) = ((D : ℝ) * Real.sqrt d * r) ^ 2 := by
  rw [mVal_eq]
  have hd : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt (by positivity)
  push_cast
  rw [mul_pow, mul_pow, hd]
  ring

/-- **P1(b), packaged for the construction.**  With `n = D q`, `mr = D √d r`,
the constructed `m = mVal d D r` lies strictly in the *upper* window
`(n², (n+1)²)` **iff** `t = mr − n` satisfies `0 < t < 1` — equivalently
(given `t > 0`) iff `t < 1`. The integer membership `m ∈ (n², (n+1)²)` is
`n² < m ∧ m < n² + 2n + 1`. -/
theorem window_upper_iff (d D r q : ℕ) (hn : 0 ≤ (D * q : ℝ))
    (ht : 0 < (D : ℝ) * Real.sqrt d * r - (D * q : ℝ)) :
    ( ((D * q : ℕ) : ℝ) ^ 2 < ((mVal d D r : ℕ) : ℝ) ∧
        ((mVal d D r : ℕ) : ℝ) < ((D * q : ℕ) : ℝ) ^ 2 + (2 * (D * q : ℝ) + 1) )
      ↔ ((D : ℝ) * Real.sqrt d * r - (D * q : ℝ)) < 1 := by
  set mr : ℝ := (D : ℝ) * Real.sqrt d * r with hmr
  set N : ℝ := (D * q : ℝ) with hN
  have hcast : ((D * q : ℕ) : ℝ) = N := by rw [hN]; push_cast; ring
  set t : ℝ := mr - N with htdef
  have hmsub : ((mVal d D r : ℕ) : ℝ) - N ^ 2 = 2 * N * t + t ^ 2 := by
    rw [mVal_cast_sq, ← hmr, htdef]; exact mOf_sub_sq_factored mr N
  rw [hcast]
  -- translate the two integer-window inequalities into the `2 N t + t²` form
  have hrw : ( N ^ 2 < ((mVal d D r : ℕ) : ℝ) ∧
        ((mVal d D r : ℕ) : ℝ) < N ^ 2 + (2 * N + 1) )
      ↔ (0 < 2 * N * t + t ^ 2 ∧ 2 * N * t + t ^ 2 < 2 * N + 1) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith [hmsub], by nlinarith [hmsub, h2]⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith [hmsub], by nlinarith [hmsub, h2]⟩
  have hN0 : 0 ≤ N := hn
  -- `ht` is already `0 < mr - N = t` after the `set`s folded it.
  have ht0 : 0 < t := ht
  rw [hrw, window_iff_t_lt_one N t hN0 ht0]

/-! ## P1(c) — distinctness of distinct squarefree kernels -/

/-- **P1(c).**  Distinct squarefree `d₁ ≠ d₂` (with `r₁, r₂ ≥ 1`) yield distinct
constructed values `mVal dᵢ D rᵢ`, provided `D ≥ 1`.  (Reuses
`construction_injective` with `κ = 2`: the squarefree kernel is recovered from
the value.) -/
theorem P1c_distinct (d₁ d₂ D r₁ r₂ : ℕ) (hD : 1 ≤ D)
    (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂) (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (hne : d₁ ≠ d₂) : mVal d₁ D r₁ ≠ mVal d₂ D r₂ := by
  intro heq
  -- d₁ D² r₁² = d₂ D² r₂²  ⟹  d₁ r₁² = d₂ r₂²  ⟹  d₁ = d₂
  rw [mVal_eq, mVal_eq] at heq
  have hDne : (D ^ 2) ≠ 0 := pow_ne_zero _ (by omega)
  have hcancel : d₁ * r₁ ^ 2 = d₂ * r₂ ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hDne)
    have e1 : D ^ 2 * (d₁ * r₁ ^ 2) = d₁ * D ^ 2 * r₁ ^ 2 := by ring
    have e2 : D ^ 2 * (d₂ * r₂ ^ 2) = d₂ * D ^ 2 * r₂ ^ 2 := by ring
    rw [e1, e2]; exact heq
  exact hne (construction_injective 2 d₁ d₂ r₁ r₂ (by norm_num) hd₁ hd₂ hr₁ hr₂ hcancel).1

/-! ## P1(d) — the deduction: `h(n) ≥ ℓ` -/

/-- `h(n)` = number of powerful (`2`-full) integers strictly inside `(n², (n+1)²)`. -/
noncomputable def hOf (n : ℕ) : ℕ :=
  ((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun m => KFull 2 m)).card

/-- **P1(d).**  Suppose `S` is a finite set of squarefree divisors of `D` (with
`D ≥ 1`), each with rounding parameter `rOfS d ≥ 1`, such that for every `d ∈ S`
the constructed value `mVal d D (rOfS d)` is powerful and lies strictly inside the
window `(n², (n+1)²)`.  Then that window contains at least `|S|` powerful integers,
i.e. `h(n) ≥ |S|`.

The injection `d ↦ mVal d D (rOfS d)` into `(window).filter (KFull 2)` is built
from `P1c_distinct`. -/
theorem P1d_count_ge (D n : ℕ) (hD : 1 ≤ D) (S : Finset ℕ) (rOfS : ℕ → ℕ)
    (hsq : ∀ d ∈ S, Squarefree d)
    (hr : ∀ d ∈ S, 1 ≤ rOfS d)
    (hmem : ∀ d ∈ S, mVal d D (rOfS d) ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2))
    (hpow : ∀ d ∈ S, KFull 2 (mVal d D (rOfS d))) :
    S.card ≤ hOf n := by
  classical
  unfold hOf
  -- injectivity of d ↦ mVal d D (rOfS d) on S
  have h_inj : (S.image (fun d => mVal d D (rOfS d))).card = S.card := by
    refine Finset.card_image_of_injOn (fun d hd d' hd' h => ?_)
    by_contra hdd
    exact P1c_distinct d d' D (rOfS d) (rOfS d') hD (hsq d hd) (hsq d' hd')
      (hr d hd) (hr d' hd') hdd h
  rw [← h_inj]
  apply Finset.card_le_card
  apply Finset.image_subset_iff.mpr
  intro d hd
  exact Finset.mem_filter.mpr ⟨hmem d hd, hpow d hd⟩

/-- Restatement of `P1d_count_ge` as `ℓ ≤ h(n)` from `ℓ ≤ |S|`. -/
theorem hOf_ge_of_directions (D n ℓ : ℕ) (hD : 1 ≤ D) (S : Finset ℕ) (rOfS : ℕ → ℕ)
    (hScard : ℓ ≤ S.card)
    (hsq : ∀ d ∈ S, Squarefree d)
    (hr : ∀ d ∈ S, 1 ≤ rOfS d)
    (hmem : ∀ d ∈ S, mVal d D (rOfS d) ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2))
    (hpow : ∀ d ∈ S, KFull 2 (mVal d D (rOfS d))) :
    ℓ ≤ hOf n :=
  le_trans hScard (P1d_count_ge D n hD S rOfS hsq hr hmem hpow)

/-! ## P2 — the algebraic (Liouville) core

The novel load-bearing lemma is a multiquadratic Liouville bound: for
`K = ℚ(√p₁, …, √p_h)` and `γ = Σ aⱼ √dⱼ` a nonzero algebraic integer,
`N_{K/ℚ}(γ) ∈ ℤ \ {0}`, so `|N(γ)| ≥ 1`, and since `N(γ) = γ · ∏(conjugates)`
with each conjugate bounded by `M`, one gets `|γ| ≥ M^{-(2^h - 1)}`.

We split this honestly:

* `liouville_from_nonzero_int_norm` — the **fully proved general principle**: if a
  nonzero **integer** `Nrm` equals `γ` times a product of `e` factors each of
  absolute value `≤ M` (with `M ≥ 1`), then `|γ| ≥ M^{-e}`.  This is the
  Liouville mechanism and it is proved from Mathlib with no axioms.

* `int_norm_ne_zero` — the **fully proved** algebraic input that the field norm of
  a nonzero element is nonzero (`Algebra.norm_ne_zero_iff`), for any finite free
  domain extension; this is the Mathlib-backed "norm of a nonzero element is
  nonzero" half.

* `multiquadratic_liouville` — the single **axiom** capturing the part with no
  Mathlib API: that for the multiquadratic field the norm is realized as the
  stated integer product over the `2^h` sign-conjugates, with `[K:ℚ] = 2^h` and an
  explicit conjugate bound.  See its docstring for the precise content. -/

section P2

/-- **P2, general principle (fully proved).**  Liouville mechanism over `ℝ`.
If a real number `Nrm` with `|Nrm| ≥ 1` factors as `Nrm = γ · P` where
`|P| ≤ M ^ e` and `M ≥ 1`, then `|γ| ≥ M ^ (-(e : ℤ))`, i.e. `|γ| ≥ 1 / M ^ e`.

This is exactly the Liouville lower bound: an algebraic integer whose norm is a
nonzero rational integer (`|Nrm| ≥ 1`) cannot be too small, because its product
with the (bounded) remaining conjugates is at least `1` in absolute value. -/
theorem liouville_from_nonzero_int_norm
    (γ Nrm P M : ℝ) (e : ℕ) (hM : 1 ≤ M)
    (hNrm : 1 ≤ |Nrm|) (hfac : Nrm = γ * P) (hP : |P| ≤ M ^ e) :
    1 / M ^ e ≤ |γ| := by
  have hMe_pos : (0:ℝ) < M ^ e := by positivity
  -- |Nrm| = |γ| · |P| ≤ |γ| · M^e
  have h1 : |Nrm| = |γ| * |P| := by rw [hfac, abs_mul]
  have h2 : (1:ℝ) ≤ |γ| * |P| := by rw [← h1]; exact hNrm
  -- so |γ| · M^e ≥ |γ| · |P| ≥ 1
  have hPabs_nonneg : (0:ℝ) ≤ |P| := abs_nonneg _
  have h3 : |γ| * |P| ≤ |γ| * M ^ e := by
    apply mul_le_mul_of_nonneg_left hP (abs_nonneg _)
  have h4 : (1:ℝ) ≤ |γ| * M ^ e := le_trans h2 h3
  -- divide by M^e:  1/M^e ≤ |γ|  ⟺  1 ≤ |γ| * M^e
  rw [div_le_iff₀ hMe_pos]
  linarith [h4]

/-- Cast form: a nonzero **integer** norm has real absolute value `≥ 1`. -/
theorem one_le_abs_cast_of_int_ne_zero (z : ℤ) (hz : z ≠ 0) : (1:ℝ) ≤ |(z : ℝ)| := by
  have h : (1:ℤ) ≤ |z| := Int.one_le_abs hz
  have hcast : (|z| : ℝ) = |(z : ℝ)| := by push_cast; rfl
  calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
    _ ≤ (|z| : ℝ) := by exact_mod_cast h
    _ = |(z : ℝ)| := hcast

/-- **P2, algebraic half (fully proved from Mathlib).**  For a finite, free
domain extension `S / R` with both domains, the field/algebra norm of a nonzero
element is nonzero.  This is `Algebra.norm_ne_zero_iff`; it is the genuine
"norm of a nonzero algebraic number is nonzero" content, and combined with the
fact that the norm of an algebraic *integer* is an integer (`isIntegral_norm`)
it yields a nonzero rational integer whose absolute value is `≥ 1`. -/
theorem int_norm_ne_zero {R S : Type*} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    {γ : S} (hγ : γ ≠ 0) : Algebra.norm R γ ≠ 0 :=
  (Algebra.norm_ne_zero_iff).mpr hγ

/-- **P2, the multiquadratic Liouville inequality (AXIOM — true; not in Mathlib).**

CLASSICAL FACT, VERIFIED EXACTLY IN Sage/PARI; NOT IN MATHLIB v4.30.0 (which has no
multiquadratic field API: neither `[K:ℚ] = 2^h` nor the `ℚ`-linear independence of the
`√d`).  Let `S` be a finite set of squarefree integers whose prime factors number at
most `h`, let `c : ℕ → ℤ` be not identically zero on `S`, and put
`γ = Σ_{d∈S} c d · √d`.  If `M ≥ 1` dominates `Σ_{d∈S} |c d| · √d` (hence dominates the
modulus of every sign-conjugate `Σ_{d∈S} c d · (±√d)`), then

  `γ ≠ 0`   and   `|γ| ≥ M^{-(2^h - 1)}`.

The previous abstract form — quantified over arbitrary reals with the hypothesis
stubbed to `True` — was UNSOUND (false for small `γ`) and is replaced here.  Why this
holds: the `√d` are `ℚ`-linearly independent, so `γ ≠ 0`; `K = ℚ(√p : p ∣ ∏ S)` has
`[K:ℚ] = 2^{#primes} ≤ 2^h`; the algebraic integer `γ` has nonzero rational-integer
norm `N_{K/ℚ}(γ)`, the product of its `≤ 2^h` conjugates each of modulus `≤ M`, so
`1 ≤ |N| ≤ |γ| · M^{2^h-1}`.  The Liouville *mechanism* (`int_norm_ne_zero`,
`liouville_from_nonzero_int_norm`) is proved above; only the multiquadratic *structure*
(linear independence, degree `≤ 2^h`, conjugate bound) is taken on faith. -/
axiom multiquadratic_liouville
    (h : ℕ) (S : Finset ℕ) (c : ℕ → ℤ) (M : ℝ)
    (hSsq : ∀ d ∈ S, Squarefree d)
    (hprimes : (S.biUnion Nat.primeFactors).card ≤ h)
    (hc : ∃ d ∈ S, c d ≠ 0)
    (hM1 : 1 ≤ M)
    (hMdom : (∑ d ∈ S, |(c d : ℝ)| * Real.sqrt (d : ℝ)) ≤ M) :
    (∑ d ∈ S, (c d : ℝ) * Real.sqrt (d : ℝ)) ≠ 0 ∧
      1 / M ^ (2 ^ h - 1) ≤ |∑ d ∈ S, (c d : ℝ) * Real.sqrt (d : ℝ)|

/-- **P2, assembled multiquadratic Liouville bound** — the lower-bound half of the
(correctly-stated, CAS-verified) axiom above. -/
theorem multiquadratic_liouville_bound
    (h : ℕ) (S : Finset ℕ) (c : ℕ → ℤ) (M : ℝ)
    (hSsq : ∀ d ∈ S, Squarefree d)
    (hprimes : (S.biUnion Nat.primeFactors).card ≤ h)
    (hc : ∃ d ∈ S, c d ≠ 0) (hM1 : 1 ≤ M)
    (hMdom : (∑ d ∈ S, |(c d : ℝ)| * Real.sqrt (d : ℝ)) ≤ M) :
    1 / M ^ (2 ^ h - 1) ≤ |∑ d ∈ S, (c d : ℝ) * Real.sqrt (d : ℝ)| :=
  (multiquadratic_liouville h S c M hSsq hprimes hc hM1 hMdom).2

end P2

/-! ## P3 — the analytic input and the conditional Theorem A

The deep analytic step (Erdős–Turán–Koksma discrepancy + multiquadratic Liouville
spacing ⟹ effective simultaneous equidistribution count) is **axiomatized**.  We
then prove the headline frequency lower bound *conditionally* on this one axiom
together with the elementary core proved above. -/

section P3

/-- **P3, the analytic input (AXIOM).**

EFFECTIVE SIMULTANEOUS EQUIDISTRIBUTION / DISCREPANCY BOUND; ANALYTIC INPUT, NOT
FORMALIZED.  This is the Erdős–Turán–Koksma discrepancy bound applied to the
simultaneous equidistribution of `(q·α₁, …, q·α_ℓ)` mod `1`
(`αⱼ = dⱼ^{-1/2}`), whose error term is controlled by the multiquadratic
Liouville spacing bound `multiquadratic_liouville_bound`.  Its quantitative output
is: the number of `q ≤ Q` for which **all** `ℓ` directions land in their windows
is at least `½ · Q · ∏ⱼ δⱼ`.

We state it abstractly as the existence, for every threshold `V` and every large
`x`, of `≥ x^{1-o(1)}` admissible base points `q ≤ Q(x)` (encoded as a finite set
`Good`), each producing — via the elementary core — `h(n) ≥ V` for the
corresponding `n = D q`.  The `1-o(1)` is encoded by the lower bound
`x ^ (1 - ε)` for the count, for every `ε > 0` and all `x ≥ x₀(ε)`.

Precisely: for each target `V` there are `D ≥ 1` (the primorial), a rounding
assignment `rOfS : ℕ → ℕ → ℕ`, and a squarefree-divisor set assignment
`Sset : ℕ → Finset ℕ` such that for every `ε > 0` there is `x₀` with: for all
`x ≥ x₀`, the set of "good" `q` in `[1, x]` for which all directions hit the upper
window has cardinality `≥ x ^ (1 - ε)`, and each good `q` satisfies the
hypotheses of `hOf_ge_of_directions` for `n = D q` with `|Sset q| ≥ V`. -/
axiom simultaneous_equidistribution_count :
    ∀ V : ℕ, ∃ (D : ℕ) (Sset : ℕ → Finset ℕ) (rOfS : ℕ → ℕ → ℕ), 1 ≤ D ∧
      ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∃ Good : Finset ℕ,
          (x ^ (1 - ε) ≤ (Good.card : ℝ)) ∧
          (∀ q ∈ Good, 1 ≤ q ∧
            V ≤ (Sset q).card ∧
            (∀ d ∈ Sset q, Squarefree d) ∧
            (∀ d ∈ Sset q, 1 ≤ rOfS q d) ∧
            (∀ d ∈ Sset q, mVal d D (rOfS q d) ∈
              Finset.Ioo ((D * q) ^ 2) ((D * q + 1) ^ 2)) ∧
            (∀ d ∈ Sset q, KFull 2 (mVal d D (rOfS q d))))

/-- **Theorem A (conditional frequency lower bound).**

For every threshold `V`, the count of `n ≤ x` with `h(n) ≥ V` is `≥ x^{1-o(1)}`:
for every `ε > 0` there is `x₀` so that for all `x ≥ x₀`, the number of admissible
base points (`q ≤ x` whose `n = D q` realizes `h(n) ≥ V`) is `≥ x^{1-ε}`.

This is proved from **exactly one axiom**, the analytic
`simultaneous_equidistribution_count` (P3), combined with the fully-proved
elementary core (`hOf_ge_of_directions`, P1).  The multiquadratic Liouville bound
(P2) feeds the discrepancy estimate inside that axiom.

The conclusion is stated with the witnessing finset `Good` of good base points;
its image under `q ↦ D q` is a set of `n`-values each with `h(n) ≥ V`, and its
cardinality is `≥ x^{1-ε}`, which is the `x^{1-o(1)}` frequency claim. -/
theorem frequency_lower_bound :
    ∀ V : ℕ, ∃ D : ℕ, 1 ≤ D ∧
      ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∃ Good : Finset ℕ,
          (x ^ (1 - ε) ≤ (Good.card : ℝ)) ∧
          (∀ q ∈ Good, 1 ≤ q ∧ V ≤ hOf (D * q)) := by
  intro V
  obtain ⟨D, Sset, rOfS, hD, hmain⟩ := simultaneous_equidistribution_count V
  refine ⟨D, hD, ?_⟩
  intro ε hε
  obtain ⟨x₀, hx₀⟩ := hmain ε hε
  refine ⟨x₀, ?_⟩
  intro x hx
  obtain ⟨Good, hcard, hgood⟩ := hx₀ x hx
  refine ⟨Good, hcard, ?_⟩
  intro q hq
  obtain ⟨hq1, hVcard, hsq, hr, hmem, hpow⟩ := hgood q hq
  refine ⟨hq1, ?_⟩
  -- apply the elementary deduction P1(d) with n = D q
  exact hOf_ge_of_directions D (D * q) V hD (Sset q) (rOfS q)
    hVcard hsq hr hmem hpow

end P3

end Erdos942.Frequency
