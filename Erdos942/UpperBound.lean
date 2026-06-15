import Erdos942.Core
import Erdos942.Construction

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Erdős #942 — the upper bound `h(n) ≪_ε n^{6/25+ε}` (elementary reduction)

This file formalizes the **elementary reduction** behind the upper bound
`h(n) = #{ powerful m : n² < m < (n+1)² } ≪_ε n^{6/25+ε}`.

A powerful (squarefull) number is `KFull 2 m` (every prime dividing `m` does so to
power `≥ 2`); we reuse that predicate from `Core.lean`, do not redefine it.

What is **proved with zero `sorry`** here (standard axioms only):

* `powerful_rep` — every powerful `m ≥ 1` has `m = a² · b³` with `b` squarefree
  and `a, b ≥ 1` (existence; classical `a²b³` decomposition).
* `at_most_one_per_b` — for fixed `b ≥ 2`, at most one `a ≥ 1` with
  `n² < a²·b³ < (n+1)²`.
* `at_most_one_per_a` — for fixed `a ≥ 1`, at most one `b ≥ 1` with
  `n² < a²·b³ < (n+1)²`.
* `min_pow_le` — the split: if `m = a²·b³`, `a,b ≥ 1`, `n² < m < (n+1)²` then
  `min a b ^ 5 ≤ (n+1)²` (so the smaller parameter is `≤ (n+1)^{2/5}`).
* `hUp` — the count `h(n)`, as a `Finset.card`, matching the convention in
  `Construction.lean`/`Frequency.lean` (`KFull 2`-filter of `Ioo (n²) ((n+1)²)`).
* `hUp_le_aspects` — the **reduction inequality**: `h(n)` is bounded by the number
  of admissible "small `b`" values plus the number of admissible "small `a`"
  values, via the injections `m ↦ b` and `m ↦ a`.

The single deep analytic input — the Filaseta–Trifonov "integer points close to a
curve" count, not in Mathlib — is isolated as the clearly-labeled axiom
`ft_curve_count`.  The headline `upper_bound` is then proved from exactly that
axiom plus the elementary reduction.
-/

namespace Erdos942.UpperBound

/-! ## §1  The `a² b³` representation of a powerful number -/

/-- **Representation lemma.**  Every powerful `m ≥ 1` can be written as
`m = a² · b³` with `b` squarefree and `a, b ≥ 1`.

Proof: write `m = s · c²` with `s` squarefree (`Nat.sq_mul_squarefree`).  For each
prime `p ∣ s` powerfulness forces `vₚ(m) = 2 vₚ(c) + 1 ≥ 2`, hence `vₚ(c) ≥ 1 = vₚ(s)`;
so `s ∣ c`, write `c = s · a`.  Then `m = s · (s a)² = a² · s³`; take `b = s`. -/
theorem powerful_rep (m : ℕ) (hm : 1 ≤ m) (hpow : KFull 2 m) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ Squarefree b ∧ m = a ^ 2 * b ^ 3 := by
  have hm0 : m ≠ 0 := by omega
  -- m = c² · s with s squarefree, c, s ≥ 1
  obtain ⟨s, c, hs0, hc0, hcs, hsq⟩ := Nat.sq_mul_squarefree_of_pos (n := m) (by omega)
  -- s ∣ c, prime by prime
  have hsc : s ∣ c := by
    rw [← Nat.factorization_le_iff_dvd hs0.ne' hc0.ne']
    intro p
    by_cases hp : p.Prime
    · -- valuation comparison at the prime p
      by_cases hps : p ∣ s
      · -- vₚ(s) = 1 (s squarefree); show vₚ(c) ≥ 1
        have hvs1 : s.factorization p = 1 := by
          have hle : s.factorization p ≤ 1 := hsq.natFactorization_le_one p
          have hge : 1 ≤ s.factorization p :=
            (Nat.Prime.dvd_iff_one_le_factorization hp hs0.ne').mp hps
          omega
        -- p ∣ m, so by powerfulness p² ∣ m, i.e. vₚ(m) ≥ 2
        have hpm : p ∣ m := by rw [← hcs]; exact hps.mul_left (c ^ 2)
        have hp2m : p ^ 2 ∣ m := hpow p hp hpm
        have hvm2 : 2 ≤ m.factorization p :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp hm0).mp hp2m
        -- vₚ(m) = 2 vₚ(c) + vₚ(s) = 2 vₚ(c) + 1
        have hfac : m.factorization p = 2 * c.factorization p + s.factorization p := by
          rw [← hcs, Nat.factorization_mul (pow_ne_zero 2 hc0.ne') hs0.ne']
          simp [Nat.factorization_pow]
        have hvc : 1 ≤ c.factorization p := by omega
        -- conclude vₚ(s) = 1 ≤ vₚ(c)
        rw [hvs1]; exact hvc
      · -- p ∤ s ⟹ vₚ(s) = 0 ≤ vₚ(c)
        have hz : s.factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          exact Or.inr (Or.inl hps)
        rw [hz]; exact Nat.zero_le _
    · have hz : s.factorization p = 0 := Nat.factorization_eq_zero_of_not_prime _ hp
      rw [hz]; exact Nat.zero_le _
  obtain ⟨a, ha⟩ := hsc
  have ha0 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · simp [h] at ha; omega
    · exact h
  refine ⟨a, s, ha0, hs0, hsq, ?_⟩
  -- m = c² · s = (s a)² · s = a² · s³
  rw [← hcs, ha]; ring

/-! ## §2  At most one `a` per `b`, at most one `b` per `a` -/

/-- **At-most-one-per-`b`.**  For a fixed `b ≥ 2`, there is at most one `a ≥ 1`
with `n² < a²·b³ < (n+1)²`.

If `a₁ < a₂` both worked, then `a₂²·b³ − a₁²·b³ ≥ (2a₁+1)·b³ ≥ (2a₁+1)·8`, while
`a₁²·b³ > n²` gives `(2a₁+1)·b³ > 2·a₁·b³ ≥ … ` ; concretely both values lie in the
window of width `2n+1`, and the gap already exceeds `2n+1`. -/
theorem at_most_one_per_b (n b a₁ a₂ : ℕ) (hb : 2 ≤ b) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (h1 : n ^ 2 < a₁ ^ 2 * b ^ 3) (h1' : a₁ ^ 2 * b ^ 3 < (n + 1) ^ 2)
    (h2 : n ^ 2 < a₂ ^ 2 * b ^ 3) (h2' : a₂ ^ 2 * b ^ 3 < (n + 1) ^ 2) :
    a₁ = a₂ := by
  by_contra hne
  -- WLOG a₁ < a₂
  wlog hlt : a₁ < a₂ generalizing a₁ a₂
  · exact this a₂ a₁ ha₂ ha₁ h2 h2' h1 h1' (Ne.symm hne) (by omega)
  -- n = 0 is vacuous (h1' would force a₁²b³ = 0).
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    have : 1 ≤ a₁ ^ 2 * b ^ 3 := by
      have : 0 < a₁ ^ 2 * b ^ 3 := by positivity
      omega
    simp at h1'; omega
  -- a₂ ≥ a₁ + 1 so a₂² ≥ a₁² + 2a₁ + 1 = a₁² + (2a₁+1)
  have hsq : a₁ ^ 2 + (2 * a₁ + 1) ≤ a₂ ^ 2 := by nlinarith [hlt]
  -- multiply by b³ : gap = (a₂²−a₁²)b³ ≥ (2a₁+1)b³
  have hgap : a₁ ^ 2 * b ^ 3 + (2 * a₁ + 1) * b ^ 3 ≤ a₂ ^ 2 * b ^ 3 := by nlinarith [hsq]
  have hb3 : 8 ≤ b ^ 3 := by
    have := Nat.pow_le_pow_left hb 3; simpa using this
  -- ((2a₁+1)b³)² > (2n+1)² :  4a₁²b³·b³ > 4n²·8 = 32n² ≥ (2n+1)²
  have hprod : 32 * n ^ 2 < 4 * (a₁ ^ 2 * b ^ 3) * b ^ 3 := by
    have hmul : (a₁ ^ 2 * b ^ 3) * 8 ≤ (a₁ ^ 2 * b ^ 3) * b ^ 3 :=
      Nat.mul_le_mul (le_refl _) hb3
    nlinarith [h1, hmul]
  have hge : 4 * (a₁ ^ 2 * b ^ 3) * b ^ 3 ≤ ((2 * a₁ + 1) * b ^ 3) ^ 2 := by ring_nf; nlinarith [sq_nonneg a₁, sq_nonneg b]
  have hwn : (2 * n + 1) ^ 2 ≤ 32 * n ^ 2 := by nlinarith [hn1]
  have hsqgap : (2 * n + 1) ^ 2 < ((2 * a₁ + 1) * b ^ 3) ^ 2 := by
    calc (2 * n + 1) ^ 2 ≤ 32 * n ^ 2 := hwn
      _ < 4 * (a₁ ^ 2 * b ^ 3) * b ^ 3 := hprod
      _ ≤ ((2 * a₁ + 1) * b ^ 3) ^ 2 := hge
  -- hence (2a₁+1)b³ > 2n+1
  have hgap2 : 2 * n + 1 < (2 * a₁ + 1) * b ^ 3 := by
    by_contra hle
    have hle' : (2 * a₁ + 1) * b ^ 3 ≤ 2 * n + 1 := not_lt.mp hle
    exact absurd hsqgap (by nlinarith [Nat.pow_le_pow_left hle' 2])
  -- Now a₂²b³ ≥ a₁²b³ + (2a₁+1)b³ > n² + (2n+1) = (n+1)², contradicting h2'
  nlinarith [hgap, hgap2, h1, h2']

/-- **At-most-one-per-`a`.**  For a fixed `a ≥ 1`, there is at most one `b ≥ 1`
with `n² < a²·b³ < (n+1)²`.

Consecutive `b` change `a²b³` by `a²((b+1)³ − b³) = a²(3b²+3b+1)`; combined with
`a²b³ > n²` this gap exceeds the window width `2n+1`. -/
theorem at_most_one_per_a (n a b₁ b₂ : ℕ) (ha : 1 ≤ a) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (h1 : n ^ 2 < a ^ 2 * b₁ ^ 3) (h1' : a ^ 2 * b₁ ^ 3 < (n + 1) ^ 2)
    (h2 : n ^ 2 < a ^ 2 * b₂ ^ 3) (h2' : a ^ 2 * b₂ ^ 3 < (n + 1) ^ 2) :
    b₁ = b₂ := by
  by_contra hne
  wlog hlt : b₁ < b₂ generalizing b₁ b₂
  · exact this b₂ b₁ hb₂ hb₁ h2 h2' h1 h1' (Ne.symm hne) (by omega)
  -- n = 0 is vacuous: h1' forces a²b₁³ = 0, contradicting a,b₁ ≥ 1.
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    have : 1 ≤ a ^ 2 * b₁ ^ 3 := by
      have : 0 < a ^ 2 * b₁ ^ 3 := by positivity
      omega
    simp at h1'; omega
  -- b₂ ≥ b₁ + 1 ⟹ b₂³ ≥ (b₁+1)³ = b₁³ + (3b₁²+3b₁+1)
  have hb2ge : b₁ + 1 ≤ b₂ := hlt
  have hcube : b₁ ^ 3 + (3 * b₁ ^ 2 + 3 * b₁ + 1) ≤ b₂ ^ 3 := by
    have := Nat.pow_le_pow_left hb2ge 3
    nlinarith [this]
  have hgap : a ^ 2 * b₁ ^ 3 + a ^ 2 * (3 * b₁ ^ 2 + 3 * b₁ + 1) ≤ a ^ 2 * b₂ ^ 3 := by
    nlinarith [hcube]
  -- both m's in a width-(2n+1) window ⟹ gap < 2n+1 ⟹ 3·a²b₁² ≤ 2n  (call hI)
  have hwin : a ^ 2 * (3 * b₁ ^ 2 + 3 * b₁ + 1) < 2 * n + 1 := by
    have e1 : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
    nlinarith [hgap, h1, h2', e1]
  have hI : 3 * (a ^ 2 * b₁ ^ 2) ≤ 2 * n := by nlinarith [hwin]
  -- multiply hI by b₁:  3·a²b₁³ ≤ 2n·b₁, and n² < a²b₁³ ⟹ 3n² < 2n·b₁ ⟹ 3n + 1 ≤ 2 b₁
  have hIb : 3 * (a ^ 2 * b₁ ^ 3) ≤ 2 * n * b₁ := by nlinarith [Nat.mul_le_mul_right b₁ hI]
  have h3n : 3 * n + 1 ≤ 2 * b₁ := by nlinarith [hIb, h1, hn1]
  -- b₁³ < (n+1)² (since a ≥ 1), so (3n+1)³ ≤ (2b₁)³ = 8 b₁³ < 8(n+1)², contradiction
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  have hb1cube : b₁ ^ 3 < (n + 1) ^ 2 := by
    have : b₁ ^ 3 ≤ a ^ 2 * b₁ ^ 3 := Nat.le_mul_of_pos_left _ ha2
    omega
  have hfin : (3 * n + 1) ^ 3 ≤ 8 * b₁ ^ 3 := by nlinarith [Nat.pow_le_pow_left h3n 3]
  nlinarith [hfin, hb1cube, hn1]

/-! ## §3  The split: the smaller parameter is `≤ (n+1)^{2/5}` -/

/-- **The split (integer form).**  If `m = a²·b³` with `a,b ≥ 1` and
`n² < m < (n+1)²`, then `min a b ^ 5 ≤ (n+1)²`.

Indeed `min a b ^ 5 = min a b ^ 2 · min a b ^ 3 ≤ a² · b³ = m < (n+1)²`, hence
`min a b ^ 5 ≤ (n+1)² − 1 ≤ (n+1)²`; we keep the clean `≤ (n+1)²` form.  This is the
elementary statement that the smaller of `a, b` is `≤ (n+1)^{2/5}`. -/
theorem min_pow_le (n a b : ℕ) (_ha : 1 ≤ a) (_hb : 1 ≤ b)
    (_h1 : n ^ 2 < a ^ 2 * b ^ 3) (h2 : a ^ 2 * b ^ 3 < (n + 1) ^ 2) :
    min a b ^ 5 ≤ (n + 1) ^ 2 := by
  have hle : min a b ^ 5 ≤ a ^ 2 * b ^ 3 := by
    have hA : min a b ≤ a := min_le_left _ _
    have hB : min a b ≤ b := min_le_right _ _
    calc min a b ^ 5 = min a b ^ 2 * min a b ^ 3 := by ring
      _ ≤ a ^ 2 * b ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_left hA 2) (Nat.pow_le_pow_left hB 3)
  omega

/-! ## §4  The count `h(n)` and the reduction inequality

We package `h(n)` exactly as in `Frequency.lean`/`Construction.lean`: the number of
`KFull 2` integers strictly inside the window `Ioo (n²) ((n+1)²)`.

The two "aspect" finsets count the *small parameter* of each powerful `m` in the
window: `bAspect n` ranges over the admissible small `b` (when `b ≤ a`), `aAspect n`
over the admissible small `a` (when `a < b`).  Both are finsets of values
`≤ (n+1)²`.  By §2–§3 the map `m ↦ (its small parameter)` is injective into
`bAspect n ∪ aAspect n`, giving `h(n) ≤ #bAspect + #aAspect`. -/

/-- `h(n)` — the number of powerful integers strictly between `n²` and `(n+1)²`.
Same convention as `Erdos942.Frequency.hOf`. -/
noncomputable def hUp (n : ℕ) : ℕ :=
  ((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun m => KFull 2 m)).card

/-- The admissible **`b`-aspect** values: those `b` with `2 ≤ b`, `b^5 ≤ (n+1)²`,
for which some `a ≥ 1` realizes a powerful `m = a²b³` in the window with `b ≤ a`. -/
noncomputable def bAspect (n : ℕ) : Finset ℕ :=
  (Finset.range ((n + 1) ^ 2 + 1)).filter (fun b =>
    2 ≤ b ∧ b ^ 5 ≤ (n + 1) ^ 2 ∧
      ∃ a, 1 ≤ a ∧ b ≤ a ∧ n ^ 2 < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 < (n + 1) ^ 2)

/-- The admissible **`a`-aspect** values: those `a` with `1 ≤ a`, `a^5 ≤ (n+1)²`,
for which some `b ≥ 1` realizes a powerful `m = a²b³` in the window with `a < b`. -/
noncomputable def aAspect (n : ℕ) : Finset ℕ :=
  (Finset.range ((n + 1) ^ 2 + 1)).filter (fun a =>
    1 ≤ a ∧ a ^ 5 ≤ (n + 1) ^ 2 ∧
      ∃ b, 1 ≤ b ∧ a < b ∧ n ^ 2 < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 < (n + 1) ^ 2)

/-- For a powerful `m` strictly between consecutive squares, `m` is not a perfect
square; consequently in its representation `m = a²b³` we cannot have `b = 1`. -/
theorem not_square_in_window (n m : ℕ) (h1 : n ^ 2 < m) (h2 : m < (n + 1) ^ 2) :
    ∀ a, m ≠ a ^ 2 := by
  intro a ha
  subst ha
  -- n² < a² < (n+1)² ⟹ n < a < n+1, impossible
  have hna : n < a := by nlinarith [h1]
  have han : a < n + 1 := by nlinarith [h2]
  omega

/-- **The reduction inequality.**  `h(n) ≤ #bAspect(n) + #aAspect(n)`.

Each powerful `m` in the window has a representation `m = a²b³` (`powerful_rep`)
with `a, b ≥ 1`, `b` squarefree.  Since `m` is not a perfect square
(`not_square_in_window`), `b ≥ 2` when `b ≤ a` is the controlling side, and the
smaller parameter is `≤ (n+1)^{2/5}` (`min_pow_le`).  We send `m` to its small
parameter: into `bAspect` if `b ≤ a` (then `b ≥ 2`), into `aAspect` if `a < b`.
The map is injective on each side by `at_most_one_per_b` / `at_most_one_per_a`.
Over-counting (a value could in principle appear on both sides) only helps `≤`. -/
theorem hUp_le_aspects (n : ℕ) :
    hUp n ≤ (bAspect n).card + (aAspect n).card := by
  classical
  unfold hUp
  -- choose a representation for each powerful m in the window
  set W := (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun m => KFull 2 m) with hW
  -- For each m ∈ W, pick (a,b); define the "small parameter assignment".
  -- We build an injection W ↪ bAspect n ∪' aAspect n by mapping m to a chosen small param,
  -- tagged by which side. Use a sum type via Finset card of a disjoint-union target.
  -- Concretely: define g : ℕ → ℕ × Bool sending m to (small param, side).
  -- side = false: b-aspect (value b); side = true: a-aspect (value a).
  have key : ∀ m ∈ W, ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ Squarefree b ∧ m = a ^ 2 * b ^ 3 ∧
      n ^ 2 < m ∧ m < (n + 1) ^ 2 := by
    intro m hm
    rw [hW, Finset.mem_filter, Finset.mem_Ioo] at hm
    obtain ⟨⟨hlo, hhi⟩, hpow⟩ := hm
    have hm1 : 1 ≤ m := by omega
    obtain ⟨a, b, ha, hb, hsq, heq⟩ := powerful_rep m hm1 hpow
    exact ⟨a, b, ha, hb, hsq, heq, hlo, hhi⟩
  -- choice function
  choose A B hA hB hsqB heq hlo hhi using key
  -- the tagged small parameter
  set g : ℕ → ℕ × Bool := fun m =>
    if hmem : m ∈ W then
      (if B m hmem ≤ A m hmem then (B m hmem, false) else (A m hmem, true))
    else (0, true) with hg
  -- the image target
  set Tb : Finset (ℕ × Bool) := (bAspect n).image (fun b => (b, false)) with hTb
  set Ta : Finset (ℕ × Bool) := (aAspect n).image (fun a => (a, true)) with hTa
  -- g maps W into Tb ∪ Ta
  have hmaps : ∀ m ∈ W, g m ∈ Tb ∪ Ta := by
    intro m hm
    have hgm : g m = (if B m hm ≤ A m hm then (B m hm, false) else (A m hm, true)) := by
      simp only [hg, dif_pos hm]
    have hbnot1 : B m hm ≠ 1 := by
      intro hb1
      -- then m = A² · 1 = A², a perfect square, impossible
      exact not_square_in_window n m (hlo m hm) (hhi m hm) (A m hm)
        (by have e := heq m hm; rw [hb1] at e; simpa using e)
    by_cases hcase : B m hm ≤ A m hm
    · -- b-aspect; B m hm ≥ 2
      have hb2 : 2 ≤ B m hm := by
        have := hB m hm; omega
      have hmin : min (A m hm) (B m hm) ^ 5 ≤ (n + 1) ^ 2 :=
        min_pow_le n (A m hm) (B m hm) (hA m hm) (hB m hm)
          (by rw [← heq m hm]; exact hlo m hm) (by rw [← heq m hm]; exact hhi m hm)
      have hminB : min (A m hm) (B m hm) = B m hm := min_eq_right hcase
      have hb5 : B m hm ^ 5 ≤ (n + 1) ^ 2 := by rw [← hminB]; exact hmin
      have hmemb : B m hm ∈ bAspect n := by
        rw [bAspect, Finset.mem_filter, Finset.mem_range]
        have hble : B m hm ≤ B m hm ^ 5 := Nat.le_self_pow (by norm_num) _
        refine ⟨by omega, hb2, hb5, A m hm, hA m hm, hcase, ?_, ?_⟩
        · rw [← heq m hm]; exact hlo m hm
        · rw [← heq m hm]; exact hhi m hm
      rw [hgm, if_pos hcase]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨_, hmemb, rfl⟩))
    · -- a-aspect; A m hm < B m hm
      replace hcase : A m hm < B m hm := Nat.lt_of_not_le hcase
      have hmin : min (A m hm) (B m hm) ^ 5 ≤ (n + 1) ^ 2 :=
        min_pow_le n (A m hm) (B m hm) (hA m hm) (hB m hm)
          (by rw [← heq m hm]; exact hlo m hm) (by rw [← heq m hm]; exact hhi m hm)
      have hminA : min (A m hm) (B m hm) = A m hm := min_eq_left hcase.le
      have ha5 : A m hm ^ 5 ≤ (n + 1) ^ 2 := by rw [← hminA]; exact hmin
      have hmema : A m hm ∈ aAspect n := by
        rw [aAspect, Finset.mem_filter, Finset.mem_range]
        have hale : A m hm ≤ A m hm ^ 5 := Nat.le_self_pow (by norm_num) _
        refine ⟨by omega, hA m hm, ha5, B m hm, hB m hm, hcase, ?_, ?_⟩
        · rw [← heq m hm]; exact hlo m hm
        · rw [← heq m hm]; exact hhi m hm
      rw [hgm, if_neg (by omega)]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨_, hmema, rfl⟩))
  -- g is injective on W
  have hinj : ∀ m₁ ∈ W, ∀ m₂ ∈ W, g m₁ = g m₂ → m₁ = m₂ := by
    intro m₁ hm₁ m₂ hm₂ hgeq
    have hg1 : g m₁ = (if B m₁ hm₁ ≤ A m₁ hm₁ then (B m₁ hm₁, false) else (A m₁ hm₁, true)) := by
      simp only [hg, dif_pos hm₁]
    have hg2 : g m₂ = (if B m₂ hm₂ ≤ A m₂ hm₂ then (B m₂ hm₂, false) else (A m₂ hm₂, true)) := by
      simp only [hg, dif_pos hm₂]
    rw [hg1, hg2] at hgeq
    by_cases hc1 : B m₁ hm₁ ≤ A m₁ hm₁ <;> by_cases hc2 : B m₂ hm₂ ≤ A m₂ hm₂
    · -- both b-side: equal b
      rw [if_pos hc1, if_pos hc2, Prod.mk.injEq] at hgeq
      have hbeq : B m₁ hm₁ = B m₂ hm₂ := hgeq.1
      -- b ≥ 2 on both
      have hb1' : 2 ≤ B m₁ hm₁ := by
        have hge1 := hB m₁ hm₁
        rcases Nat.lt_or_ge (B m₁ hm₁) 2 with h | h
        · exfalso
          have hb1 : B m₁ hm₁ = 1 := by omega
          exact not_square_in_window n m₁ (hlo m₁ hm₁) (hhi m₁ hm₁) (A m₁ hm₁)
            (by have e := heq m₁ hm₁; rw [hb1] at e; simpa using e)
        · exact h
      -- apply at_most_one_per_b with b = B m₁ hm₁ = B m₂ hm₂
      have haeq : A m₁ hm₁ = A m₂ hm₂ :=
        at_most_one_per_b n (B m₁ hm₁) (A m₁ hm₁) (A m₂ hm₂) hb1' (hA m₁ hm₁) (hA m₂ hm₂)
          (by rw [← heq m₁ hm₁]; exact hlo m₁ hm₁)
          (by rw [← heq m₁ hm₁]; exact hhi m₁ hm₁)
          (by rw [hbeq, ← heq m₂ hm₂]; exact hlo m₂ hm₂)
          (by rw [hbeq, ← heq m₂ hm₂]; exact hhi m₂ hm₂)
      rw [heq m₁ hm₁, heq m₂ hm₂, haeq, hbeq]
    · rw [if_pos hc1, if_neg hc2, Prod.mk.injEq] at hgeq
      exact absurd hgeq.2 (by simp)
    · rw [if_neg hc1, if_pos hc2, Prod.mk.injEq] at hgeq
      exact absurd hgeq.2 (by simp)
    · -- both a-side: equal a
      rw [if_neg hc1, if_neg hc2, Prod.mk.injEq] at hgeq
      have haeq : A m₁ hm₁ = A m₂ hm₂ := hgeq.1
      have hbeq : B m₁ hm₁ = B m₂ hm₂ :=
        at_most_one_per_a n (A m₁ hm₁) (B m₁ hm₁) (B m₂ hm₂) (hA m₁ hm₁) (hB m₁ hm₁) (hB m₂ hm₂)
          (by rw [← heq m₁ hm₁]; exact hlo m₁ hm₁)
          (by rw [← heq m₁ hm₁]; exact hhi m₁ hm₁)
          (by rw [haeq, ← heq m₂ hm₂]; exact hlo m₂ hm₂)
          (by rw [haeq, ← heq m₂ hm₂]; exact hhi m₂ hm₂)
      rw [heq m₁ hm₁, heq m₂ hm₂, haeq, hbeq]
  -- so |W| ≤ |Tb ∪ Ta| ≤ |Tb| + |Ta| = |bAspect| + |aAspect|
  have hcard : W.card ≤ (Tb ∪ Ta).card :=
    Finset.card_le_card_of_injOn g hmaps hinj
  calc W.card ≤ (Tb ∪ Ta).card := hcard
    _ ≤ Tb.card + Ta.card := Finset.card_union_le _ _
    _ = (bAspect n).card + (aAspect n).card := by
        rw [hTb, hTa, Finset.card_image_of_injOn, Finset.card_image_of_injOn]
        · intro x _ y _ h; exact (Prod.mk.injEq _ _ _ _).mp h |>.1
        · intro x _ y _ h; exact (Prod.mk.injEq _ _ _ _).mp h |>.1

/-! ## §5  The analytic axiom and the headline upper bound -/

/-- **The Filaseta–Trifonov curve-count input (AXIOM — classical, not in Mathlib).**

This is Filaseta–Trifonov, "The distribution of squarefull numbers in short
intervals" / "On gaps between squarefull numbers" (the "integer points close to a
curve" method, Proc. London Math. Soc. (3) 73 (1996), Thm 4.1), applied dyadically.

Counting the powerful `m ∈ (n², (n+1)²)` via the `m = a²b³` decomposition, the
admissible small parameter (`b` in the `b`-aspect, `a` in the `a`-aspect, each
`≤ (n+1)^{2/5}` by `min_pow_le`) is constrained to be an integer near the curve
`x ↦ ⌊√(N/x³)⌋` (resp. `x ↦ ⌊(N/x²)^{1/3}⌋`) over a dyadic range.  The
Filaseta–Trifonov second-difference / divided-difference machinery bounds the number
of such near-curve integer points; summed dyadically the worst block sits at
`a ≍ b ≍ n^{2/5}` and yields the exponent `6/25`.  This analytic count is **not** in
Mathlib v4.30.0, so we take exactly this cardinality bound as a single axiom — in the
same spirit as the ETK/multiquadratic axioms documented in `Frequency.lean`.

We state it as: for every `ε > 0` there is a constant `C > 0` bounding **both**
aspect counts by `C · n^{6/25+ε}` (one combined axiom; either aspect alone is
dominated by the same bound). -/
axiom ft_curve_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ((bAspect n).card : ℝ) ≤ C * (n : ℝ) ^ ((6 : ℝ) / 25 + ε) ∧
      ((aAspect n).card : ℝ) ≤ C * (n : ℝ) ^ ((6 : ℝ) / 25 + ε)

/-- **Upper bound (Erdős #942, conditional on the Filaseta–Trifonov count).**

For every `ε > 0` there is `C > 0` with `h(n) ≤ C · n^{6/25+ε}` for all `n`.

Proved from the elementary reduction `hUp_le_aspects` (which is on the standard
axioms only) together with the single analytic axiom `ft_curve_count`. -/
theorem upper_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (hUp n : ℝ) ≤ C * (n : ℝ) ^ ((6 : ℝ) / 25 + ε) := by
  intro ε hε
  obtain ⟨C, hC0, hCbound⟩ := ft_curve_count ε hε
  refine ⟨2 * C, by linarith, ?_⟩
  intro n
  obtain ⟨hb, ha⟩ := hCbound n
  have hred : (hUp n : ℝ) ≤ ((bAspect n).card : ℝ) + ((aAspect n).card : ℝ) := by
    have h := hUp_le_aspects n
    have : (hUp n : ℝ) ≤ (((bAspect n).card + (aAspect n).card : ℕ) : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_add] at this
  calc (hUp n : ℝ) ≤ ((bAspect n).card : ℝ) + ((aAspect n).card : ℝ) := hred
    _ ≤ C * (n : ℝ) ^ ((6 : ℝ) / 25 + ε) + C * (n : ℝ) ^ ((6 : ℝ) / 25 + ε) := by
        exact add_le_add hb ha
    _ = 2 * C * (n : ℝ) ^ ((6 : ℝ) / 25 + ε) := by ring

end Erdos942.UpperBound
