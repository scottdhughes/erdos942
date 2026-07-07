import Erdos942.Core
import Erdos942.UpperBound

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Erdős #942 — the unconditional global count `#{powerful m ≤ x} ≤ 3√x`

This file proves an **unconditional** global upper bound for the number of powerful
(squarefull) numbers up to `x`:

`#{ m : 1 ≤ m ≤ x, KFull 2 m } ≤ 3 · √x`.

The proof is the classical one:

1. Every powerful `m ≥ 1` is `m = a²·b³` with `b` squarefree and `a,b ≥ 1`
   (`Erdos942.UpperBound.powerful_rep`).  The pair `(a,b)` is *determined* by `m`
   because `m = b·(a·b)²`, so `construction_injective` (κ=2) applies.  Hence the
   powerful count is bounded by the number of admissible pairs `(a,b)` with
   `a²·b³ ≤ x`, `a,b ≥ 1`.
2. Summing over `b`, the number of admissible `a` for a fixed `b` is
   `Nat.sqrt (x / b³)`, so the pair count is `≤ ∑_{b=1}^{x} Nat.sqrt (x / b³)`.
3. Casting to `ℝ`, `Nat.sqrt (x/b³) ≤ √x · b^{-3/2}`, and
   `∑_{b=1}^{N} b^{-3/2} ≤ 3` uniformly in `N` (telescoping), giving the bound.

Zero `sorry`, zero `native_decide`, standard axioms only.
-/

namespace Erdos942.GlobalCount

open Erdos942 Erdos942.UpperBound

/-! ## §1  The powerful count as a `Finset.card` and the pair injection -/

/-- The set of powerful numbers in `[1, x]`. -/
noncomputable def powerfulSet (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun m => KFull 2 m)

/-- The index set of admissible pairs `(a, b)` with `a²·b³ ≤ x` and `a, b ≥ 1`. -/
noncomputable def pairSet (x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 x)).filter
    (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ x)

/-- The injection `m ↦ (a, b)` where `m = a²·b³`.  Well-defined via choice. -/
noncomputable def toPair (m : ℕ) : ℕ × ℕ :=
  if h : 1 ≤ m ∧ KFull 2 m then
    (Classical.choose (powerful_rep m h.1 h.2),
     Classical.choose (Classical.choose_spec (powerful_rep m h.1 h.2)))
  else (0, 0)

/-- Key spec of `toPair`: for powerful `m ≥ 1`, `toPair m = (a, b)` with
`1 ≤ a`, `1 ≤ b`, `Squarefree b`, and `m = a²·b³`. -/
theorem toPair_spec (m : ℕ) (hm : 1 ≤ m) (hpow : KFull 2 m) :
    1 ≤ (toPair m).1 ∧ 1 ≤ (toPair m).2 ∧ Squarefree (toPair m).2 ∧
      m = (toPair m).1 ^ 2 * (toPair m).2 ^ 3 := by
  have h : 1 ≤ m ∧ KFull 2 m := ⟨hm, hpow⟩
  set a := Classical.choose (powerful_rep m hm hpow) with ha_def
  have ha := Classical.choose_spec (powerful_rep m hm hpow)
  set b := Classical.choose ha with hb_def
  have hb := Classical.choose_spec ha
  -- unfold toPair
  have htp : toPair m = (a, b) := by
    unfold toPair
    rw [dif_pos h]
  rw [htp]
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩

/-- Injectivity of `toPair` on the powerful set: if two powerful numbers map to the
same pair, they are equal.  (Trivial, since `m = a²·b³`.)  More usefully, the map is
injective on `powerfulSet x`. -/
theorem toPair_injOn (x : ℕ) :
    Set.InjOn toPair (powerfulSet x : Set ℕ) := by
  intro m₁ hm₁ m₂ hm₂ hEq
  simp only [powerfulSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hm₁ hm₂
  obtain ⟨⟨hm₁a, _⟩, hp₁⟩ := hm₁
  obtain ⟨⟨hm₂a, _⟩, hp₂⟩ := hm₂
  have s₁ := toPair_spec m₁ hm₁a hp₁
  have s₂ := toPair_spec m₂ hm₂a hp₂
  rw [s₁.2.2.2, s₂.2.2.2, hEq]

/-- The pair image of a powerful `m ≤ x` lands in `pairSet x`. -/
theorem toPair_mem_pairSet (x m : ℕ) (hmem : m ∈ powerfulSet x) :
    toPair m ∈ pairSet x := by
  simp only [powerfulSet, Finset.mem_filter, Finset.mem_Icc] at hmem
  obtain ⟨⟨hm1, hmx⟩, hpow⟩ := hmem
  have s := toPair_spec m hm1 hpow
  obtain ⟨ha1, hb1, _, hrep⟩ := s
  set a := (toPair m).1 with ha_def
  set b := (toPair m).2 with hb_def
  have hb3 : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb1
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha1
  have hax : a ≤ x := by
    calc a ≤ a ^ 2 := Nat.le_self_pow (by norm_num) a
      _ = a ^ 2 * 1 := (mul_one _).symm
      _ ≤ a ^ 2 * b ^ 3 := Nat.mul_le_mul_left _ hb3
      _ = m := hrep.symm
      _ ≤ x := hmx
  have hbx : b ≤ x := by
    calc b ≤ b ^ 3 := Nat.le_self_pow (by norm_num) b
      _ = 1 * b ^ 3 := (one_mul _).symm
      _ ≤ a ^ 2 * b ^ 3 := Nat.mul_le_mul_right _ ha2
      _ = m := hrep.symm
      _ ≤ x := hmx
  simp only [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨⟨ha1, hax⟩, ⟨hb1, hbx⟩⟩, ha1, hb1, ?_⟩
  rw [← hrep]; exact hmx

/-- Step 1 conclusion: the powerful count is bounded by the pair count. -/
theorem powerful_card_le_pair_card (x : ℕ) :
    (powerfulSet x).card ≤ (pairSet x).card := by
  apply Finset.card_le_card_of_injOn toPair
  · intro m hm; exact toPair_mem_pairSet x m hm
  · exact toPair_injOn x

/-! ## §2  Counting pairs: fibering over `b` -/

/-- The `b`-fiber of `pairSet x`: pairs `(a, b)` with fixed second coordinate `b`. -/
theorem pairSet_fiber_card_le (x b : ℕ) :
    ((pairSet x).filter (fun p => p.2 = b)).card ≤ Nat.sqrt (x / b ^ 3) := by
  -- Map each surviving pair `(a, b)` to `a`; it lands in `Icc 1 (Nat.sqrt (x/b³))`.
  by_cases hb : 1 ≤ b
  · have hb3 : 0 < b ^ 3 := by positivity
    have hcard : ((pairSet x).filter (fun p => p.2 = b)).card
        ≤ (Finset.Icc 1 (Nat.sqrt (x / b ^ 3))).card := by
      apply Finset.card_le_card_of_injOn (fun p => p.1)
      · intro p hp
        simp only [Finset.mem_coe] at hp
        simp only [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        obtain ⟨⟨⟨⟨ha1, _⟩, _⟩, _, _, hle⟩, hb2⟩ := hp
        -- a²·b³ ≤ x  ⟹  a² ≤ x/b³  ⟹  a ≤ Nat.sqrt (x/b³)
        subst hb2
        have hdiv : p.1 ^ 2 ≤ x / p.2 ^ 3 := by
          rw [Nat.le_div_iff_mul_le hb3]; exact hle
        have hsq : p.1 ≤ Nat.sqrt (x / p.2 ^ 3) := Nat.le_sqrt'.mpr hdiv
        simp only [Finset.coe_Icc, Set.mem_Icc]
        exact ⟨ha1, hsq⟩
      · -- injective on the fiber: second coordinate is fixed to `b`, first coord determines pair
        intro p hp q hq hEq
        simp only [Finset.mem_coe, pairSet, Finset.mem_filter] at hp hq
        have hpb := hp.2
        have hqb := hq.2
        exact Prod.ext hEq (by rw [hpb, hqb])
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  · -- b = 0: fiber is empty since pairs require p.2 ≥ 1
    have hb0 : b = 0 := by omega
    apply le_trans _ (Nat.zero_le _)
    apply le_of_eq
    rw [Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    intro p hp hpb
    simp only [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨_, _, hb1, _⟩ := hp
    rw [hpb, hb0] at hb1
    exact absurd hb1 (by norm_num)

/-- Step 2 conclusion: the pair count is bounded by `∑_{b=1}^{x} Nat.sqrt (x / b³)`. -/
theorem pair_card_le_sum (x : ℕ) :
    (pairSet x).card ≤ ∑ b ∈ Finset.Icc 1 x, Nat.sqrt (x / b ^ 3) := by
  -- Fiber over the second coordinate.
  have hmap : ∀ p ∈ pairSet x, p.2 ∈ Finset.Icc 1 x := by
    intro p hp
    simp only [pairSet, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.2
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_le_sum
  intro b _
  exact pairSet_fiber_card_le x b

/-! ## §3  The analytic bound: `∑_{b≥1} b^{-3/2} ≤ 3` and the final count -/

/-- Telescoping term bound.  For a real `B ≥ 2`,
`1 / B^{3/2} ≤ 2/√(B-1) - 2/√B`, phrased using `Real.sqrt`. -/
theorem term_le_telescope {B : ℝ} (hB : 2 ≤ B) :
    1 / (B * Real.sqrt B) ≤ 2 / Real.sqrt (B - 1) - 2 / Real.sqrt B := by
  have hB0 : (0:ℝ) < B := by linarith
  have hB1 : (0:ℝ) < B - 1 := by linarith
  set s := Real.sqrt B with hs_def
  set t := Real.sqrt (B - 1) with ht_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hB0
  have ht_pos : 0 < t := Real.sqrt_pos.mpr hB1
  have hs2 : s ^ 2 = B := Real.sq_sqrt (le_of_lt hB0)
  have ht2 : t ^ 2 = B - 1 := Real.sq_sqrt (le_of_lt hB1)
  have hts : t ≤ s := by
    rw [hs_def, ht_def]; exact Real.sqrt_le_sqrt (by linarith)
  have hst_pos : 0 < s + t := by linarith
  -- Reduce to a polynomial inequality by clearing all (positive) denominators.
  rw [div_sub_div _ _ (ne_of_gt ht_pos) (ne_of_gt hs_pos)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- Goal: 1 * (t * s) ≤ (2*s - 2*t) * (B * s).  Substitute B = s², use s² - t² = 1.
  -- Now: 1 * (t * s) ≤ (2 s - 2 t) · (B · s), with B = s², t² = s² - 1.
  -- Reduces to  2 s² (s - t) ≥ t, i.e.  2 s² ≥ t(s+t) = ts + t² = ts + s² - 1,
  -- i.e.  s² + 1 ≥ ts, which holds since ts ≤ s².
  have hdiff1 : (s - t) * (s + t) = 1 := by nlinarith [hs2, ht2]
  have hts2 : t * s ≤ s ^ 2 := by nlinarith [hts, hs_pos]
  nlinarith [hdiff1, hts2, hs2, ht2, hs_pos, ht_pos, hts, mul_pos hs_pos ht_pos,
    mul_pos (mul_pos hs_pos hs_pos) hs_pos, mul_nonneg (le_of_lt hs_pos) (sub_nonneg.mpr hts)]

/-- Telescoped partial-sum bound: `∑_{b=1}^{N} 1/(b√b) ≤ 3 - 2/√N` for `N ≥ 1`.
This is the uniform-in-`N` `p`-series bound at `p = 3/2`. -/
theorem sum_recip_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ b ∈ Finset.Icc 1 N, 1 / ((b : ℝ) * Real.sqrt b) ≤ 3 - 2 / Real.sqrt N := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · -- N = 1
      subst hn0
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Real.sqrt_one]
      norm_num
    · -- N = n + 1 with n ≥ 1
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hstep := ih hn1
      -- new term = 1/((n+1)·√(n+1)); use telescope with B = n+1 ≥ 2.
      have hBge : (2 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
        linarith
      have htel := term_le_telescope hBge
      -- (n+1 : ℝ) - 1 = n, and casts
      have hcast : ((n : ℝ) + 1) - 1 = (n : ℝ) := by ring
      rw [hcast] at htel
      have hcastN : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcastN]
      -- Combine: sum ≤ (3 - 2/√n) + (2/√n - 2/√(n+1)) = 3 - 2/√(n+1)
      calc ∑ b ∈ Finset.Icc 1 n, 1 / ((b : ℝ) * Real.sqrt b)
            + 1 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))
          ≤ (3 - 2 / Real.sqrt n)
            + (2 / Real.sqrt (n : ℝ) - 2 / Real.sqrt ((n : ℝ) + 1)) := by
            gcongr
        _ = 3 - 2 / Real.sqrt ((n : ℝ) + 1) := by ring

/-- Casting bound: for `b ≥ 1`, `(Nat.sqrt (x / b³) : ℝ) ≤ √x · (1 / (b·√b))`.
Equivalently `(Nat.sqrt (x/b³) : ℝ) ≤ √x / √(b³)`. -/
theorem sqrt_div_le (x b : ℕ) (hb : 1 ≤ b) :
    (Nat.sqrt (x / b ^ 3) : ℝ) ≤ Real.sqrt x * (1 / ((b : ℝ) * Real.sqrt b)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hbsqrt : (0 : ℝ) < Real.sqrt b := Real.sqrt_pos.mpr hb0
  -- (Nat.sqrt (x/b³))² ≤ x/b³ ≤ x/b³ (real), so Nat.sqrt (x/b³) ≤ √(x/b³) = √x/√(b³).
  -- First: (Nat.sqrt y : ℝ) ≤ Real.sqrt y for y = x/b³ (as a real via the nat division ≤ real division).
  set y := x / b ^ 3 with hy
  have hstep1 : (Nat.sqrt y : ℝ) ≤ Real.sqrt (y : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have : (Nat.sqrt y) ^ 2 ≤ y := Nat.sqrt_le' y
    calc ((Nat.sqrt y : ℝ)) ^ 2 = ((Nat.sqrt y) ^ 2 : ℕ) := by push_cast; ring
      _ ≤ (y : ℝ) := by exact_mod_cast this
  -- (y : ℝ) ≤ (x : ℝ) / (b : ℝ)^3  since Nat division ≤ real division.
  have hb3pos : (0 : ℝ) < (b : ℝ) ^ 3 := by positivity
  have hstep2 : (y : ℝ) ≤ (x : ℝ) / (b : ℝ) ^ 3 := by
    rw [hy, le_div_iff₀ hb3pos]
    have hnat : x / b ^ 3 * b ^ 3 ≤ x := Nat.div_mul_le_self x (b ^ 3)
    calc ((x / b ^ 3 : ℕ) : ℝ) * (b : ℝ) ^ 3
          = (((x / b ^ 3) * b ^ 3 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (x : ℝ) := by exact_mod_cast hnat
  -- Chain: Nat.sqrt y ≤ √y ≤ √(x/b³) = √x/√(b³) = √x/(b·√b).
  have hchain : (Nat.sqrt y : ℝ) ≤ Real.sqrt ((x : ℝ) / (b : ℝ) ^ 3) :=
    le_trans hstep1 (Real.sqrt_le_sqrt hstep2)
  -- √(x/b³) = √x / √(b³) and √(b³) = b·√b.
  have hsqrtdiv : Real.sqrt ((x : ℝ) / (b : ℝ) ^ 3)
      = Real.sqrt x / ((b : ℝ) * Real.sqrt b) := by
    rw [Real.sqrt_div' _ (by positivity)]
    congr 1
    -- √(b³) = b·√b
    have : (b : ℝ) ^ 3 = (b : ℝ) ^ 2 * b := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hb0)]
  rw [hsqrtdiv] at hchain
  calc (Nat.sqrt y : ℝ) ≤ Real.sqrt x / ((b : ℝ) * Real.sqrt b) := hchain
    _ = Real.sqrt x * (1 / ((b : ℝ) * Real.sqrt b)) := by rw [mul_one_div]

/-! ## §4  The final unconditional global count -/

/-- **Global count of powerful numbers (Erdős #942, unconditional).**
The number of powerful (2-full) numbers `m` with `1 ≤ m ≤ x` is at most `3√x`. -/
theorem powerful_global_count (x : ℕ) :
    (((Finset.Icc 1 x).filter (fun m => KFull 2 m)).card : ℝ) ≤ 3 * Real.sqrt x := by
  -- Reduce to the pair-sum bound (Nat), then cast and apply the analytic bounds.
  have hcard : (powerfulSet x).card ≤ ∑ b ∈ Finset.Icc 1 x, Nat.sqrt (x / b ^ 3) :=
    le_trans (powerful_card_le_pair_card x) (pair_card_le_sum x)
  have hcardR : ((powerfulSet x).card : ℝ)
      ≤ ∑ b ∈ Finset.Icc 1 x, (Nat.sqrt (x / b ^ 3) : ℝ) := by
    calc ((powerfulSet x).card : ℝ)
        ≤ ((∑ b ∈ Finset.Icc 1 x, Nat.sqrt (x / b ^ 3) : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = ∑ b ∈ Finset.Icc 1 x, (Nat.sqrt (x / b ^ 3) : ℝ) := by push_cast; ring
  -- powerfulSet x = the filtered Icc in the statement
  have hset : powerfulSet x = (Finset.Icc 1 x).filter (fun m => KFull 2 m) := rfl
  rw [hset] at hcardR
  -- Bound each term by √x · (1/(b·√b)), factor out √x, use ∑ ≤ 3.
  have hterm : ∀ b ∈ Finset.Icc 1 x, (Nat.sqrt (x / b ^ 3) : ℝ)
      ≤ Real.sqrt x * (1 / ((b : ℝ) * Real.sqrt b)) := by
    intro b hb
    simp only [Finset.mem_Icc] at hb
    exact sqrt_div_le x b hb.1
  have hsum1 : ∑ b ∈ Finset.Icc 1 x, (Nat.sqrt (x / b ^ 3) : ℝ)
      ≤ ∑ b ∈ Finset.Icc 1 x, Real.sqrt x * (1 / ((b : ℝ) * Real.sqrt b)) :=
    Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum1
  -- ∑ 1/(b√b) ≤ 3
  rcases Nat.eq_zero_or_pos x with hx0 | hxpos
  · -- x = 0: LHS card is 0, RHS = 0.
    subst hx0
    have hempty : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by
      rw [Finset.Icc_eq_empty]; omega
    rw [hempty, Finset.filter_empty, Finset.card_empty]
    simp
  · have hsum2 : ∑ b ∈ Finset.Icc 1 x, 1 / ((b : ℝ) * Real.sqrt b) ≤ 3 := by
      have := sum_recip_le x hxpos
      have hnn : 0 ≤ 2 / Real.sqrt x := by positivity
      linarith
    have hsqrtnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    calc (((Finset.Icc 1 x).filter (fun m => KFull 2 m)).card : ℝ)
        ≤ Real.sqrt x * ∑ b ∈ Finset.Icc 1 x, 1 / ((b : ℝ) * Real.sqrt b) :=
          le_trans hcardR hsum1
      _ ≤ Real.sqrt x * 3 := by
          apply mul_le_mul_of_nonneg_left hsum2 hsqrtnn
      _ = 3 * Real.sqrt x := by ring

end Erdos942.GlobalCount
