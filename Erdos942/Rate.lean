import Erdos942.Construction
open scoped BigOperators Nat Classical
open Real

/- ===== nth_prime_upper ===== -/
open scoped Nat

namespace NthPrimeUpper

theorem bert (k : ℕ) : Nat.nth Nat.Prime (k+1) ≤ 2 * Nat.nth Nat.Prime k := by
  have hp : Nat.Prime (Nat.nth Nat.Prime k) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime k) hp.pos.ne'
  refine le_trans ?_ hle
  by_contra hcon; rw [not_le] at hcon
  have := Nat.le_nth_of_lt_nth_succ hcon hq; omega

theorem seed (h : ℕ) : Nat.nth Nat.Prime h ≤ 2^(h+1) := by
  induction h with
  | zero => rw [Nat.nth_prime_zero_eq_two]; norm_num
  | succ k ih =>
    calc Nat.nth Nat.Prime (k+1) ≤ 2 * Nat.nth Nat.Prime k := bert k
    _ ≤ 2 * 2^(k+1) := by omega
    _ = 2^(k+1+1) := by ring

theorem piid (h : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime h) = h + 1 := by
  have hp : Nat.Prime (Nat.nth Nat.Prime h) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime h
  have h1 : Nat.primeCounting' (Nat.nth Nat.Prime h) = h := Nat.primeCounting'_nth_eq h
  unfold Nat.primeCounting
  rw [show Nat.primeCounting' = Nat.count Nat.Prime from rfl] at h1 ⊢
  rw [Nat.count_succ, h1]; simp [hp]

end NthPrimeUpper

open NthPrimeUpper in
theorem nth_prime_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 2 ≤ h →
      (Nat.nth Nat.Prime h : ℝ) ≤ C * (h : ℝ) * Real.log h := by
  refine ⟨50, by norm_num, ?_⟩
  intro h hh
  set x : ℝ := (Nat.nth Nat.Prime h : ℝ) with hxdef
  -- basic positivity
  have hx5N : 5 ≤ Nat.nth Nat.Prime h := by
    have : Nat.nth Nat.Prime 2 ≤ Nat.nth Nat.Prime h :=
      (Nat.nth_le_nth Nat.infinite_setOf_prime).2 hh
    rwa [Nat.nth_prime_two_eq_five] at this
  have hx5 : (5:ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hx5N
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlg2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhR : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlogh : Real.log 2 ≤ Real.log h := Real.log_le_log (by norm_num) hhR
  have hloghpos : 0 < Real.log h := by linarith
  -- (★) core
  have hstar : x * Real.log 2 - Real.log (x+1) ≤ ((h:ℝ)+1) * Real.log x := by
    have hpi := Chebyshev.pi_ge (Nat.nth Nat.Prime h)
    rw [piid h] at hpi
    rw [div_le_iff₀ hlogx] at hpi
    rw [hxdef]; push_cast at hpi ⊢; linarith [hpi]
  -- log(x+1) ≤ log2 + log x
  have hlx1 : Real.log (x+1) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    apply Real.log_le_log (by linarith); linarith
  -- real seed: log x ≤ (h+1) log 2
  have hseed : Real.log x ≤ ((h:ℝ)+1) * Real.log 2 := by
    have hs : x ≤ (2:ℝ)^(h+1) := by rw [hxdef]; exact_mod_cast seed h
    calc Real.log x ≤ Real.log ((2:ℝ)^(h+1)) := Real.log_le_log hxpos hs
    _ = ((h:ℝ)+1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  -- step2: x ≤ 9 h^2
  have hstep2 : x ≤ 9 * (h:ℝ)^2 := by
    -- x*lg2 ≤ (h+2)*Lx + lg2 ; Lx ≤ (h+1)lg2 ; combine
    have hA : x * Real.log 2 ≤ ((h:ℝ)+2) * Real.log x + Real.log 2 := by
      linarith [hstar, hlx1]
    have hB : x * Real.log 2 ≤ ((h:ℝ)+2) * (((h:ℝ)+1) * Real.log 2) + Real.log 2 := by
      have hpos2 : (0:ℝ) ≤ (h:ℝ)+2 := by linarith
      nlinarith [hA, hseed, mul_le_mul_of_nonneg_left hseed hpos2]
    -- divide by lg2
    have hB' : x * Real.log 2 ≤ (((h:ℝ)+2)*((h:ℝ)+1) + 1) * Real.log 2 := by nlinarith [hB]
    have hC : x ≤ ((h:ℝ)+2)*((h:ℝ)+1) + 1 := le_of_mul_le_mul_right hB' hlg2
    nlinarith [hC, hhR]
  -- log x ≤ log 9 + 2 log h
  have hlog9 : Real.log x ≤ Real.log 9 + 2 * Real.log h := by
    have h9 : Real.log (9 * (h:ℝ)^2) = Real.log 9 + 2 * Real.log h := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    calc Real.log x ≤ Real.log (9 * (h:ℝ)^2) := Real.log_le_log hxpos hstep2
    _ = Real.log 9 + 2 * Real.log h := h9
  -- step3: x*lg2 ≤ (h+2)*Lx + lg2 ≤ (h+2)(log9 + 2 log h) + lg2
  have hstep3 : x * Real.log 2 ≤ ((h:ℝ)+2) * (Real.log 9 + 2 * Real.log h) + Real.log 2 := by
    have hA : x * Real.log 2 ≤ ((h:ℝ)+2) * Real.log x + Real.log 2 := by
      linarith [hstar, hlx1]
    have hpos2 : (0:ℝ) ≤ (h:ℝ)+2 := by linarith
    nlinarith [hA, mul_le_mul_of_nonneg_left hlog9 hpos2]
  -- numeric facts
  have hlog9le : Real.log 9 ≤ 4 := by
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
    have he : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]; push_cast; ring
    rw [he]; linarith
  have hlg2lb : (1:ℝ)/2 ≤ Real.log 2 := by
    have : Real.log (2⁻¹) ≤ (2:ℝ)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    rw [Real.log_inv] at this; linarith
  have hloghlb : (1:ℝ)/2 ≤ Real.log h := le_trans hlg2lb hlogh
  -- divide hstep3 by log 2:  x ≤ 2*(h+2)*(log9 + 2 logh) + 1
  -- (since 1/log2 ≤ 2 because log2 ≥ 1/2)
  have hdiv : x ≤ 2 * ((h:ℝ)+2) * (Real.log 9 + 2 * Real.log h) + 1 := by
    -- from hstep3: x*t ≤ A + t  with A = (h+2)(log9+2logh) ≥ 0
    have hAnn : (0:ℝ) ≤ ((h:ℝ)+2) * (Real.log 9 + 2 * Real.log h) := by
      apply mul_nonneg (by linarith); nlinarith [hloghpos]
    -- want x ≤ 2A + 1; suffices (x - (2A+1)) * t ≤ 0 with t > 0
    have key : (x - (2 * ((h:ℝ)+2) * (Real.log 9 + 2 * Real.log h) + 1)) * Real.log 2 ≤ 0 := by
      nlinarith [hstep3, hlg2lb, hAnn]
    nlinarith [key, hlg2,
      mul_pos hlg2 hlg2]
  -- finally x ≤ 50 h logh
  rw [hxdef]; rw [hxdef] at hdiv
  refine le_trans hdiv ?_
  nlinarith [hlog9le, hloghlb, hlogh, hhR, hloghpos,
    mul_le_mul hhR hloghlb (by norm_num) (by linarith : (0:ℝ) ≤ (h:ℝ)),
    mul_le_mul_of_nonneg_left hlog9le (show (0:ℝ) ≤ (h:ℝ)+2 by linarith),
    mul_nonneg (show (0:ℝ) ≤ (h:ℝ) by linarith) hloghpos.le]

/- ===== box_principle_quantitative ===== -/
open scoped BigOperators Nat Classical

/-- Quantitative simultaneous box principle: same as `box_principle_simultaneous`
but exposing the denominator bound `q ≤ ∏ ⌈(δ i)⁻¹⌉₊`. -/
theorem box_principle_quantitative {ι : Type*} [Fintype ι] (α : ι → ℝ) (δ : ι → ℝ)
    (hδ : ∀ i, 0 < δ i) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ ∏ i, ⌈(δ i)⁻¹⌉₊ ∧
      ∀ i, |(q : ℝ) * α i - ((round ((q : ℝ) * α i) : ℤ) : ℝ)| ≤ δ i := by
  set T := ∏ i, ⌈(δ i)⁻¹⌉₊ with hT
  have hT_pos : 0 < T := Finset.prod_pos fun i _ => Nat.ceil_pos.mpr (inv_pos.mpr (hδ i))
  obtain ⟨t₁, t₂, ht₁t₂, ht₂T, ht⟩ :
      ∃ t₁ t₂ : ℕ, t₁ < t₂ ∧ t₂ ≤ T ∧
        ∀ i, ⌊Int.fract (t₁ * α i) / δ i⌋₊ = ⌊Int.fract (t₂ * α i) / δ i⌋₊ := by
    have h_pigeonhole : Finset.card (Finset.image
        (fun t : ℕ => fun i : ι => ⌊Int.fract (t * α i) / δ i⌋₊) (Finset.range (T + 1))) ≤ T := by
      refine' le_trans (Finset.card_le_card <| Finset.image_subset_iff.mpr _) _
      exact Finset.Iic (fun i => ⌈(δ i)⁻¹⌉₊ - 1)
      · simp +zetaDelta at *
        intro x hx i; refine' Nat.le_sub_one_of_lt _; refine' Nat.floor_lt' _ |>.2 _
        · exact ne_of_gt (Nat.ceil_pos.mpr (inv_pos.mpr (hT_pos i)))
        · rw [div_lt_iff₀ (hT_pos i)]; nlinarith [Nat.le_ceil ((δ i)⁻¹), hT_pos i, mul_inv_cancel₀ (ne_of_gt (hT_pos i)), Int.fract_lt_one ((x : ℝ) * α i)]
      · erw [Finset.card_map, Finset.card_pi]; aesop
    contrapose! h_pigeonhole
    rw [Finset.card_image_of_injOn fun t₁ ht₁ t₂ ht₂ h => le_antisymm (le_of_not_gt fun h' => by obtain ⟨i, hi⟩ := h_pigeonhole _ _ h' (by linarith [Finset.mem_range.mp ht₁, Finset.mem_range.mp ht₂]); have := congr_fun h i; aesop) (le_of_not_gt fun h' => by obtain ⟨i, hi⟩ := h_pigeonhole _ _ h' (by linarith [Finset.mem_range.mp ht₁, Finset.mem_range.mp ht₂]); have := congr_fun h i; aesop)]; simp +arith +decide
  refine' ⟨t₂ - t₁, Nat.sub_pos_of_lt ht₁t₂, le_trans (Nat.sub_le _ _) ht₂T, _⟩
  intro i
  have h_frac : |Int.fract (t₁ * α i) - Int.fract (t₂ * α i)| ≤ δ i := by
    have := ht i; rw [Nat.floor_eq_iff] at this
    · rw [abs_le]; constructor <;> nlinarith [Nat.floor_le (show 0 ≤ Int.fract ((t₂ : ℝ) * α i) / δ i by exact div_nonneg (Int.fract_nonneg _) (le_of_lt (hδ i))), Nat.lt_floor_add_one (Int.fract ((t₂ : ℝ) * α i) / δ i), hδ i, mul_div_cancel₀ (Int.fract ((t₁ : ℝ) * α i)) (ne_of_gt (hδ i)), mul_div_cancel₀ (Int.fract ((t₂ : ℝ) * α i)) (ne_of_gt (hδ i))]
    · exact div_nonneg (Int.fract_nonneg _) (le_of_lt (hδ i))
  convert round_le _ (⌊(t₂ : ℝ) * α i⌋ - ⌊(t₁ : ℝ) * α i⌋) |> le_trans <| _ using 1
  · infer_instance
  · convert h_frac using 1; rw [Nat.cast_sub ht₁t₂.le]; rw [Int.fract, Int.fract]; ring
    rw [← abs_neg]; push_cast; ring

/- ===== divisor_count ===== -/
open scoped BigOperators

theorem squarefree_divisors_count (D : ℕ) (hD : Squarefree D) (hD1 : 1 < D) :
    ((D.divisors).filter (1 < ·)).card = 2 ^ D.primeFactors.card - 1 := by
  have hD0 : D ≠ 0 := by omega
  -- number of divisors = 2 ^ ω D
  have hcard : D.divisors.card = 2 ^ D.primeFactors.card := by
    rw [Nat.card_divisors hD0]
    rw [Finset.prod_congr rfl (fun p hp => ?_)]
    · rw [Finset.prod_const]
    · -- factorization p + 1 = 2 for p a prime factor
      have hp' : p ∈ D.primeFactors := hp
      have hpd : p ∣ D := Nat.dvd_of_mem_primeFactors hp'
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp'
      have hle : D.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hD
      have hge : 1 ≤ D.factorization p := by
        rw [← Nat.Prime.dvd_iff_one_le_factorization hpp hD0]
        exact hpd
      omega
  -- divisors = {1} ∪ filter (1 < ·), disjointly
  have h1mem : 1 ∈ D.divisors := Nat.one_mem_divisors.mpr hD0
  -- the filter complement: filter (¬ 1 < ·) divisors = {1}
  have hsplit : (D.divisors.filter (1 < ·)).card = D.divisors.card - 1 := by
    have : D.divisors.filter (fun d => ¬ (1 < d)) = {1} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_singleton, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdvd, _⟩, hnlt⟩
        have hd0 : d ≠ 0 := by
          rintro rfl
          simp at hdvd
          exact hD0 hdvd
        omega
      · rintro rfl
        exact ⟨⟨one_dvd D, hD0⟩, by omega⟩
    have hcardfilter := Finset.card_filter_add_card_filter_not
      (s := D.divisors) (p := fun d => 1 < d)
    rw [this] at hcardfilter
    simp only [Finset.card_singleton] at hcardfilter
    omega
  rw [hsplit, hcard]

/-- Downstream form: for a squarefree `D > 1` whose number of prime factors `h = ω D`
satisfies `2 ^ h - 1 ≥ 2 * ℓ`, the set of divisors `d` of `D` with `1 < d` has card
`≥ 2 * ℓ`, and every such `d` is squarefree (automatic since `d ∣ D` and `D` is squarefree).
The witnessing finset is `(D.divisors).filter (1 < ·)`. -/
theorem squarefree_many_divisors (D : ℕ) (hD : Squarefree D) (hD1 : 1 < D)
    (ℓ : ℕ) (hℓ : 2 * ℓ ≤ 2 ^ D.primeFactors.card - 1) :
    ∃ S : Finset ℕ, 2 * ℓ ≤ S.card ∧
      (∀ d ∈ S, d ∣ D ∧ 1 < d ∧ Squarefree d) := by
  refine ⟨(D.divisors).filter (1 < ·), ?_, ?_⟩
  · rw [squarefree_divisors_count D hD hD1]; exact hℓ
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hlt⟩ := hd
    exact ⟨hdvd, hlt, hD.squarefree_of_dvd hdvd⟩

/- ===== rate_inversion ===== -/
open Real

/-- Faithful reformulation of the "inversion" lemma.

The literal statement with only `2 ≤ X` is FALSE: as `X → e⁺`,
`log log X → 0⁺`, so `X / (log X · log log X) → +∞`, while the
constraint `X ≤ C·ℓ·log ℓ·log log ℓ` is satisfied for every `ℓ ≥ ℓ₀`
(the RHS is huge).  Picking `X` close enough to `e` with `ℓ = ℓ₀`
breaks any fixed `c, ℓ₀`.

The honest version restricts to the regime where the rate function
`f(t) = t/(log t · log log t)` is meaningful, i.e. `log X ≥ 1` and
`log log X ≥ 1`, equivalently `exp (exp 1) ≤ X`.  In the intended
application `X = log N → ∞`, so this regime is exactly the one of
interest.  We use the hypothesis `Real.exp (Real.exp 1) ≤ X`.

Conclusion: with `c = 1/(C+1)`,
  `c · X / (log X · log log X) ≤ ℓ`,
i.e. `ℓ ≳ X / (log X · log log X)`. -/
theorem rate_inversion (C : ℝ) (hC : 0 < C) :
    ∃ (c : ℝ) (ℓ₀ : ℕ), 0 < c ∧ ∀ (ℓ : ℕ) (X : ℝ),
      ℓ₀ ≤ ℓ → Real.exp (Real.exp 1) ≤ X →
      X ≤ C * (ℓ : ℝ) * Real.log ℓ * Real.log (Real.log ℓ) →
      c * X / (Real.log X * Real.log (Real.log X)) ≤ (ℓ : ℝ) := by
  refine ⟨1 / (C + 1), 3, by positivity, ?_⟩
  intro ℓ X hℓ hX hXY
  -- Basic facts about X.
  have hEpos : (0:ℝ) < Real.exp (Real.exp 1) := Real.exp_pos _
  have hX2 : (2:ℝ) ≤ X := by
    refine le_trans ?_ hX
    have h1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    calc (2:ℝ) ≤ Real.exp 1 := by
            have h := Real.add_one_le_exp (1:ℝ); nlinarith [h]
      _ ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr h1
  have hXpos : (0:ℝ) < X := lt_of_lt_of_le (by norm_num) hX2
  -- log X ≥ 1 :  X ≥ exp(exp 1) ≥ exp 1, so log X ≥ exp 1 ≥ 1
  have hlogX_ge_e1 : Real.exp 1 ≤ Real.log X := by
    have : Real.log (Real.exp (Real.exp 1)) ≤ Real.log X :=
      Real.log_le_log hEpos hX
    simpa [Real.log_exp] using this
  have he1_ge1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hlogX1 : (1:ℝ) ≤ Real.log X := le_trans he1_ge1 hlogX_ge_e1
  have hlogXpos : (0:ℝ) < Real.log X := lt_of_lt_of_le (by norm_num) hlogX1
  -- log log X ≥ 1
  have hloglogX1 : (1:ℝ) ≤ Real.log (Real.log X) := by
    have : Real.log (Real.exp 1) ≤ Real.log (Real.log X) :=
      Real.log_le_log (Real.exp_pos _) hlogX_ge_e1
    simpa [Real.log_exp] using this
  have hloglogXpos : (0:ℝ) < Real.log (Real.log X) := lt_of_lt_of_le (by norm_num) hloglogX1
  -- ℓ facts
  have hℓ3 : (3:ℕ) ≤ ℓ := hℓ
  have hℓR3 : (3:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ3
  have hℓpos : (0:ℝ) < (ℓ:ℝ) := lt_of_lt_of_le (by norm_num) hℓR3
  have hcpos : (0:ℝ) < 1 / (C + 1) := by positivity
  have hc_le1 : 1 / (C + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  -- denominator positive
  have hden : (0:ℝ) < Real.log X * Real.log (Real.log X) := mul_pos hlogXpos hloglogXpos
  by_cases hcase : (ℓ:ℝ) ≤ X
  · -- Case A1: ℓ ≤ X.  Use monotonicity of log to compare denominators.
    -- log ℓ ≥ 1
    have hlogℓ1 : (1:ℝ) ≤ Real.log ℓ := by
      have : Real.log (Real.exp 1) ≤ Real.log ℓ := by
        apply Real.log_le_log (Real.exp_pos _)
        calc Real.exp 1 ≤ (3:ℝ) := by
              have h := Real.add_one_le_exp (1:ℝ)
              -- exp 1 ≤ 3
              nlinarith [Real.exp_one_lt_d9]
          _ ≤ (ℓ:ℝ) := hℓR3
      simpa [Real.log_exp] using this
    have hlogℓpos : (0:ℝ) < Real.log ℓ := lt_of_lt_of_le (by norm_num) hlogℓ1
    -- log ℓ ≤ log X
    have hlog_le : Real.log ℓ ≤ Real.log X := Real.log_le_log hℓpos hcase
    -- log log ℓ ≤ log log X
    have hloglog_le : Real.log (Real.log ℓ) ≤ Real.log (Real.log X) :=
      Real.log_le_log hlogℓpos hlog_le
    -- log log ℓ ≥ 0
    have hloglogℓ0 : (0:ℝ) ≤ Real.log (Real.log ℓ) := Real.log_nonneg hlogℓ1
    -- C·ℓ·log ℓ·loglog ℓ ≤ C·ℓ·log X·loglog X
    have hYbound : C * (ℓ:ℝ) * Real.log ℓ * Real.log (Real.log ℓ)
        ≤ C * (ℓ:ℝ) * Real.log X * Real.log (Real.log X) := by
      gcongr
    have hXle : X ≤ C * (ℓ:ℝ) * Real.log X * Real.log (Real.log X) :=
      le_trans hXY hYbound
    -- Now c·X/(logX loglogX) ≤ c·C·ℓ ≤ ℓ  (since c·C ≤ 1)
    -- From hXle: X / (logX loglogX) ≤ C·ℓ
    have hfX : X / (Real.log X * Real.log (Real.log X)) ≤ C * (ℓ:ℝ) := by
      rw [div_le_iff₀ hden]
      calc X ≤ C * (ℓ:ℝ) * Real.log X * Real.log (Real.log X) := hXle
        _ = C * (ℓ:ℝ) * (Real.log X * Real.log (Real.log X)) := by ring
    -- multiply by c
    have : (1 / (C + 1)) * X / (Real.log X * Real.log (Real.log X))
        ≤ (1 / (C + 1)) * (C * (ℓ:ℝ)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hfX (le_of_lt hcpos)
    refine le_trans this ?_
    -- (1/(C+1))·(C·ℓ) ≤ ℓ
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0:ℝ) < C + 1)]
    nlinarith [hℓpos]
  · -- Case A2: X < ℓ.  f(X) ≤ X < ℓ.
    rw [not_le] at hcase
    -- f(X) = X/(logX loglogX) ≤ X since denom ≥ 1
    have hden1 : (1:ℝ) ≤ Real.log X * Real.log (Real.log X) := by
      nlinarith [hlogX1, hloglogX1, hlogXpos.le, hloglogXpos.le]
    have hfXleX : X / (Real.log X * Real.log (Real.log X)) ≤ X := by
      rw [div_le_iff₀ hden]
      nlinarith [hden1, hXpos.le]
    have : (1 / (C + 1)) * X / (Real.log X * Real.log (Real.log X))
        ≤ (1 / (C + 1)) * X := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hfXleX (le_of_lt hcpos)
    refine le_trans this ?_
    calc (1 / (C + 1)) * X ≤ 1 * X := by
          apply mul_le_mul_of_nonneg_right hc_le1 hXpos.le
      _ = X := one_mul X
      _ ≤ (ℓ:ℝ) := le_of_lt hcase

/- ===== log_primorial ===== -/
open scoped BigOperators
open Real

theorem log_primorial_le
    (hnth : ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 2 ≤ h →
              (Nat.nth Nat.Prime h : ℝ) ≤ C * (h : ℝ) * Real.log h) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ h : ℕ, 2 ≤ h →
      Real.log (∏ i ∈ Finset.range h, (Nat.nth Nat.Prime i : ℝ))
        ≤ C' * (h : ℝ) * Real.log h := by
  obtain ⟨C, hC, hbound⟩ := hnth
  -- log 2 > 0
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- choose C' = 2 + |log C| / log 2
  refine ⟨2 + |Real.log C| / Real.log 2, by positivity, ?_⟩
  intro h hh
  have hh2 : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hpos : (0:ℝ) < (h:ℝ) := by linarith
  -- log h ≥ log 2 > 0
  have hmono2 : Real.log 2 ≤ Real.log h := by
    apply Real.log_le_log (by norm_num) hh2
  have hloghpos : (0:ℝ) < Real.log h := by linarith
  -- step 1: log of product = sum of logs
  have hne : ∀ i ∈ Finset.range h, (Nat.nth Nat.Prime i : ℝ) ≠ 0 := by
    intro i _
    have : (0:ℝ) < (Nat.nth Nat.Prime i : ℝ) := by
      have := (Nat.prime_nth_prime i).pos; exact_mod_cast this
    exact ne_of_gt this
  rw [Real.log_prod hne]
  -- step 2: each log p_i ≤ log p_h
  have hmono : ∀ i ∈ Finset.range h,
      Real.log (Nat.nth Nat.Prime i : ℝ) ≤ Real.log (Nat.nth Nat.Prime h : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply Real.log_le_log
    · have := (Nat.prime_nth_prime i).pos; exact_mod_cast this
    · have : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime h := by
        apply Nat.nth_monotone Nat.infinite_setOf_prime; omega
      exact_mod_cast this
  -- step 3: sum ≤ h * log p_h
  have hsum : ∑ i ∈ Finset.range h, Real.log (Nat.nth Nat.Prime i : ℝ)
      ≤ (Finset.range h).card • Real.log (Nat.nth Nat.Prime h : ℝ) :=
    Finset.sum_le_card_nsmul _ _ _ hmono
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  -- step 4: log p_h ≤ log(C h log h)
  have hph_pos : (0:ℝ) < (Nat.nth Nat.Prime h : ℝ) := by
    have := (Nat.prime_nth_prime h).pos; exact_mod_cast this
  have hbh := hbound h hh
  have hlogph : Real.log (Nat.nth Nat.Prime h : ℝ) ≤ Real.log (C * h * Real.log h) :=
    Real.log_le_log hph_pos hbh
  have hexpand : Real.log (C * h * Real.log h)
      = Real.log C + Real.log h + Real.log (Real.log h) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
  -- log(log h) ≤ log h
  have hloglog : Real.log (Real.log h) ≤ Real.log h := by
    have := Real.log_le_sub_one_of_pos hloghpos; linarith
  -- log C ≤ (|log C|/log 2) * log h
  have hlogC : Real.log C ≤ (|Real.log C| / Real.log 2) * Real.log h := by
    have h2 : |Real.log C| = (|Real.log C| / Real.log 2) * Real.log 2 := by field_simp
    calc Real.log C ≤ |Real.log C| := le_abs_self _
      _ = (|Real.log C| / Real.log 2) * Real.log 2 := h2
      _ ≤ (|Real.log C| / Real.log 2) * Real.log h := by
          apply mul_le_mul_of_nonneg_left hmono2; positivity
  -- combine
  have hlogph2 : Real.log (Nat.nth Nat.Prime h : ℝ)
      ≤ (2 + |Real.log C| / Real.log 2) * Real.log h := by
    rw [hexpand] at hlogph
    nlinarith [hlogph, hloglog, hlogC]
  calc ∑ i ∈ Finset.range h, Real.log (Nat.nth Nat.Prime i : ℝ)
      ≤ (h:ℝ) * Real.log (Nat.nth Nat.Prime h : ℝ) := hsum
    _ ≤ (h:ℝ) * ((2 + |Real.log C| / Real.log 2) * Real.log h) :=
        mul_le_mul_of_nonneg_left hlogph2 (le_of_lt hpos)
    _ = (2 + |Real.log C| / Real.log 2) * h * Real.log h := by ring

/- ===== ASSEMBLY (to fill) ===== -/
/-- Squarefreeness of a product of a finset of primes. -/
theorem squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using squarefree_one
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    have hap : a.Prime := hs a (Finset.mem_insert_self a t)
    have iht : Squarefree (∏ p ∈ t, p) := ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
    apply (Nat.squarefree_mul ?_).mpr ⟨hap.squarefree, iht⟩
    apply Nat.Coprime.prod_right
    intro p hp
    exact (Nat.coprime_primes hap (hs p (Finset.mem_insert_of_mem hp))).mpr
      (by rintro rfl; exact ha hp)

/- ===== GENERAL-κ placement machinery (from placement_general.lean) ===== -/
open scoped BigOperators
open Real Finset

noncomputable def alphaG (d κ : ℕ) : ℝ := (d : ℝ) ^ (-(1 : ℝ) / (κ : ℝ))
noncomputable def rG (d κ q : ℕ) : ℕ := (round ((q : ℝ) * alphaG d κ)).toNat
noncomputable def epsG (d κ q : ℕ) : ℝ := (q : ℝ) * alphaG d κ - (round ((q : ℝ) * alphaG d κ) : ℤ)

/-- β = d^{1/κ}. -/
noncomputable def betaG (d κ : ℕ) : ℝ := (d : ℝ) ^ ((1 : ℝ) / (κ : ℝ))

/-! ### Basic facts about α and β -/

theorem betaG_pos (κ d : ℕ) (hd2 : 2 ≤ d) : 0 < betaG d κ := by
  unfold betaG; positivity

theorem alphaG_pos (κ d : ℕ) (hd2 : 2 ≤ d) : 0 < alphaG d κ := by
  unfold alphaG; positivity

theorem betaG_pow (κ d : ℕ) (hκ : 1 ≤ κ) (hd2 : 2 ≤ d) : betaG d κ ^ κ = (d : ℝ) := by
  unfold betaG
  rw [← Real.rpow_natCast ((d:ℝ) ^ ((1:ℝ)/(κ:ℝ))) κ, ← Real.rpow_mul (by positivity)]
  rw [one_div, inv_mul_cancel₀ (by positivity : (κ:ℝ) ≠ 0), Real.rpow_one]

theorem alpha_beta_eq (κ d : ℕ) (hd2 : 2 ≤ d) : alphaG d κ * betaG d κ = 1 := by
  unfold alphaG betaG
  rw [← Real.rpow_add (by positivity)]
  rw [show (-(1:ℝ)/(κ:ℝ) + (1:ℝ)/(κ:ℝ)) = 0 by ring, Real.rpow_zero]

theorem betaG_ge_one (κ d : ℕ) (hκ : 1 ≤ κ) (hd2 : 2 ≤ d) : 1 ≤ betaG d κ := by
  unfold betaG
  apply Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ d))
  positivity

/-! ### Irrationality, hence ε ≠ 0 -/

theorem betaG_irrational (κ d : ℕ) (hκ : 2 ≤ κ) (hd2 : 2 ≤ d) (hd : Squarefree d) :
    Irrational (betaG d κ) := by
  -- pick a prime p ∣ d
  obtain ⟨p, hp, hpd⟩ := (Nat.exists_prime_and_dvd (by omega : d ≠ 1))
  haveI : Fact p.Prime := ⟨hp⟩
  have hbpow : betaG d κ ^ κ = ((d : ℤ) : ℝ) := by
    rw [betaG_pow κ d (by omega) hd2]; push_cast; ring
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  -- multiplicity of p in d is 1 (squarefree, p ∣ d)
  have hmult : multiplicity (p : ℤ) (d : ℤ) = 1 := by
    have hfin : FiniteMultiplicity (p : ℤ) (d : ℤ) := by
      rw [Int.finiteMultiplicity_iff]
      refine ⟨?_, hd0⟩
      have h2 := hp.two_le
      rw [Int.natAbs_natCast]
      omega
    rw [hfin.multiplicity_eq_iff]
    refine ⟨?_, ?_⟩
    · simpa using (Int.natCast_dvd_natCast.mpr hpd)
    · -- p^2 does not divide d
      intro hdvd
      have hdvd' : (p * p : ℕ) ∣ d := by
        have h2 : ((p * p : ℕ) : ℤ) ∣ (d : ℤ) := by push_cast at hdvd ⊢; ring_nf at hdvd ⊢; exact hdvd
        exact_mod_cast h2
      have := hd p hdvd'
      rw [Nat.isUnit_iff] at this
      exact hp.one_lt.ne' this
  have hmodne : multiplicity (p : ℤ) (d : ℤ) % κ ≠ 0 := by
    rw [hmult, Nat.one_mod_eq_one.mpr (by omega)]; omega
  exact irrational_nrt_of_n_not_dvd_multiplicity κ hd0 p hbpow hmodne

theorem alphaG_irrational (κ d : ℕ) (hκ : 2 ≤ κ) (hd2 : 2 ≤ d) (hd : Squarefree d) :
    Irrational (alphaG d κ) := by
  -- α = 1/β; if α rational then β = 1/α rational
  have hb := betaG_irrational κ d hκ hd2 hd
  have hab := alpha_beta_eq κ d hd2
  have hbpos := betaG_pos κ d hd2
  intro ⟨r, hr⟩
  apply hb
  refine ⟨r⁻¹, ?_⟩
  have haα : alphaG d κ ≠ 0 := ne_of_gt (alphaG_pos κ d hd2)
  have hrne : (r : ℝ) ≠ 0 := by rw [hr]; exact haα
  -- β = 1/α
  have hbinv : betaG d κ = 1 / alphaG d κ := by
    rw [eq_div_iff haα, mul_comm]; exact hab
  rw [hbinv, ← hr]
  push_cast
  rw [one_div]

theorem epsG_ne_zero (κ d q : ℕ) (hκ : 2 ≤ κ) (hd2 : 2 ≤ d) (hd : Squarefree d) (hq : 1 ≤ q) :
    epsG d κ q ≠ 0 := by
  unfold epsG
  intro h
  -- then q * α = round, an integer; so α = round / q is rational
  have hα := alphaG_irrational κ d hκ hd2 hd
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  apply hα
  refine ⟨(round ((q:ℝ) * alphaG d κ) : ℚ) / (q : ℚ), ?_⟩
  have heq : (q : ℝ) * alphaG d κ = (round ((q:ℝ) * alphaG d κ) : ℤ) := by linarith [h]
  push_cast
  rw [div_eq_iff hqne]
  linarith [heq]

/-! ### Binomial tail bound -/

theorem binom_tail_bound (κ : ℕ) (hκ : 1 ≤ κ) (q s : ℝ) (hq : 1 ≤ q)
    (hs1 : |s| ≤ 1) :
    |(q - s) ^ κ - q ^ κ| ≤ (κ : ℝ) * q ^ (κ - 1) * |s| * 2 ^ κ := by
  have hexp : (q - s) ^ κ = ∑ m ∈ range (κ + 1), q ^ m * (-s) ^ (κ - m) * (κ.choose m : ℝ) := by
    rw [sub_eq_add_neg]; exact add_pow q (-s) κ
  have hlast : ∑ m ∈ range (κ + 1), q ^ m * (-s) ^ (κ - m) * (κ.choose m : ℝ)
      = (∑ m ∈ range κ, q ^ m * (-s) ^ (κ - m) * (κ.choose m : ℝ)) + q ^ κ := by
    rw [Finset.sum_range_succ]; congr 1; simp
  have hdiff : (q - s) ^ κ - q ^ κ = ∑ m ∈ range κ, q ^ m * (-s) ^ (κ - m) * (κ.choose m : ℝ) := by
    rw [hexp, hlast]; ring
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ m ∈ range κ,
      |q ^ m * (-s) ^ (κ - m) * (κ.choose m : ℝ)| ≤ q ^ (κ - 1) * |s| * 2 ^ κ := by
    intro m hm
    rw [mem_range] at hm
    rw [abs_mul, abs_mul]
    have h1 : |q ^ m| = q ^ m := abs_of_nonneg (by positivity)
    have h2 : |(-s) ^ (κ - m)| = |s| ^ (κ - m) := by rw [abs_pow, abs_neg]
    have h3 : |(κ.choose m : ℝ)| = (κ.choose m : ℝ) := abs_of_nonneg (by positivity)
    rw [h1, h2, h3]
    have hqm : q ^ m ≤ q ^ (κ - 1) := pow_le_pow_right₀ hq (by omega)
    have hsm : |s| ^ (κ - m) ≤ |s| := by
      have : |s| ^ (κ - m) ≤ |s| ^ 1 := pow_le_pow_of_le_one (abs_nonneg s) hs1 (by omega)
      simpa using this
    have hc : (κ.choose m : ℝ) ≤ 2 ^ κ := by
      have hh := Nat.choose_le_two_pow (n := κ) (k := m)
      have : (κ.choose m : ℝ) ≤ ((2 ^ κ : ℕ) : ℝ) := by exact_mod_cast hh
      simpa using this
    exact mul_le_mul (mul_le_mul hqm hsm (by positivity) (by positivity)) hc (by positivity) (by positivity)
  calc ∑ m ∈ range κ, |q ^ m * (-s) ^ (κ - m) * (κ.choose m : ℝ)|
      ≤ ∑ m ∈ range κ, q ^ (κ - 1) * |s| * 2 ^ κ := Finset.sum_le_sum hterm
    _ = (κ : ℝ) * (q ^ (κ - 1) * |s| * 2 ^ κ) := by
        rw [Finset.sum_const, Finset.card_range]; ring
    _ = (κ : ℝ) * q ^ (κ - 1) * |s| * 2 ^ κ := by ring

/-! ### round ≥ 1 -/

theorem round_ge_one (κ D d q : ℕ) (hκ : 2 ≤ κ) (hD : 1 ≤ D) (hd2 : 2 ≤ d) (hq : 1 ≤ q)
    (htol : |epsG d κ q| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * betaG d κ)) :
    1 ≤ round ((q : ℝ) * alphaG d κ) := by
  by_contra hcon
  push_neg at hcon
  -- round ≤ 0.  But qα > 0 ⟹ round ≥ 0, so round = 0.
  have hαpos := alphaG_pos κ d hd2
  have hqαpos : 0 < (q : ℝ) * alphaG d κ := by
    apply mul_pos; exact_mod_cast hq; exact hαpos
  have hround_nonneg : 0 ≤ round ((q : ℝ) * alphaG d κ) := by
    rw [round_eq]; apply Int.floor_nonneg.mpr; linarith
  have hround0 : round ((q : ℝ) * alphaG d κ) = 0 := by omega
  -- then |ε| = qα
  have heps : epsG d κ q = (q : ℝ) * alphaG d κ := by
    unfold epsG; rw [hround0]; push_cast; ring
  have habs : |epsG d κ q| = (q : ℝ) * alphaG d κ := by rw [heps]; exact abs_of_pos hqαpos
  -- qα = q/β ≥ 1/β
  have hβpos := betaG_pos κ d hd2
  have hαβ := alpha_beta_eq κ d hd2
  have hαinv : alphaG d κ = 1 / betaG d κ := by
    rw [eq_div_iff (ne_of_gt hβpos)]; exact hαβ
  have hqα_ge : (q : ℝ) * alphaG d κ ≥ 1 / betaG d κ := by
    rw [hαinv]
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith [hβpos, mul_pos (show (0:ℝ) < 1/betaG d κ by positivity) (show (0:ℝ) < 1 by norm_num)]
  -- contradiction: 1/β ≤ |ε| ≤ δ < 1/β
  rw [habs] at htol
  -- so qα ≤ δ < 1/β ≤ qα.  Use 2^(κ+1)κD > 1 strictly.
  have hbigstrict : (1 : ℝ) < 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) := by
    have hDr : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    have hk : (2:ℝ) ≤ (κ:ℝ) := by exact_mod_cast hκ
    have h2 : (4:ℝ) ≤ 2 ^ (κ+1) := by
      calc (4:ℝ) = 2^2 := by norm_num
        _ ≤ 2^(κ+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hstep : (8:ℝ) ≤ 2 ^ (κ+1) * (κ:ℝ) := by nlinarith
    nlinarith [hstep, hDr]
  have hδstrict : 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * betaG d κ) < 1 / betaG d κ := by
    rw [div_lt_div_iff₀ (by positivity) hβpos]
    nlinarith [hβpos]
  linarith [hqα_ge, htol, hδstrict]

/-! ### The core identity -/

theorem rG_cast (κ D d q : ℕ) (hκ : 2 ≤ κ) (hD : 1 ≤ D) (hd2 : 2 ≤ d) (hq : 1 ≤ q)
    (htol : |epsG d κ q| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * betaG d κ)) :
    ((rG d κ q : ℕ) : ℝ) = (round ((q : ℝ) * alphaG d κ) : ℤ) := by
  have h1 := round_ge_one κ D d q hκ hD hd2 hq htol
  unfold rG
  have : ((round ((q:ℝ) * alphaG d κ)).toNat : ℤ) = round ((q:ℝ) * alphaG d κ) :=
    Int.toNat_of_nonneg (by omega)
  rw [show (((round ((q:ℝ) * alphaG d κ)).toNat : ℕ) : ℝ)
        = (((round ((q:ℝ) * alphaG d κ)).toNat : ℤ) : ℝ) by push_cast; ring, this]

theorem dr_pow_eq (κ D d q : ℕ) (hκ : 2 ≤ κ) (hD : 1 ≤ D) (hd2 : 2 ≤ d) (hq : 1 ≤ q)
    (htol : |epsG d κ q| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * betaG d κ)) :
    (d : ℝ) * ((rG d κ q : ℕ) : ℝ) ^ κ = ((q : ℝ) - betaG d κ * epsG d κ q) ^ κ := by
  have hrc := rG_cast κ D d q hκ hD hd2 hq htol
  -- r = qα - ε
  have hr : ((rG d κ q : ℕ) : ℝ) = (q : ℝ) * alphaG d κ - epsG d κ q := by
    rw [hrc]; unfold epsG; ring
  rw [hr]
  -- d = β^κ
  rw [← betaG_pow κ d (by omega) hd2]
  rw [← mul_pow]
  congr 1
  -- β * (qα - ε) = q - βε
  have hαβ := alpha_beta_eq κ d hd2
  have hbq : betaG d κ * ((q : ℝ) * alphaG d κ) = (q : ℝ) := by
    rw [show betaG d κ * ((q:ℝ) * alphaG d κ) = (q:ℝ) * (alphaG d κ * betaG d κ) by ring, hαβ]; ring
  rw [mul_sub, hbq]

/-! ### Central estimate -/

theorem central_bound (κ D d q : ℕ) (hκ : 2 ≤ κ) (hD : 1 ≤ D) (hd2 : 2 ≤ d) (hq : 1 ≤ q)
    (htol : |epsG d κ q| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * betaG d κ)) :
    |((d * D ^ κ * (rG d κ q) ^ κ : ℕ) : ℝ) - (((D * q) ^ κ : ℕ) : ℝ)|
      < (((D * q) ^ (κ - 1) : ℕ) : ℝ) := by
  have hβpos := betaG_pos κ d hd2
  have hDr : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hqr : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hkr : (2:ℝ) ≤ (κ:ℝ) := by exact_mod_cast hκ
  set s := betaG d κ * epsG d κ q with hs
  -- bound on |s|
  have hβε : |s| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ)) := by
    rw [hs, abs_mul, abs_of_pos hβpos]
    calc betaG d κ * |epsG d κ q|
        ≤ betaG d κ * (1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * betaG d κ)) :=
          mul_le_mul_of_nonneg_left htol (le_of_lt hβpos)
      _ = 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ)) := by
          field_simp
  -- 2^(κ+1) κ D ≥ 1 so |s| ≤ 1
  have hden_ge : (1:ℝ) ≤ 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) := by
    have h2 : (1:ℝ) ≤ 2 ^ (κ+1) := one_le_pow₀ (by norm_num)
    have hstep : (1:ℝ) ≤ 2 ^ (κ+1) * (κ:ℝ) := by nlinarith
    nlinarith [hstep, hDr]
  have hs1 : |s| ≤ 1 := by
    calc |s| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ)) := hβε
      _ ≤ 1 / 1 := by apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden_ge
      _ = 1 := by norm_num
  -- identity for m - n^κ
  have hid := dr_pow_eq κ D d q hκ hD hd2 hq htol
  have hm : ((d * D ^ κ * (rG d κ q) ^ κ : ℕ) : ℝ) = (D:ℝ)^κ * ((q:ℝ) - s)^κ := by
    push_cast
    rw [hs, ← hid]; push_cast; ring
  have hn : (((D * q) ^ κ : ℕ) : ℝ) = (D:ℝ)^κ * (q:ℝ)^κ := by push_cast; ring
  rw [hm, hn]
  rw [show (D:ℝ)^κ * ((q:ℝ) - s)^κ - (D:ℝ)^κ * (q:ℝ)^κ
        = (D:ℝ)^κ * (((q:ℝ) - s)^κ - (q:ℝ)^κ) by ring]
  rw [abs_mul, abs_of_pos (show (0:ℝ) < (D:ℝ)^κ by positivity)]
  -- apply binom bound
  have hbin := binom_tail_bound κ (by omega) (q:ℝ) s hqr hs1
  -- |(q-s)^κ - q^κ| ≤ κ q^{κ-1} |s| 2^κ
  have hstep1 : (D:ℝ)^κ * |((q:ℝ) - s)^κ - (q:ℝ)^κ|
      ≤ (D:ℝ)^κ * ((κ:ℝ) * (q:ℝ) ^ (κ - 1) * |s| * 2 ^ κ) :=
    mul_le_mul_of_nonneg_left hbin (by positivity)
  -- substitute |s| bound
  have hstep2 : (D:ℝ)^κ * ((κ:ℝ) * (q:ℝ) ^ (κ - 1) * |s| * 2 ^ κ)
      ≤ (D:ℝ)^κ * ((κ:ℝ) * (q:ℝ) ^ (κ - 1) * (1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ))) * 2 ^ κ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left hβε (by positivity)
  -- compute RHS = D^{κ-1} q^{κ-1}/2 = (Dq)^{κ-1}/2 < (Dq)^{κ-1}
  have hRHS : (D:ℝ)^κ * ((κ:ℝ) * (q:ℝ) ^ (κ - 1) * (1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ))) * 2 ^ κ)
      = (D:ℝ)^(κ-1) * (q:ℝ)^(κ-1) / 2 := by
    have hDne : (D:ℝ) ≠ 0 := by positivity
    have hκne : (κ:ℝ) ≠ 0 := by positivity
    have hDκ : (D:ℝ)^κ = (D:ℝ)^(κ-1) * (D:ℝ) := by
      rw [← pow_succ]; congr 1; omega
    have h2κ : (2:ℝ)^(κ+1) = 2^κ * 2 := by rw [pow_succ]
    rw [hDκ, h2κ]
    field_simp
  have hfinal : (((D * q) ^ (κ - 1) : ℕ) : ℝ) = (D:ℝ)^(κ-1) * (q:ℝ)^(κ-1) := by push_cast; ring
  calc (D:ℝ)^κ * |((q:ℝ) - s)^κ - (q:ℝ)^κ|
      ≤ (D:ℝ)^(κ-1) * (q:ℝ)^(κ-1) / 2 := by rw [← hRHS]; exact le_trans hstep1 hstep2
    _ < (D:ℝ)^(κ-1) * (q:ℝ)^(κ-1) := by
        have : (0:ℝ) < (D:ℝ)^(κ-1) * (q:ℝ)^(κ-1) := by positivity
        linarith
    _ = (((D * q) ^ (κ - 1) : ℕ) : ℝ) := hfinal.symm

/-! ### Window widths (ℕ facts) -/

theorem window_width_upper (n κ : ℕ) (hκ : 1 ≤ κ) (hn : 1 ≤ n) :
    n ^ κ + n ^ (κ - 1) ≤ (n + 1) ^ κ := by
  have hge := geom_sum₂_mul_of_ge (show n ≤ n + 1 by omega) κ
  have hsub : (n + 1) - n = 1 := by omega
  rw [hsub, mul_one] at hge
  -- the i = κ-1 term of the sum
  have hmem : (κ - 1) ∈ range κ := by rw [mem_range]; omega
  have hterm_le : n ^ (κ - 1) ≤ ∑ i ∈ range κ, (n + 1) ^ i * n ^ (κ - 1 - i) := by
    have hsingle := Finset.single_le_sum (f := fun i => (n + 1) ^ i * n ^ (κ - 1 - i))
      (fun i _ => Nat.zero_le _) hmem
    refine le_trans ?_ hsingle
    have heq : (n + 1) ^ (κ-1) * n ^ (κ - 1 - (κ-1)) = (n + 1) ^ (κ-1) := by
      rw [show κ - 1 - (κ-1) = 0 by omega]; simp
    simp only at hsingle ⊢
    rw [heq]
    exact Nat.pow_le_pow_left (by omega) _
  -- combine
  have hmono : n ^ κ ≤ (n + 1) ^ κ := Nat.pow_le_pow_left (by omega) _
  omega

theorem window_width_lower (n κ : ℕ) (hκ : 1 ≤ κ) (hn : 1 ≤ n) :
    (n - 1) ^ κ + n ^ (κ - 1) ≤ n ^ κ := by
  have hge := geom_sum₂_mul_of_ge (show n - 1 ≤ n by omega) κ
  have hsub : n - (n - 1) = 1 := by omega
  rw [hsub, mul_one] at hge
  have hmem : (κ - 1) ∈ range κ := by rw [mem_range]; omega
  have hterm_le : n ^ (κ - 1) ≤ ∑ i ∈ range κ, n ^ i * (n - 1) ^ (κ - 1 - i) := by
    have hsingle := Finset.single_le_sum (f := fun i => n ^ i * (n - 1) ^ (κ - 1 - i))
      (fun i _ => Nat.zero_le _) hmem
    refine le_trans ?_ hsingle
    have heq : n ^ (κ-1) * (n - 1) ^ (κ - 1 - (κ-1)) = n ^ (κ-1) := by
      rw [show κ - 1 - (κ-1) = 0 by omega]; simp
    simp only at hsingle ⊢
    rw [heq]
  have hmono : (n - 1) ^ κ ≤ n ^ κ := Nat.pow_le_pow_left (by omega) _
  omega

/-! ### m ≠ n^κ -/

theorem m_ne (κ D d q : ℕ) (hκ : 2 ≤ κ) (hD : 1 ≤ D) (hd2 : 2 ≤ d)
    (hd : Squarefree d) (hq : 1 ≤ q)
    (htol : |epsG d κ q| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * betaG d κ)) :
    (d * D ^ κ * (rG d κ q) ^ κ) ≠ (D * q) ^ κ := by
  intro heq
  -- d * r^κ = q^κ
  have hr1 : 1 ≤ round ((q:ℝ) * alphaG d κ) := round_ge_one κ D d q hκ hD hd2 hq htol
  have hrG1 : 1 ≤ rG d κ q := by unfold rG; omega
  have hDne : D ≠ 0 := by omega
  have hdr : d * (rG d κ q) ^ κ = q ^ κ := by
    have hexp : d * D ^ κ * (rG d κ q) ^ κ = D ^ κ * (d * (rG d κ q) ^ κ) := by ring
    rw [hexp, mul_pow] at heq
    -- D^κ * (d r^κ) = D^κ * q^κ
    have hcancel : d * (rG d κ q) ^ κ = q ^ κ := by
      have hDκ : D ^ κ ≠ 0 := pow_ne_zero _ hDne
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hDκ) (by linarith [heq])
    exact hcancel
  -- so β = q / r is rational, contradiction
  have hβ := betaG_irrational κ d hκ hd2 hd
  apply hβ
  -- (β)^κ = d = q^κ / r^κ = (q/r)^κ ⟹ β = q/r
  have hβpos := betaG_pos κ d hd2
  have hrpos : 0 < (rG d κ q : ℝ) := by exact_mod_cast hrG1
  have hd_eq : (d : ℝ) = ((q : ℝ) / (rG d κ q : ℝ)) ^ κ := by
    rw [div_pow]
    rw [eq_div_iff (by positivity)]
    have : (d : ℝ) * (rG d κ q : ℝ) ^ κ = (q : ℝ) ^ κ := by exact_mod_cast hdr
    linarith [this]
  -- β = q/r
  have hβeq : betaG d κ = (q : ℝ) / (rG d κ q : ℝ) := by
    have hbpow := betaG_pow κ d (by omega) hd2
    have hpos2 : 0 < (q : ℝ) / (rG d κ q : ℝ) := by positivity
    have hpoweq : betaG d κ ^ κ = ((q : ℝ) / (rG d κ q : ℝ)) ^ κ := by rw [hbpow, hd_eq]
    rcases lt_trichotomy (betaG d κ) ((q : ℝ) / (rG d κ q : ℝ)) with hlt | heq | hgt
    · exact absurd hpoweq (ne_of_lt (pow_lt_pow_left₀ hlt (le_of_lt hβpos) (by omega)))
    · exact heq
    · exact absurd hpoweq.symm (ne_of_lt (pow_lt_pow_left₀ hgt (le_of_lt hpos2) (by omega)))
  refine ⟨(q : ℚ) / (rG d κ q : ℚ), ?_⟩
  rw [hβeq]; push_cast; ring

/-! ### Main theorem -/

theorem placement_kfull_window_general
    (κ D d q : ℕ) (hκ : 2 ≤ κ) (hD : 1 ≤ D) (hd2 : 2 ≤ d)
    (hd : Squarefree d) (hdvd : d ∣ D) (hq : 1 ≤ q)
    (htol : |epsG d κ q| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d : ℝ) ^ ((1 : ℝ) / (κ : ℝ)))) :
    1 ≤ rG d κ q ∧ KFull κ (d * D ^ κ * (rG d κ q) ^ κ) ∧
      ( (d * D ^ κ * (rG d κ q) ^ κ) ∈ Finset.Ioo ((D * q - 1) ^ κ) ((D * q) ^ κ)
      ∨ (d * D ^ κ * (rG d κ q) ^ κ) ∈ Finset.Ioo ((D * q) ^ κ) ((D * q + 1) ^ κ) ) := by
  -- rewrite tolerance with betaG
  have htol' : |epsG d κ q| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * betaG d κ) := by
    unfold betaG; exact htol
  -- r ≥ 1
  have hr1 : 1 ≤ round ((q:ℝ) * alphaG d κ) := round_ge_one κ D d q hκ hD hd2 hq htol'
  have hrG1 : 1 ≤ rG d κ q := by unfold rG; omega
  refine ⟨hrG1, kfull_construction κ d D (rG d κ q) hdvd, ?_⟩
  -- abbreviations
  set m := d * D ^ κ * (rG d κ q) ^ κ with hm
  set n := D * q with hn
  have hn1 : 1 ≤ n := Nat.mul_pos hD hq
  -- the central bound (ℝ)
  have hcb := central_bound κ D d q hκ hD hd2 hq htol'
  -- |(m:ℝ) - (n^κ : ℝ)| < (n^(κ-1) : ℝ)
  have hcb' : |((m : ℕ) : ℝ) - ((n ^ κ : ℕ) : ℝ)| < ((n ^ (κ - 1) : ℕ) : ℝ) := by
    rw [hm, hn]; exact_mod_cast hcb
  -- m ≠ n^κ
  have hmne : m ≠ n ^ κ := by rw [hm, hn]; exact m_ne κ D d q hκ hD hd2 hd hq htol'
  -- convert to ℕ bounds: |m - n^κ| < n^(κ-1) means n^κ - n^(κ-1) < m < n^κ + n^(κ-1)
  have habs := abs_lt.mp hcb'
  have hlo : ((n ^ κ : ℕ) : ℝ) - ((n ^ (κ-1) : ℕ) : ℝ) < (m : ℝ) := by linarith [habs.1]
  have hhi : (m : ℝ) < ((n ^ κ : ℕ) : ℝ) + ((n ^ (κ-1) : ℕ) : ℝ) := by linarith [habs.2]
  -- in ℕ
  have hloN : n ^ κ - n ^ (κ-1) < m := by
    by_contra hc
    push_neg at hc  -- m ≤ n^κ - n^(κ-1)
    have : (m : ℝ) ≤ ((n ^ κ : ℕ) : ℝ) - ((n ^ (κ-1) : ℕ) : ℝ) := by
      have hge : n ^ (κ-1) ≤ n ^ κ := Nat.pow_le_pow_right (by omega) (by omega)
      have : (m:ℝ) ≤ ((n^κ - n^(κ-1) : ℕ) : ℝ) := by exact_mod_cast hc
      rw [Nat.cast_sub hge] at this; exact this
    linarith [hlo]
  have hhiN : m < n ^ κ + n ^ (κ-1) := by
    by_contra hc
    push_neg at hc
    have : ((n ^ κ : ℕ) : ℝ) + ((n ^ (κ-1) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hc
    linarith [hhi]
  -- window widths
  have hwlo := window_width_lower n κ (by omega) hn1   -- (n-1)^κ + n^(κ-1) ≤ n^κ
  have hwhi := window_width_upper n κ (by omega) hn1   -- n^κ + n^(κ-1) ≤ (n+1)^κ
  -- dichotomy m < n^κ or m > n^κ
  rcases Nat.lt_or_ge m (n ^ κ) with hlt | hge
  · -- lower window: (n-1)^κ < m < n^κ
    left
    rw [Finset.mem_Ioo]
    have hge2 : n ^ (κ-1) ≤ n ^ κ := Nat.pow_le_pow_right (by omega) (by omega)
    refine ⟨?_, hlt⟩
    -- (n-1)^κ < m.  We have (n-1)^κ ≤ n^κ - n^(κ-1) < m
    omega
  · -- m ≥ n^κ, and m ≠ n^κ ⟹ m > n^κ
    right
    have hgt : n ^ κ < m := lt_of_le_of_ne hge (fun h => hmne h.symm)
    rw [Finset.mem_Ioo]
    refine ⟨hgt, ?_⟩
    -- m < (n+1)^κ.  m < n^κ + n^(κ-1) ≤ (n+1)^κ
    omega

/- ===== GENERAL-κ assembly additions ===== -/
open scoped BigOperators
open Real

/-- Logarithmic bound on the box-principle denominator `q`, general-κ tolerance
`δ d = 1/(2^(κ+1)·κ·D·d^{1/κ})`.  Uses `d^{1/κ} ≤ d ≤ D`. -/
theorem log_q_bound_general (κ : ℕ) (hκ : 2 ≤ κ) (D : ℕ) (hD1 : 1 ≤ D) (S : Finset ℕ)
    (hSdvd : ∀ d ∈ S, 2 ≤ d ∧ d ≤ D) (q : ℕ) (hq1 : 1 ≤ q)
    (hqbound : q ≤ ∏ i : S,
        ⌈((1 : ℝ) / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (i : ℕ) ^ ((1 : ℝ) / (κ : ℝ))))⁻¹⌉₊) :
    Real.log q ≤ (S.card : ℝ) * Real.log ((2 ^ (κ + 1) * (κ : ℝ) + 1) * (D : ℝ) ^ 2) := by
  classical
  have hDR1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD1
  have hκR : (2:ℝ) ≤ (κ:ℝ) := by exact_mod_cast hκ
  -- the "Kconst·D^2" upper bound for each ceil
  set Kc : ℝ := 2 ^ (κ + 1) * (κ : ℝ) + 1 with hKc
  have hKcpos : (0:ℝ) < Kc := by rw [hKc]; positivity
  -- positivity of the ceil for d ∈ S
  have hbasepos : ∀ d ∈ S, (0:ℝ) < 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ)) := by
    intro d hd
    obtain ⟨hd2, _⟩ := hSdvd d hd
    have : (0:ℝ) < (d:ℝ) ^ ((1:ℝ)/(κ:ℝ)) := by positivity
    positivity
  have hcpos : ∀ d ∈ S, 0 < ⌈((1 : ℝ) / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ := by
    intro d hd
    apply Nat.ceil_pos.mpr; apply inv_pos.mpr; apply one_div_pos.mpr
    exact hbasepos d hd
  -- each ceil ≤ Kc * D^2
  have hδinv : ∀ d ∈ S,
      ((⌈((1 : ℝ) / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ : ℕ) : ℝ)
        ≤ Kc * (D:ℝ)^2 := by
    intro d hd
    obtain ⟨hd2, hdD⟩ := hSdvd d hd
    have hbase := hbasepos d hd
    have hδeq : ((1 : ℝ) / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹
        = 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ)) := by
      rw [one_div, inv_inv]
    -- d^{1/κ} ≤ d
    have hdR1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    have hexple : (d:ℝ) ^ ((1:ℝ)/(κ:ℝ)) ≤ (d:ℝ) := by
      calc (d:ℝ) ^ ((1:ℝ)/(κ:ℝ)) ≤ (d:ℝ) ^ (1:ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hdR1
            rw [div_le_one (by positivity)]; linarith
        _ = (d:ℝ) := Real.rpow_one _
    have hdRle : (d:ℝ) ≤ (D:ℝ) := by exact_mod_cast hdD
    -- the real value ≤ 2^(κ+1)·κ·D·D = (2^(κ+1)·κ)·D^2
    have hval : 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ))
        ≤ 2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)^2 := by
      have hfac : (0:ℝ) ≤ 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) := by positivity
      calc 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ))
          ≤ 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (D:ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hfac
            exact le_trans hexple hdRle
        _ = 2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)^2 := by ring
    have hceil : (⌈2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ))⌉₊ : ℝ)
        ≤ 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ)) + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    rw [hδeq]
    have hD2 : (1:ℝ) ≤ (D:ℝ)^2 := by nlinarith [hDR1]
    calc (⌈2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ))⌉₊ : ℝ)
        ≤ 2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℕ) ^ ((1:ℝ)/(κ:ℝ)) + 1 := hceil
      _ ≤ 2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)^2 + 1 := by linarith [hval]
      _ ≤ 2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)^2 + 1 * (D:ℝ)^2 := by nlinarith [hD2]
      _ = Kc * (D:ℝ)^2 := by rw [hKc]; ring
  -- log q ≤ log of product
  have hprodpos : (0:ℝ) < ((∏ i : S, ⌈((1:ℝ)/(2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)*(i:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ : ℕ) : ℝ) := by
    have : 0 < ∏ i : S, ⌈((1:ℝ)/(2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)*(i:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ :=
      Finset.prod_pos (fun i _ => hcpos i i.2)
    exact_mod_cast this
  have hqle : Real.log q
      ≤ Real.log ((∏ i : S, ⌈((1:ℝ)/(2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)*(i:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ : ℕ) : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hq1); exact_mod_cast hqbound
  refine le_trans hqle ?_
  rw [show ((∏ i : S, ⌈((1:ℝ)/(2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)*(i:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ : ℕ) : ℝ)
        = ∏ i : S, ((⌈((1:ℝ)/(2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)*(i:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ : ℕ) : ℝ) by push_cast; rfl]
  rw [Real.log_prod (by intro i _; have := hcpos i i.2; positivity)]
  rw [Finset.sum_coe_sort S
    (fun d => Real.log ((⌈((1:ℝ)/(2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)*(d:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ : ℕ) : ℝ))]
  have hbd : ∀ d ∈ S,
      Real.log ((⌈((1:ℝ)/(2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)*(d:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ : ℕ) : ℝ)
        ≤ Real.log (Kc * (D:ℝ)^2) := by
    intro d hd
    apply Real.log_le_log _ (hδinv d hd)
    have := hcpos d hd; exact_mod_cast this
  calc ∑ d ∈ S, Real.log ((⌈((1:ℝ)/(2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)*(d:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ : ℕ) : ℝ)
      ≤ S.card • Real.log (Kc * (D:ℝ)^2) := Finset.sum_le_card_nsmul _ _ _ hbd
    _ = (S.card : ℝ) * Real.log (Kc * (D:ℝ)^2) := by rw [nsmul_eq_mul]

/-- General-κ injectivity-based window card bound. -/
theorem window_card_bound_general (κ D q : ℕ) (hκ : 2 ≤ κ) (hD : 1 ≤ D) (T : Finset ℕ)
    (hsq : ∀ p ∈ T, Squarefree p) (hr : ∀ p ∈ T, 1 ≤ rG p κ q)
    (W : Finset ℕ)
    (hmem : ∀ p ∈ T, (p * D ^ κ * (rG p κ q) ^ κ) ∈ W ∧ KFull κ (p * D ^ κ * (rG p κ q) ^ κ)) :
    T.card ≤ (W.filter (fun m => KFull κ m)).card := by
  classical
  have hDne : (D:ℕ) ≠ 0 := by omega
  have h_inj : Finset.card (Finset.image (fun p => p * D ^ κ * (rG p κ q) ^ κ) T) = T.card := by
    refine Finset.card_image_of_injOn fun p hp p' hp' h => ?_
    -- p * D^κ * (rG p)^κ = p' * D^κ * (rG p')^κ ⟹ p*(rG p)^κ = p'*(rG p')^κ
    have hcancel : p * (rG p κ q) ^ κ = p' * (rG p' κ q) ^ κ := by
      have hDκ : (D ^ κ) ≠ 0 := pow_ne_zero _ hDne
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hDκ)
      -- D^κ * (p*(rG p)^κ) = D^κ * (p'*(rG p')^κ)
      have e1 : D ^ κ * (p * (rG p κ q) ^ κ) = p * D ^ κ * (rG p κ q) ^ κ := by ring
      have e2 : D ^ κ * (p' * (rG p' κ q) ^ κ) = p' * D ^ κ * (rG p' κ q) ^ κ := by ring
      rw [e1, e2]; exact h
    exact (construction_injective κ p p' (rG p κ q) (rG p' κ q) hκ
      (hsq p hp) (hsq p' hp') (hr p hp) (hr p' hp') hcancel).1
  rw [← h_inj]
  apply Finset.card_le_card
  apply Finset.image_subset_iff.mpr
  intro p hp
  exact Finset.mem_filter.mpr (hmem p hp)

set_option maxHeartbeats 1000000 in
theorem powerful_count_rate_general (κ : ℕ) (hκ : 2 ≤ κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ n : ℕ, B < n ∧
      c * Real.log n / (Real.log (Real.log n) * Real.log (Real.log (Real.log n)))
        ≤ ((Finset.Ioo (n ^ κ) ((n + 1) ^ κ)).filter (fun m => KFull κ m)).card := by
  -- κ-dependent constant from log Kc, Kc = 2^(κ+1)·κ + 1
  set Kc : ℝ := 2 ^ (κ + 1) * (κ : ℝ) + 1 with hKcdef
  have hKcpos : (0:ℝ) < Kc := by rw [hKcdef]; positivity
  obtain ⟨C', hC'pos, hC'⟩ := log_primorial_le nth_prime_upper
  -- Cbig absorbs all κ-dependent constants
  set Cbig : ℝ := 100 * C' + 100 + 100 * |Real.log Kc| with hCbigdef
  have hCbigpos : 0 < Cbig := by rw [hCbigdef]; positivity
  obtain ⟨c, ℓ₀, hcpos, hinv⟩ := rate_inversion Cbig hCbigpos
  refine ⟨c, hcpos, ?_⟩
  intro B
  obtain ⟨ℓ, hℓℓ₀, hℓB, hℓlog⟩ :
      ∃ ℓ : ℕ, ℓ₀ ≤ ℓ ∧ B < ℓ ∧ (30:ℝ) ≤ Real.log ℓ := by
    refine ⟨max ℓ₀ (max (B+1) (Nat.ceil (Real.exp 30))), le_max_left _ _, ?_, ?_⟩
    · have : B + 1 ≤ max ℓ₀ (max (B+1) (Nat.ceil (Real.exp 30))) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      omega
    · have hge : Real.exp 30 ≤ (max ℓ₀ (max (B+1) (Nat.ceil (Real.exp 30))) : ℕ) := by
        have h1 : (Nat.ceil (Real.exp 30) : ℝ)
            ≤ (max ℓ₀ (max (B+1) (Nat.ceil (Real.exp 30))) : ℕ) := by
          have : Nat.ceil (Real.exp 30) ≤ max ℓ₀ (max (B+1) (Nat.ceil (Real.exp 30))) :=
            le_trans (le_max_right _ _) (le_max_right _ _)
          exact_mod_cast this
        exact le_trans (Nat.le_ceil _) h1
      have := Real.log_le_log (Real.exp_pos 30) hge
      rwa [Real.log_exp] at this
  have hℓ1 : 1 ≤ ℓ := by
    by_contra hcon
    push_neg at hcon
    interval_cases ℓ <;> simp_all <;> nlinarith [hℓlog]
  have hℓR1 : (1:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ1
  have hℓRpos : (0:ℝ) < (ℓ:ℝ) := by linarith
  have hlogℓpos : (0:ℝ) < Real.log ℓ := by linarith
  have hlogℓ1 : (1:ℝ) ≤ Real.log ℓ := by linarith
  have hloglogℓ : (3:ℝ) ≤ Real.log (Real.log ℓ) := by
    have h30 : Real.log (30:ℝ) ≤ Real.log (Real.log ℓ) := Real.log_le_log (by norm_num) hℓlog
    have hl30 : (3:ℝ) ≤ Real.log 30 := by
      have he3 : Real.exp 3 ≤ 30 := by
        have hpos := Real.exp_pos 1
        have he : Real.exp 3 = (Real.exp 1)^3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [he]
        have : (Real.exp 1)^3 ≤ (2.7182818286:ℝ)^3 :=
          pow_le_pow_left₀ hpos.le Real.exp_one_lt_d9.le 3
        nlinarith [this]
      calc (3:ℝ) = Real.log (Real.exp 3) := by rw [Real.log_exp]
        _ ≤ Real.log 30 := Real.log_le_log (Real.exp_pos 3) he3
    linarith
  have hloglogℓpos : (0:ℝ) < Real.log (Real.log ℓ) := by linarith
  obtain ⟨h, hh2, hpow, hhub⟩ :
      ∃ h : ℕ, 2 ≤ h ∧ 2 * ℓ ≤ 2 ^ h - 1 ∧ (h : ℝ) * Real.log 2 ≤ Real.log (2 * ℓ) + 2 := by
    refine ⟨Nat.log 2 (2 * ℓ) + 2, by omega, ?_, ?_⟩
    · have h1 : 2 * ℓ < 2 ^ (Nat.log 2 (2 * ℓ) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) (2 * ℓ)
      have h2 : 2 ^ (Nat.log 2 (2 * ℓ) + 1) ≤ 2 ^ (Nat.log 2 (2 * ℓ) + 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have hN : 1 ≤ 2 * ℓ := by omega
      have hkey : (Nat.log 2 (2 * ℓ) : ℝ) * Real.log 2 ≤ Real.log (2 * ℓ) := by
        have h1 : (2:ℕ) ^ (Nat.log 2 (2 * ℓ)) ≤ 2 * ℓ := Nat.pow_log_le_self 2 (by omega)
        have h2 : ((2:ℕ) ^ (Nat.log 2 (2 * ℓ)) : ℝ) ≤ ((2 * ℓ : ℕ) : ℝ) := by exact_mod_cast h1
        have h3 : Real.log ((2:ℕ) ^ (Nat.log 2 (2 * ℓ)) : ℝ) ≤ Real.log ((2 * ℓ : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) h2
        rw [show ((2:ℕ) ^ (Nat.log 2 (2 * ℓ)) : ℝ) = (2:ℝ) ^ (Nat.log 2 (2 * ℓ)) by push_cast; ring,
          Real.log_pow] at h3
        push_cast at h3 ⊢; linarith [h3]
      have hl2le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
      push_cast
      nlinarith [hkey, hl2le]
  set Dset : Finset ℕ := (Finset.range h).image (Nat.nth Nat.Prime) with hDsetdef
  set D : ℕ := ∏ p ∈ Dset, p with hDdef
  have hDset_prime : ∀ p ∈ Dset, p.Prime := by
    intro p hp; rw [hDsetdef, Finset.mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp; exact Nat.prime_nth_prime i
  have hDset_card : Dset.card = h := by
    rw [hDsetdef, Finset.card_image_of_injective _ (Nat.nth_injective Nat.infinite_setOf_prime),
      Finset.card_range]
  have hDsq : Squarefree D := by rw [hDdef]; exact squarefree_prod_primes Dset hDset_prime
  have hD1 : 1 < D := by
    rw [hDdef]
    obtain ⟨a, ha⟩ : Dset.Nonempty := Finset.card_pos.mp (by rw [hDset_card]; omega)
    calc 1 < a := (hDset_prime a ha).one_lt
      _ ≤ ∏ p ∈ Dset, p := Finset.single_le_prod' (f := fun p => p)
          (fun i hi => (hDset_prime i hi).pos) ha
  have hD : 1 ≤ D := by omega
  have hDpf : D.primeFactors.card = h := by
    rw [hDdef, Nat.primeFactors_prod hDset_prime, hDset_card]
  obtain ⟨S₀, hS₀card, hS₀prop⟩ := squarefree_many_divisors D hDsq hD1 ℓ (by rw [hDpf]; exact hpow)
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hS₀card
  have hSprop : ∀ d ∈ S, d ∣ D ∧ 1 < d ∧ Squarefree d := fun d hd => hS₀prop d (hSsub hd)
  -- Box principle: α = alphaG d κ, δ d = 1/(2^(κ+1)·κ·D·d^{1/κ})
  set α : ℕ → ℝ := fun d => alphaG d κ with hαdef
  set δ : ℕ → ℝ := fun d => 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℝ) ^ ((1:ℝ)/(κ:ℝ))) with hδdef
  have hδpos : ∀ d ∈ S, 0 < δ d := by
    intro d hd
    obtain ⟨_, hd1, _⟩ := hSprop d hd
    rw [hδdef]; apply one_div_pos.mpr
    have : (0:ℝ) < (d:ℝ) ^ ((1:ℝ)/(κ:ℝ)) := by
      have : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
      positivity
    positivity
  obtain ⟨q, hq1, hqbound, hqtol⟩ :=
    box_principle_quantitative (ι := S) (fun i => α i) (fun i => δ i) (fun i => hδpos i i.2)
  set n : ℕ := D * q with hndef
  have hn1 : 1 ≤ n := Nat.mul_pos hD hq1
  -- tolerance for each d ∈ S
  have htol : ∀ d ∈ S, |epsG d κ q| ≤ 1 / (2 ^ (κ + 1) * (κ : ℝ) * (D : ℝ) * (d:ℝ) ^ ((1:ℝ)/(κ:ℝ))) := by
    intro d hd
    have := hqtol ⟨d, hd⟩
    rw [hαdef, hδdef] at this
    simp only at this
    rw [epsG]
    convert this using 2
  have h_placement : ∀ d ∈ S, 1 ≤ rG d κ q ∧ KFull κ (d * D ^ κ * (rG d κ q) ^ κ) ∧
      ((d * D ^ κ * (rG d κ q) ^ κ) ∈ Finset.Ioo ((D * q - 1) ^ κ) ((D * q) ^ κ) ∨
       (d * D ^ κ * (rG d κ q) ^ κ) ∈ Finset.Ioo ((D * q) ^ κ) ((D * q + 1) ^ κ)) := by
    intro d hd
    obtain ⟨hdvd, hd1, hdsq⟩ := hSprop d hd
    exact placement_kfull_window_general κ D d q hκ hD (by omega) hdsq hdvd hq1 (htol d hd)
  -- pigeonhole
  set Shi := S.filter (fun d => (d * D ^ κ * (rG d κ q) ^ κ) ∈ Finset.Ioo (n ^ κ) ((n + 1) ^ κ)) with hShidef
  set Slo := S.filter (fun d => (d * D ^ κ * (rG d κ q) ^ κ) ∈ Finset.Ioo ((n - 1) ^ κ) (n ^ κ)) with hSlodef
  have h_pig : ℓ ≤ Shi.card ∨ ℓ ≤ Slo.card := by
    have hsum : Shi.card + Slo.card ≥ S.card := by
      rw [← Finset.card_union_add_card_inter]
      refine le_add_right (Finset.card_le_card fun x hx => ?_)
      have hp := h_placement x hx
      rw [hShidef, hSlodef, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hp.2.2 with hlo | hhi
      · right; refine ⟨hx, ?_⟩; rw [hndef]; exact hlo
      · left; refine ⟨hx, ?_⟩; rw [hndef]; exact hhi
    have : 2 * ℓ ≤ Shi.card + Slo.card := by omega
    omega
  -- Size bookkeeping
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hDR1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDge2pow : 2 ^ h ≤ D := by
    rw [hDdef]
    calc 2 ^ h = ∏ _p ∈ Dset, 2 := by rw [Finset.prod_const, hDset_card]
      _ ≤ ∏ p ∈ Dset, p := Finset.prod_le_prod' (fun p hp => (hDset_prime p hp).two_le)
  have h2ℓltD : 2 * ℓ < D := by
    have : 2 * ℓ + 1 ≤ 2 ^ h := by
      have h1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      omega
    omega
  have hnge : 2 * ℓ < n := by rw [hndef]; calc 2 * ℓ < D := h2ℓltD
                                              _ ≤ D * q := Nat.le_mul_of_pos_right D hq1
  have hDcast : ((D:ℕ):ℝ) = ∏ i ∈ Finset.range h, (Nat.nth Nat.Prime i : ℝ) := by
    rw [hDdef, hDsetdef, Finset.prod_image
      (by intro a _ b _ hab; exact Nat.nth_injective Nat.infinite_setOf_prime hab)]
    push_cast; rfl
  have hlogD : Real.log D ≤ C' * (h:ℝ) * Real.log h := by
    rw [hDcast]; exact hC' h hh2
  have hl2lb : (1:ℝ)/2 ≤ Real.log 2 := by
    have : Real.log (2⁻¹) ≤ (2:ℝ)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    rw [Real.log_inv] at this; linarith
  have hlog2ℓ : Real.log (2 * (ℓ:ℝ)) ≤ 1 + Real.log ℓ := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    linarith
  have hhub' : (h:ℝ) * Real.log 2 ≤ Real.log (2 * (ℓ:ℝ)) + 2 := hhub
  have hhle : (h:ℝ) ≤ 8 * Real.log ℓ := by
    have hb : (h:ℝ) * Real.log 2 ≤ 3 + Real.log ℓ := by linarith [hhub', hlog2ℓ]
    have hhpos : (0:ℝ) ≤ (h:ℝ) := by positivity
    nlinarith [hb, hl2lb, hhpos, hlogℓ1]
  have hhpos : (0:ℝ) < (h:ℝ) := by
    have : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh2
    linarith
  have hloghle : Real.log h ≤ 2 * Real.log (Real.log ℓ) := by
    have hstep : Real.log h ≤ Real.log (8 * Real.log ℓ) :=
      Real.log_le_log hhpos hhle
    have hexp : Real.log (8 * Real.log ℓ) = Real.log 8 + Real.log (Real.log ℓ) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
    have hlog8 : Real.log 8 ≤ 3 := by
      have : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; push_cast; ring
      have h2le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
      rw [this]; linarith
    rw [hexp] at hstep; linarith [hloglogℓ]
  have hlogDle : Real.log D ≤ 16 * C' * Real.log ℓ * Real.log (Real.log ℓ) := by
    have hlogDnn : (0:ℝ) ≤ Real.log D := Real.log_nonneg hDR1
    calc Real.log D ≤ C' * (h:ℝ) * Real.log h := hlogD
      _ ≤ C' * (8 * Real.log ℓ) * (2 * Real.log (Real.log ℓ)) := by
          have hloghnn : (0:ℝ) ≤ Real.log h := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ h))
          have hhnn : (0:ℝ) ≤ (h:ℝ) := by positivity
          have hloglognn : (0:ℝ) ≤ Real.log (Real.log ℓ) := by linarith [hloglogℓ]
          have hlogℓnn : (0:ℝ) ≤ Real.log ℓ := by linarith
          have e1 : C' * (h:ℝ) * Real.log h ≤ C' * (8 * Real.log ℓ) * Real.log h := by
            apply mul_le_mul_of_nonneg_right _ hloghnn
            exact mul_le_mul_of_nonneg_left hhle hC'pos.le
          have e2 : C' * (8 * Real.log ℓ) * Real.log h
              ≤ C' * (8 * Real.log ℓ) * (2 * Real.log (Real.log ℓ)) := by
            apply mul_le_mul_of_nonneg_left hloghle
            positivity
          linarith [e1, e2]
      _ = 16 * C' * Real.log ℓ * Real.log (Real.log ℓ) := by ring
  -- log q bound (general κ)
  have hlogq : Real.log q ≤ 2 * (ℓ:ℝ) * Real.log (Kc * (D:ℝ)^2) := by
    have hSdvd : ∀ d ∈ S, 2 ≤ d ∧ d ≤ D := by
      intro d hd
      obtain ⟨hdvd, hd1, _⟩ := hSprop d hd
      exact ⟨by omega, Nat.le_of_dvd (by omega) hdvd⟩
    have hqbound' : q ≤ ∏ i : S,
        ⌈((1:ℝ)/(2 ^ (κ + 1) * (κ : ℝ) * (D:ℝ)*(i:ℕ) ^ ((1:ℝ)/(κ:ℝ))))⁻¹⌉₊ := by
      convert hqbound using 2
    have := log_q_bound_general κ hκ D hD S hSdvd q hq1 hqbound'
    rw [hScard] at this
    calc Real.log q ≤ ((2 * ℓ : ℕ) : ℝ) * Real.log (Kc * (D:ℝ)^2) := by
            rw [hKcdef]; exact this
      _ = 2 * (ℓ:ℝ) * Real.log (Kc * (D:ℝ)^2) := by push_cast; ring
  -- combine into overall size bound on log n
  have hlogDnn : (0:ℝ) ≤ Real.log D := Real.log_nonneg hDR1
  have hloglogℓnn : (0:ℝ) ≤ Real.log (Real.log ℓ) := by linarith [hloglogℓ]
  have hprod90 : (90:ℝ) ≤ Real.log ℓ * Real.log (Real.log ℓ) := by
    nlinarith [hℓlog, hloglogℓ, hlogℓpos]
  have hPnn : (0:ℝ) ≤ Real.log ℓ * Real.log (Real.log ℓ) := by positivity
  have hP1 : (1:ℝ) ≤ Real.log ℓ * Real.log (Real.log ℓ) := by linarith [hprod90]
  -- log(Kc·D^2) = log Kc + 2 log D ≤ |log Kc|·P + 2·16C'·P
  have hlogKcD : Real.log (Kc * (D:ℝ)^2)
      ≤ (|Real.log Kc| + 32 * C') * (Real.log ℓ * Real.log (Real.log ℓ)) := by
    have heq : Real.log (Kc * (D:ℝ)^2) = Real.log Kc + 2 * Real.log D := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
    rw [heq]
    have h1 : Real.log Kc ≤ |Real.log Kc| * (Real.log ℓ * Real.log (Real.log ℓ)) := by
      calc Real.log Kc ≤ |Real.log Kc| := le_abs_self _
        _ = |Real.log Kc| * 1 := by ring
        _ ≤ |Real.log Kc| * (Real.log ℓ * Real.log (Real.log ℓ)) := by
            apply mul_le_mul_of_nonneg_left hP1 (abs_nonneg _)
    have h2 : 2 * Real.log D ≤ 32 * C' * (Real.log ℓ * Real.log (Real.log ℓ)) := by
      nlinarith [hlogDle]
    nlinarith [h1, h2]
  have hncast : ((n:ℕ):ℝ) = (D:ℝ) * (q:ℝ) := by rw [hndef]; push_cast; ring
  have hlogn : Real.log n = Real.log D + Real.log q := by
    rw [hncast, Real.log_mul (by positivity) (by positivity)]
  have hsize : Real.log n ≤ Cbig * (ℓ:ℝ) * Real.log ℓ * Real.log (Real.log ℓ) := by
    rw [hlogn]
    have hDpart : Real.log D ≤ 16 * C' * (ℓ:ℝ) * (Real.log ℓ * Real.log (Real.log ℓ)) := by
      calc Real.log D ≤ 16 * C' * (Real.log ℓ * Real.log (Real.log ℓ)) := by
            nlinarith [hlogDle]
        _ ≤ 16 * C' * (ℓ:ℝ) * (Real.log ℓ * Real.log (Real.log ℓ)) := by
            nlinarith [hPnn, hC'pos, hℓR1]
    have hqpart : Real.log q
        ≤ 2 * (|Real.log Kc| + 32 * C') * (ℓ:ℝ) * (Real.log ℓ * Real.log (Real.log ℓ)) := by
      calc Real.log q ≤ 2 * (ℓ:ℝ) * Real.log (Kc * (D:ℝ)^2) := hlogq
        _ ≤ 2 * (ℓ:ℝ) * ((|Real.log Kc| + 32 * C') * (Real.log ℓ * Real.log (Real.log ℓ))) := by
            apply mul_le_mul_of_nonneg_left hlogKcD (by positivity)
        _ = 2 * (|Real.log Kc| + 32 * C') * (ℓ:ℝ) * (Real.log ℓ * Real.log (Real.log ℓ)) := by ring
    have hcoeff : 16 * C' + 2 * (|Real.log Kc| + 32 * C') ≤ Cbig := by
      rw [hCbigdef]; nlinarith [hC'pos, abs_nonneg (Real.log Kc)]
    nlinarith [hDpart, hqpart, hPnn, hℓRpos, mul_le_mul_of_nonneg_right hcoeff
      (mul_nonneg hℓRpos.le hPnn)]
  -- finishing step
  have hee : Real.exp (Real.exp 1) ≤ 30 := by
    have h1 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; linarith
    calc Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr h1
      _ ≤ 30 := by
          have hpos := Real.exp_pos 1
          have he : Real.exp 3 = (Real.exp 1)^3 := by rw [← Real.exp_nat_mul]; norm_num
          rw [he]
          have : (Real.exp 1)^3 ≤ (2.7182818286:ℝ)^3 :=
            pow_le_pow_left₀ hpos.le Real.exp_one_lt_d9.le 3
          nlinarith [this]
  have hfinish : ∀ N : ℕ, B < N → N ≤ n → 2 * ℓ ≤ N + 1 →
      ℓ ≤ ((Finset.Ioo (N^κ) ((N+1)^κ)).filter (fun m => KFull κ m)).card →
      ∃ n : ℕ, B < n ∧
        c * Real.log n / (Real.log (Real.log n) * Real.log (Real.log (Real.log n)))
          ≤ ((Finset.Ioo (n^κ) ((n+1)^κ)).filter (fun m => KFull κ m)).card := by
    intro N hNB hNn hNℓ hcount
    refine ⟨N, hNB, ?_⟩
    set X : ℝ := Real.log N with hXdef
    have hNpos : 0 < N := by omega
    have hNR1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
    have hNgeℓ : (ℓ:ℝ) ≤ (N:ℝ) := by
      have : ℓ ≤ N := by omega
      exact_mod_cast this
    have hXge : (30:ℝ) ≤ X := by
      rw [hXdef]; exact le_trans hℓlog (Real.log_le_log hℓRpos hNgeℓ)
    have hXee : Real.exp (Real.exp 1) ≤ X := le_trans hee hXge
    have hXlen : X ≤ Real.log n := by
      rw [hXdef]; exact Real.log_le_log (by exact_mod_cast hNpos) (by exact_mod_cast hNn)
    have hXub : X ≤ Cbig * (ℓ:ℝ) * Real.log ℓ * Real.log (Real.log ℓ) := le_trans hXlen hsize
    have hinv' := hinv ℓ X hℓℓ₀ hXee hXub
    have hgoaleq : c * Real.log N / (Real.log (Real.log N) * Real.log (Real.log (Real.log N)))
        = c * X / (Real.log X * Real.log (Real.log X)) := by rw [hXdef]
    rw [hgoaleq]
    calc c * X / (Real.log X * Real.log (Real.log X)) ≤ (ℓ:ℝ) := hinv'
      _ ≤ ((Finset.Ioo (N^κ) ((N+1)^κ)).filter (fun m => KFull κ m)).card := by
          exact_mod_cast hcount
  -- dispatch via pigeonhole
  rcases h_pig with hhi | hlo
  · apply hfinish n (by omega) (le_refl n) (by omega)
    refine le_trans hhi ?_
    apply window_card_bound_general κ D q hκ hD Shi
    · exact fun p hp => (hSprop p (Finset.filter_subset _ _ hp)).2.2
    · exact fun p hp => (h_placement p (Finset.filter_subset _ _ hp)).1
    · refine fun p hp => ⟨?_, (h_placement p (Finset.mem_filter.mp hp).1).2.1⟩
      have := (Finset.mem_filter.mp hp).2; rw [hndef] at this ⊢; exact this
  · have hn1' : (n - 1) + 1 = n := by omega
    apply hfinish (n - 1) (by omega) (by omega) (by omega)
    have hwin : Finset.Ioo ((n-1)^κ) (((n-1)+1)^κ) = Finset.Ioo ((n-1)^κ) (n^κ) := by rw [hn1']
    rw [hwin]
    refine le_trans hlo ?_
    apply window_card_bound_general κ D q hκ hD Slo
    · exact fun p hp => (hSprop p (Finset.filter_subset _ _ hp)).2.2
    · exact fun p hp => (h_placement p (Finset.filter_subset _ _ hp)).1
    · refine fun p hp => ⟨?_, (h_placement p (Finset.mem_filter.mp hp).1).2.1⟩
      have := (Finset.mem_filter.mp hp).2; rw [hndef] at this ⊢; exact this


/-- The $\kappa=2$ case (Erdős Problem #942): the powerful-number rate, as a corollary of the
general theorem. -/
theorem powerful_count_rate :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ n : ℕ, B < n ∧
      c * Real.log n / (Real.log (Real.log n) * Real.log (Real.log (Real.log n)))
        ≤ ((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun m => KFull 2 m)).card :=
  powerful_count_rate_general 2 (by norm_num)
