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

/-- Logarithmic bound on the box-principle denominator `q`. -/
theorem log_q_bound (D : ℕ) (hD1 : 1 ≤ D) (S : Finset ℕ)
    (hSdvd : ∀ d ∈ S, 2 ≤ d ∧ d ≤ D) (q : ℕ) (hq1 : 1 ≤ q)
    (hqbound : q ≤ ∏ i : S, ⌈((1 : ℝ) / (16 * (D : ℝ) * Real.sqrt (i : ℕ)))⁻¹⌉₊) :
    Real.log q ≤ (S.card : ℝ) * Real.log (17 * (D : ℝ) ^ 2) := by
  classical
  have hDR1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD1
  -- positivity of the ceil for d ∈ S
  have hcpos : ∀ d ∈ S, 0 < ⌈((1 : ℝ) / (16 * (D : ℝ) * Real.sqrt (d:ℕ)))⁻¹⌉₊ := by
    intro d hd
    obtain ⟨hd2, _⟩ := hSdvd d hd
    apply Nat.ceil_pos.mpr; apply inv_pos.mpr; apply one_div_pos.mpr
    have : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    positivity
  -- each ceil ≤ 17 D^2
  have hδinv : ∀ d ∈ S,
      ((⌈((1 : ℝ) / (16 * (D : ℝ) * Real.sqrt (d:ℕ)))⁻¹⌉₊ : ℕ) : ℝ) ≤ 17 * (D:ℝ)^2 := by
    intro d hd
    obtain ⟨hd2, hdD⟩ := hSdvd d hd
    have hδeq : ((1 : ℝ) / (16 * (D : ℝ) * Real.sqrt (d:ℕ)))⁻¹ = 16 * (D:ℝ) * Real.sqrt d := by
      rw [one_div, inv_inv]
    rw [hδeq]
    have hsd : Real.sqrt d ≤ Real.sqrt D := Real.sqrt_le_sqrt (by exact_mod_cast hdD)
    have hsD : Real.sqrt D ≤ D := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (D:ℝ) by positivity), Real.sqrt_nonneg (D:ℝ),
        Real.sqrt_le_sqrt (show (1:ℝ) ≤ (D:ℝ) from hDR1), Real.sqrt_one]
    have hsd1 : (1:ℝ) ≤ Real.sqrt d := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; apply Real.sqrt_le_sqrt
      exact_mod_cast (by omega : (1:ℕ) ≤ d)
    have hceil : (⌈(16 * (D:ℝ) * Real.sqrt d)⌉₊ : ℝ) ≤ 16 * (D:ℝ) * Real.sqrt d + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    nlinarith [hsd, hsD, hsd1, hDR1, Real.sqrt_nonneg (d:ℝ), hceil]
  -- log q ≤ log of product
  have hprodpos : (0:ℝ) < ((∏ i : S, ⌈((1:ℝ)/(16*(D:ℝ)*Real.sqrt (i:ℕ)))⁻¹⌉₊ : ℕ) : ℝ) := by
    have : 0 < ∏ i : S, ⌈((1:ℝ)/(16*(D:ℝ)*Real.sqrt (i:ℕ)))⁻¹⌉₊ :=
      Finset.prod_pos (fun i _ => hcpos i i.2)
    exact_mod_cast this
  have hqle : Real.log q
      ≤ Real.log ((∏ i : S, ⌈((1:ℝ)/(16*(D:ℝ)*Real.sqrt (i:ℕ)))⁻¹⌉₊ : ℕ) : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hq1); exact_mod_cast hqbound
  refine le_trans hqle ?_
  rw [show ((∏ i : S, ⌈((1:ℝ)/(16*(D:ℝ)*Real.sqrt (i:ℕ)))⁻¹⌉₊ : ℕ) : ℝ)
        = ∏ i : S, ((⌈((1:ℝ)/(16*(D:ℝ)*Real.sqrt (i:ℕ)))⁻¹⌉₊ : ℕ) : ℝ) by push_cast; rfl]
  rw [Real.log_prod (by
    intro i _; have := hcpos i i.2; positivity)]
  rw [Finset.sum_coe_sort S
    (fun d => Real.log ((⌈((1:ℝ)/(16*(D:ℝ)*Real.sqrt (d:ℕ)))⁻¹⌉₊ : ℕ) : ℝ))]
  have hbd : ∀ d ∈ S,
      Real.log ((⌈((1:ℝ)/(16*(D:ℝ)*Real.sqrt (d:ℕ)))⁻¹⌉₊ : ℕ) : ℝ) ≤ Real.log (17 * (D:ℝ)^2) := by
    intro d hd
    apply Real.log_le_log _ (hδinv d hd)
    have := hcpos d hd; exact_mod_cast this
  calc ∑ d ∈ S, Real.log ((⌈((1:ℝ)/(16*(D:ℝ)*Real.sqrt (d:ℕ)))⁻¹⌉₊ : ℕ) : ℝ)
      ≤ S.card • Real.log (17 * (D:ℝ)^2) := Finset.sum_le_card_nsmul _ _ _ hbd
    _ = (S.card : ℝ) * Real.log (17 * (D:ℝ)^2) := by rw [nsmul_eq_mul]

set_option maxHeartbeats 1000000 in
theorem powerful_count_rate :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ n : ℕ, B < n ∧
      c * Real.log n / (Real.log (Real.log n) * Real.log (Real.log (Real.log n)))
        ≤ ((Finset.Ioo (n^2) ((n+1)^2)).filter (fun m => KFull 2 m)).card := by
  -- Fix the constants once.
  obtain ⟨C', hC'pos, hC'⟩ := log_primorial_le nth_prime_upper
  set Cbig : ℝ := 100 * C' + 100 with hCbigdef
  have hCbigpos : 0 < Cbig := by rw [hCbigdef]; positivity
  obtain ⟨c, ℓ₀, hcpos, hinv⟩ := rate_inversion Cbig hCbigpos
  refine ⟨c, hcpos, ?_⟩
  intro B
  -- Choose ℓ very large: bigger than ℓ₀, B, and with `Real.log ℓ ≥ 30`.
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
  -- ℓ ≥ exp 30 > 1.
  have hℓ1 : 1 ≤ ℓ := by
    by_contra hcon
    push_neg at hcon
    interval_cases ℓ <;> simp_all <;> nlinarith [hℓlog]
  have hℓR1 : (1:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ1
  -- positivity / size facts about ℓ.
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
  -- h := Nat.log 2 (2*ℓ) + 2, kept abstract via its key properties.
  obtain ⟨h, hh2, hpow, hhub⟩ :
      ∃ h : ℕ, 2 ≤ h ∧ 2 * ℓ ≤ 2 ^ h - 1 ∧ (h : ℝ) * Real.log 2 ≤ Real.log (2 * ℓ) + 2 := by
    refine ⟨Nat.log 2 (2 * ℓ) + 2, by omega, ?_, ?_⟩
    · have h1 : 2 * ℓ < 2 ^ (Nat.log 2 (2 * ℓ) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) (2 * ℓ)
      have h2 : 2 ^ (Nat.log 2 (2 * ℓ) + 1) ≤ 2 ^ (Nat.log 2 (2 * ℓ) + 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · -- (log₂(2ℓ)+2)·log2 = log₂(2ℓ)·log2 + 2 log2 ≤ log(2ℓ) + 2 log2
      have hN : 1 ≤ 2 * ℓ := by omega
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
  -- D as a product over the image finset of the first h primes.
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
  -- Many squarefree divisors of D.
  obtain ⟨S₀, hS₀card, hS₀prop⟩ := squarefree_many_divisors D hDsq hD1 ℓ (by rw [hDpf]; exact hpow)
  -- Shrink to exactly 2*ℓ.
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hS₀card
  have hSprop : ∀ d ∈ S, d ∣ D ∧ 1 < d ∧ Squarefree d := fun d hd => hS₀prop d (hSsub hd)
  -- Box principle to find q.
  set α : ℕ → ℝ := fun d => 1 / Real.sqrt d with hαdef
  set δ : ℕ → ℝ := fun d => 1 / (16 * (D : ℝ) * Real.sqrt d) with hδdef
  have hδpos : ∀ d ∈ S, 0 < δ d := by
    intro d hd
    obtain ⟨_, hd1, _⟩ := hSprop d hd
    rw [hδdef]; apply one_div_pos.mpr
    have : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    positivity
  obtain ⟨q, hq1, hqbound, hqtol⟩ :=
    box_principle_quantitative (ι := S) (fun i => α i) (fun i => δ i) (fun i => hδpos i i.2)
  set n : ℕ := D * q with hndef
  have hn1 : 1 ≤ n := Nat.mul_pos hD hq1
  -- placement for each d ∈ S
  have htol : ∀ d ∈ S, |epsOf d q| ≤ 1 / (16 * (D : ℝ) * Real.sqrt d) := by
    intro d hd
    have := hqtol ⟨d, hd⟩
    rw [hαdef, hδdef] at this
    simp only at this
    rw [epsOf]
    convert this using 2
  have h_placement : ∀ d ∈ S, 1 ≤ rOf d q ∧ KFull 2 (mOf D d q) ∧
      (mOf D d q ∈ Finset.Ioo ((D * q - 1) ^ 2) ((D * q) ^ 2) ∨
       mOf D d q ∈ Finset.Ioo ((D * q) ^ 2) ((D * q + 1) ^ 2)) := by
    intro d hd
    obtain ⟨hdvd, hd1, hdsq⟩ := hSprop d hd
    exact placement_kfull_window D d q hD (by omega) hdsq hdvd hq1 (htol d hd)
  -- pigeonhole
  set Shi := S.filter (fun d => mOf D d q ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2)) with hShidef
  set Slo := S.filter (fun d => mOf D d q ∈ Finset.Ioo ((n - 1) ^ 2) (n ^ 2)) with hSlodef
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
  -- ===== Size bookkeeping =====
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hDR1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  -- D ≥ 2^h ≥ 2ℓ+1 (product of h primes, each ≥ 2).
  have hDge2pow : 2 ^ h ≤ D := by
    rw [hDdef]
    calc 2 ^ h = ∏ _p ∈ Dset, 2 := by rw [Finset.prod_const, hDset_card]
      _ ≤ ∏ p ∈ Dset, p := Finset.prod_le_prod' (fun p hp => (hDset_prime p hp).two_le)
  have h2ℓltD : 2 * ℓ < D := by
    have : 2 * ℓ + 1 ≤ 2 ^ h := by
      have h1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      omega
    omega
  -- n large.
  have hnge : 2 * ℓ < n := by rw [hndef]; calc 2 * ℓ < D := h2ℓltD
                                              _ ≤ D * q := Nat.le_mul_of_pos_right D hq1
  -- (D:ℝ) = ∏ i ∈ range h, (nth Prime i : ℝ)
  have hDcast : ((D:ℕ):ℝ) = ∏ i ∈ Finset.range h, (Nat.nth Nat.Prime i : ℝ) := by
    rw [hDdef, hDsetdef, Finset.prod_image
      (by intro a _ b _ hab; exact Nat.nth_injective Nat.infinite_setOf_prime hab)]
    push_cast; rfl
  -- log D ≤ C' * h * log h
  have hlogD : Real.log D ≤ C' * (h:ℝ) * Real.log h := by
    rw [hDcast]; exact hC' h hh2
  -- bound h ≤ 8 log ℓ and log h ≤ 2 loglog ℓ.
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
    -- (h)·log2 ≤ log(2ℓ)+2 ≤ 3 + log ℓ ; log2 ≥ 1/2 ⇒ h ≤ 2(3+logℓ) = 6+2logℓ ≤ 8 log ℓ
    have hb : (h:ℝ) * Real.log 2 ≤ 3 + Real.log ℓ := by linarith [hhub', hlog2ℓ]
    have hhpos : (0:ℝ) ≤ (h:ℝ) := by positivity
    nlinarith [hb, hl2lb, hhpos, hlogℓ1]
  have hhpos : (0:ℝ) < (h:ℝ) := by
    have : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh2
    linarith
  have hloghle : Real.log h ≤ 2 * Real.log (Real.log ℓ) := by
    -- log h ≤ log(8 log ℓ) = log 8 + loglog ℓ ≤ 3 + loglog ℓ ≤ 2 loglog ℓ
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
  -- combine: log D ≤ C' * (8 log ℓ) * (2 loglog ℓ) = 16 C' log ℓ loglog ℓ
  have hlogDle : Real.log D ≤ 16 * C' * Real.log ℓ * Real.log (Real.log ℓ) := by
    have hlogDnn : (0:ℝ) ≤ Real.log D := Real.log_nonneg hDR1
    calc Real.log D ≤ C' * (h:ℝ) * Real.log h := hlogD
      _ ≤ C' * (8 * Real.log ℓ) * (2 * Real.log (Real.log ℓ)) := by
          have hloghnn : (0:ℝ) ≤ Real.log h := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ h))
          have hhnn : (0:ℝ) ≤ (h:ℝ) := by positivity
          have hloglognn : (0:ℝ) ≤ Real.log (Real.log ℓ) := by linarith [hloglogℓ]
          have hlogℓnn : (0:ℝ) ≤ Real.log ℓ := by linarith
          -- C'·h·logh ≤ C'·(8logℓ)·(2 loglogℓ)
          have e1 : C' * (h:ℝ) * Real.log h ≤ C' * (8 * Real.log ℓ) * Real.log h := by
            apply mul_le_mul_of_nonneg_right _ hloghnn
            exact mul_le_mul_of_nonneg_left hhle hC'pos.le
          have e2 : C' * (8 * Real.log ℓ) * Real.log h
              ≤ C' * (8 * Real.log ℓ) * (2 * Real.log (Real.log ℓ)) := by
            apply mul_le_mul_of_nonneg_left hloghle
            positivity
          linarith [e1, e2]
      _ = 16 * C' * Real.log ℓ * Real.log (Real.log ℓ) := by ring
  -- ===== log q bound (via standalone lemma) =====
  have hlogq : Real.log q ≤ 2 * (ℓ:ℝ) * Real.log (17 * (D:ℝ)^2) := by
    have hSdvd : ∀ d ∈ S, 2 ≤ d ∧ d ≤ D := by
      intro d hd
      obtain ⟨hdvd, hd1, _⟩ := hSprop d hd
      exact ⟨by omega, Nat.le_of_dvd (by omega) hdvd⟩
    have hqbound' : q ≤ ∏ i : S, ⌈((1:ℝ)/(16*(D:ℝ)*Real.sqrt (i:ℕ)))⁻¹⌉₊ := by
      convert hqbound using 2
    have := log_q_bound D hD S hSdvd q hq1 hqbound'
    rw [hScard] at this
    calc Real.log q ≤ ((2 * ℓ : ℕ) : ℝ) * Real.log (17 * (D:ℝ)^2) := this
      _ = 2 * (ℓ:ℝ) * Real.log (17 * (D:ℝ)^2) := by push_cast; ring
  -- ===== combine into overall size bound on log n =====
  have hlogDnn : (0:ℝ) ≤ Real.log D := Real.log_nonneg hDR1
  have hloglogℓnn : (0:ℝ) ≤ Real.log (Real.log ℓ) := by linarith [hloglogℓ]
  have hprod90 : (90:ℝ) ≤ Real.log ℓ * Real.log (Real.log ℓ) := by
    nlinarith [hℓlog, hloglogℓ, hlogℓpos]
  -- log(17 D^2) = log 17 + 2 log D ≤ logℓloglogℓ + 2·16C'·logℓloglogℓ
  have hlog17D : Real.log (17 * (D:ℝ)^2)
      ≤ (1 + 32 * C') * (Real.log ℓ * Real.log (Real.log ℓ)) := by
    have heq : Real.log (17 * (D:ℝ)^2) = Real.log 17 + 2 * Real.log D := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have hlog17 : Real.log 17 ≤ 90 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 17 by norm_num); linarith
    rw [heq]
    have h1 : Real.log 17 ≤ Real.log ℓ * Real.log (Real.log ℓ) := le_trans hlog17 hprod90
    have h2 : 2 * Real.log D ≤ 32 * C' * (Real.log ℓ * Real.log (Real.log ℓ)) := by
      have := hlogDle
      nlinarith [hlogDle]
    nlinarith [h1, h2]
  -- log n = log D + log q
  have hncast : ((n:ℕ):ℝ) = (D:ℝ) * (q:ℝ) := by rw [hndef]; push_cast; ring
  have hlogn : Real.log n = Real.log D + Real.log q := by
    rw [hncast, Real.log_mul (by positivity) (by positivity)]
  have hℓRpos' : (0:ℝ) < (ℓ:ℝ) := hℓRpos
  have hsize : Real.log n ≤ Cbig * (ℓ:ℝ) * Real.log ℓ * Real.log (Real.log ℓ) := by
    rw [hlogn]
    -- log D ≤ 16C'·P ≤ 16C'·ℓ·P  (since ℓ ≥ 1)
    have hDpart : Real.log D ≤ 16 * C' * (ℓ:ℝ) * (Real.log ℓ * Real.log (Real.log ℓ)) := by
      have hPnn : (0:ℝ) ≤ Real.log ℓ * Real.log (Real.log ℓ) := by positivity
      calc Real.log D ≤ 16 * C' * (Real.log ℓ * Real.log (Real.log ℓ)) := by
            nlinarith [hlogDle]
        _ ≤ 16 * C' * (ℓ:ℝ) * (Real.log ℓ * Real.log (Real.log ℓ)) := by
            nlinarith [hPnn, hC'pos, hℓR1]
    -- log q ≤ 2ℓ·log(17D^2) ≤ 2ℓ·(1+32C')·P
    have hqpart : Real.log q ≤ 2 * (1 + 32 * C') * (ℓ:ℝ) * (Real.log ℓ * Real.log (Real.log ℓ)) := by
      have hPnn : (0:ℝ) ≤ Real.log ℓ * Real.log (Real.log ℓ) := by positivity
      calc Real.log q ≤ 2 * (ℓ:ℝ) * Real.log (17 * (D:ℝ)^2) := hlogq
        _ ≤ 2 * (ℓ:ℝ) * ((1 + 32 * C') * (Real.log ℓ * Real.log (Real.log ℓ))) := by
            apply mul_le_mul_of_nonneg_left hlog17D (by positivity)
        _ = 2 * (1 + 32 * C') * (ℓ:ℝ) * (Real.log ℓ * Real.log (Real.log ℓ)) := by ring
    -- combine; Cbig = 100C'+100 ≥ 16C' + 2(1+32C') = 80C'+2
    have hPnn : (0:ℝ) ≤ Real.log ℓ * Real.log (Real.log ℓ) := by positivity
    have hcoeff : 16 * C' + 2 * (1 + 32 * C') ≤ Cbig := by rw [hCbigdef]; nlinarith [hC'pos]
    nlinarith [hDpart, hqpart, hPnn, hℓRpos, mul_le_mul_of_nonneg_right hcoeff
      (mul_nonneg hℓRpos.le hPnn)]
  -- ===== generic finishing step at index N =====
  -- exp(exp 1) ≤ 30
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
      ℓ ≤ ((Finset.Ioo (N^2) ((N+1)^2)).filter (fun m => KFull 2 m)).card →
      ∃ n : ℕ, B < n ∧
        c * Real.log n / (Real.log (Real.log n) * Real.log (Real.log (Real.log n)))
          ≤ ((Finset.Ioo (n^2) ((n+1)^2)).filter (fun m => KFull 2 m)).card := by
    intro N hNB hNn hNℓ hcount
    refine ⟨N, hNB, ?_⟩
    set X : ℝ := Real.log N with hXdef
    -- N ≥ 2ℓ - 1 ≥ ... ; need log N ≥ exp(exp 1) and ≤ Cbig·...
    have hNpos : 0 < N := by omega
    have hNR1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
    -- log N ≥ log ℓ ≥ 30 :  N+1 ≥ 2ℓ so N ≥ 2ℓ - 1 ≥ ℓ (since ℓ ≥ 1)
    have hNgeℓ : (ℓ:ℝ) ≤ (N:ℝ) := by
      have : ℓ ≤ N := by omega
      exact_mod_cast this
    have hXge : (30:ℝ) ≤ X := by
      rw [hXdef]; exact le_trans hℓlog (Real.log_le_log hℓRpos hNgeℓ)
    have hXee : Real.exp (Real.exp 1) ≤ X := le_trans hee hXge
    -- X ≤ log n ≤ Cbig·ℓ·logℓ·loglogℓ
    have hXlen : X ≤ Real.log n := by
      rw [hXdef]; exact Real.log_le_log (by exact_mod_cast hNpos) (by exact_mod_cast hNn)
    have hXub : X ≤ Cbig * (ℓ:ℝ) * Real.log ℓ * Real.log (Real.log ℓ) := le_trans hXlen hsize
    have hinv' := hinv ℓ X hℓℓ₀ hXee hXub
    -- goal LHS = c*X/(logX*loglogX); note log N = X
    have hgoaleq : c * Real.log N / (Real.log (Real.log N) * Real.log (Real.log (Real.log N)))
        = c * X / (Real.log X * Real.log (Real.log X)) := by rw [hXdef]
    rw [hgoaleq]
    calc c * X / (Real.log X * Real.log (Real.log X)) ≤ (ℓ:ℝ) := hinv'
      _ ≤ ((Finset.Ioo (N^2) ((N+1)^2)).filter (fun m => KFull 2 m)).card := by
          exact_mod_cast hcount
  -- ===== dispatch via pigeonhole =====
  have hnleq : n ≤ n := le_refl n
  rcases h_pig with hhi | hlo
  · -- Shi side: N = n
    apply hfinish n (by omega) (le_refl n) (by omega)
    refine le_trans hhi ?_
    convert window_card_bound D q hD Shi _ _ _ _ using 2
    · exact fun p hp => (hSprop p (Finset.filter_subset _ _ hp)).2.2
    · exact fun p hp => (h_placement p (Finset.filter_subset _ _ hp)).1
    · refine fun p hp => ⟨?_, (h_placement p (Finset.mem_filter.mp hp).1).2.1⟩
      have := (Finset.mem_filter.mp hp).2; rw [hndef] at this ⊢; exact this
  · -- Slo side: N = n-1, window (n-1)^2..n^2 = (N)^2..(N+1)^2
    have hn1 : (n - 1) + 1 = n := by omega
    apply hfinish (n - 1) (by omega) (by omega) (by omega)
    have hwin : Finset.Ioo ((n-1)^2) (((n-1)+1)^2) = Finset.Ioo ((n-1)^2) (n^2) := by rw [hn1]
    rw [hwin]
    refine le_trans hlo ?_
    convert window_card_bound D q hD Slo _ _ _ _ using 2
    · exact fun p hp => (hSprop p (Finset.filter_subset _ _ hp)).2.2
    · exact fun p hp => (h_placement p (Finset.filter_subset _ _ hp)).1
    · refine fun p hp => ⟨?_, (h_placement p (Finset.mem_filter.mp hp).1).2.1⟩
      have := (Finset.mem_filter.mp hp).2; rw [hndef] at this ⊢; exact this
