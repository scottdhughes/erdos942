import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- A natural number `m` is `κ`-full if every prime dividing it does so to the power `κ`.
For `κ = 2` these are the classical powerful (squarefull) numbers. -/
def KFull (κ m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ κ ∣ m

/-
THEOREM 1. The construction `d * D^κ * r^κ` is always `κ`-full whenever `d ∣ D`.
-/
theorem kfull_construction (κ d D r : ℕ) (hdD : d ∣ D) :
    KFull κ (d * D ^ κ * r ^ κ) := by
  intro p pp dp; simp_all +decide [ mul_assoc, Nat.Prime.dvd_mul ] ;
  rcases dp with ( dp | dp | dp );
  · exact dvd_mul_of_dvd_right ( dvd_mul_of_dvd_left ( pow_dvd_pow_of_dvd ( dvd_trans dp hdD ) _ ) _ ) _;
  · exact dvd_mul_of_dvd_right ( dvd_mul_of_dvd_left ( pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) _ ) _ ) _;
  · exact dvd_mul_of_dvd_right ( dvd_mul_of_dvd_right ( pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) _ ) _ ) _

/-
THEOREM 2. Distinctness of the construction via valuations mod `κ`.
-/
theorem construction_injective (κ d₁ d₂ r₁ r₂ : ℕ) (hκ : 2 ≤ κ)
    (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂) (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (h : d₁ * r₁ ^ κ = d₂ * r₂ ^ κ) : d₁ = d₂ ∧ r₁ = r₂ := by
  -- For every prime p, apply Nat.factorization to both sides of h: factorization (d₁ * r₁^κ) p = factorization (d₂ * r₂^κ) p.
  have h_factorization : ∀ p, p.Prime → (Nat.factorization d₁ p + κ * Nat.factorization r₁ p) = (Nat.factorization d₂ p + κ * Nat.factorization r₂ p) := by
    intro p pp; apply_fun fun x => x.factorization p at h; simp_all +decide [ Nat.factorization_mul, show d₁ ≠ 0 by aesop_cat, show r₁ ≠ 0 by aesop_cat, show d₂ ≠ 0 by aesop_cat, show r₂ ≠ 0 by aesop_cat ] ;
  -- Squarefreeness gives dᵢ.factorization p ≤ 1 (Nat.Squarefree.factorization_le_one). Reduce mod κ (κ ≥ 2): since dᵢ.factorization p ≤ 1 < κ, dᵢ.factorization p = (dᵢ.factorization p + κ * ...) % κ. Thus d₁.factorization p % κ = d₂.factorization p % κ, and since both are < κ they are equal: d₁.factorization p = d₂.factorization p for every prime p.
  have h_factorization_eq : ∀ p, p.Prime → Nat.factorization d₁ p = Nat.factorization d₂ p := by
    intro p pp; specialize h_factorization p pp; have := congr_arg ( · % κ ) h_factorization; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hκ ] at this;
    exact Nat.mod_eq_of_lt ( show d₁.factorization p < κ from lt_of_le_of_lt ( Nat.le_of_lt_succ <| Nat.lt_succ_of_le <| Nat.le_of_not_lt fun h => by have := hd₁.natFactorization_le_one p; linarith ) hκ ) ▸ Nat.mod_eq_of_lt ( show d₂.factorization p < κ from lt_of_le_of_lt ( Nat.le_of_lt_succ <| Nat.lt_succ_of_le <| Nat.le_of_not_lt fun h => by have := hd₂.natFactorization_le_one p; linarith ) hκ ) ▸ this;
  -- Hence by Nat.eq_iff_factorization_eq (or Nat.factorization_inj) for positive d₁ d₂, d₁ = d₂.
  have h_eq : d₁ = d₂ := by
    rw [ ← Nat.prod_factorization_pow_eq_self hd₁.ne_zero, ← Nat.prod_factorization_pow_eq_self hd₂.ne_zero ];
    congr 1 with p ; by_cases hp : Nat.Prime p <;> aesop;
  cases κ <;> aesop

/-
THEOREM 3. The hand-checkable instance from the paper: at least two powerful numbers strictly
between the consecutive squares `2909²` and `2910²`.
-/
theorem two_powerful_between_2909_2910 :
    ∃ m₁ m₂ : ℕ, m₁ ≠ m₂ ∧ KFull 2 m₁ ∧ KFull 2 m₂ ∧
      2909 ^ 2 < m₁ ∧ m₁ < 2910 ^ 2 ∧ 2909 ^ 2 < m₂ ∧ m₂ < 2910 ^ 2 := by
  -- 8467200 = 3 * 6^2 * 280^2 (with 3 ∣ 6) and 8468064 = 6 * 6^2 * 198^2 (with 6 ∣ 6).
  refine ⟨3 * 6 ^ 2 * 280 ^ 2, 6 * 6 ^ 2 * 198 ^ 2, ?_,
    kfull_construction 2 3 6 280 (by norm_num),
    kfull_construction 2 6 6 198 (by norm_num), ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num