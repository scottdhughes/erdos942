import Erdos942.Core

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The lower-bound construction (qualitative form)

This module formalizes the construction underlying the lower bound for Erdős #942:
the simultaneous Dirichlet box principle, the window placement of the constructed
numbers, and the pigeonhole assembly, yielding that `h(n)` is unbounded
(`powerful_count_unbounded`). The explicit rate is not formalized here; see the note.
-/

/-
`√d` is irrational for `d ≥ 2` squarefree.
-/
theorem sqrt_irrational_of_squarefree (d : ℕ) (hd2 : 2 ≤ d) (hd : Squarefree d) :
    Irrational (Real.sqrt d) := by
  convert irrational_sqrt_natCast_iff.mpr _;
  rintro ⟨ k, rfl ⟩ ; simp_all +decide [ sq, Nat.squarefree_mul_iff ]

/-! ## Lemma A : simultaneous box principle -/

/-
**Lemma A (simultaneous box principle).**  Given reals `α i` and positive tolerances `δ i`
indexed by a finite type, there is a natural `q ≥ 1` with `‖q • α i‖ ≤ δ i` for every `i`,
where `‖x‖` is the distance from `x` to the nearest integer, `|x - round x|`.
-/
theorem box_principle_simultaneous {ι : Type*} [Fintype ι] (α : ι → ℝ) (δ : ι → ℝ)
    (hδ : ∀ i, 0 < δ i) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ i, |(q : ℝ) * α i - ((round ((q : ℝ) * α i) : ℤ) : ℝ)| ≤ δ i := by
  -- Set T := ∏ i, ⌈(δ i)⁻¹⌉₊. Note that T > 0 (since δ i > 0). By the pigeonhole principle, there exist distinct t₁, t₂ ∈ {0, ..., T} such that ⌊Int.fract (t₁ * α i) / δ i⌋₊ = ⌊Int.fract (t₂ * α i) / δ i⌋₊ for all i.
  set T := ∏ i, ⌈(δ i)⁻¹⌉₊ with hT
  have hT_pos : 0 < T := by
    exact Finset.prod_pos fun i _ => Nat.ceil_pos.mpr ( inv_pos.mpr ( hδ i ) )
  obtain ⟨t₁, t₂, ht₁t₂, ht⟩ : ∃ t₁ t₂ : ℕ, t₁ < t₂ ∧ t₂ ≤ T ∧ ∀ i, ⌊Int.fract (t₁ * α i) / δ i⌋₊ = ⌊Int.fract (t₂ * α i) / δ i⌋₊ := by
    have h_pigeonhole : Finset.card (Finset.image (fun t : ℕ => fun i : ι => ⌊Int.fract (t * α i) / δ i⌋₊) (Finset.range (T + 1))) ≤ T := by
      refine' le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
      exact Finset.Iic ( fun i => ⌈ ( δ i ) ⁻¹⌉₊ - 1 );
      · simp +zetaDelta at *;
        intro x hx i; refine' Nat.le_sub_one_of_lt _; refine' Nat.floor_lt' _ |>.2 _;
        · exact ne_of_gt ( Nat.ceil_pos.mpr ( inv_pos.mpr ( hT_pos i ) ) );
        · rw [ div_lt_iff₀ ( hT_pos i ) ] ; nlinarith [ Nat.le_ceil ( ( δ i ) ⁻¹ ), hT_pos i, mul_inv_cancel₀ ( ne_of_gt ( hT_pos i ) ), Int.fract_lt_one ( ( x : ℝ ) * α i ) ];
      · erw [ Finset.card_map, Finset.card_pi ] ; aesop;
    contrapose! h_pigeonhole;
    rw [ Finset.card_image_of_injOn fun t₁ ht₁ t₂ ht₂ h => le_antisymm ( le_of_not_gt fun h' => by obtain ⟨ i, hi ⟩ := h_pigeonhole _ _ h' ( by linarith [ Finset.mem_range.mp ht₁, Finset.mem_range.mp ht₂ ] ) ; have := congr_fun h i; aesop ) ( le_of_not_gt fun h' => by obtain ⟨ i, hi ⟩ := h_pigeonhole _ _ h' ( by linarith [ Finset.mem_range.mp ht₁, Finset.mem_range.mp ht₂ ] ) ; have := congr_fun h i; aesop ) ] ; simp +arith +decide;
  refine' ⟨ t₂ - t₁, _, _ ⟩;
  · exact Nat.sub_pos_of_lt ht₁t₂;
  · intro i
    have h_frac : |Int.fract (t₁ * α i) - Int.fract (t₂ * α i)| ≤ δ i := by
      have := ht.2 i; rw [ Nat.floor_eq_iff ] at this;
      · rw [ abs_le ] ; constructor <;> nlinarith [ Nat.floor_le ( show 0 ≤ Int.fract ( ( t₂ : ℝ ) * α i ) / δ i by exact div_nonneg ( Int.fract_nonneg _ ) ( le_of_lt ( hδ i ) ) ), Nat.lt_floor_add_one ( Int.fract ( ( t₂ : ℝ ) * α i ) / δ i ), hδ i, mul_div_cancel₀ ( Int.fract ( ( t₁ : ℝ ) * α i ) ) ( ne_of_gt ( hδ i ) ), mul_div_cancel₀ ( Int.fract ( ( t₂ : ℝ ) * α i ) ) ( ne_of_gt ( hδ i ) ) ] ;
      · exact div_nonneg ( Int.fract_nonneg _ ) ( le_of_lt ( hδ i ) );
    convert round_le _ ( ⌊ ( t₂ : ℝ ) * α i⌋ - ⌊ ( t₁ : ℝ ) * α i⌋ ) |> le_trans <| _ using 1;
    · infer_instance;
    · convert h_frac using 1 ; rw [ Nat.cast_sub ht₁t₂.le ] ; rw [ Int.fract, Int.fract ] ; ring;
      rw [ ← abs_neg ] ; push_cast ; ring;

/-! ## Lemma B : window placement -/

/-- The rounded value `r = round(q/√d)` as a natural number. -/
noncomputable def rOf (d q : ℕ) : ℕ := (round ((q : ℝ) * (1 / Real.sqrt d))).toNat

/-- The constructed powerful number `m = d · D² · r²`. -/
noncomputable def mOf (D d q : ℕ) : ℕ := d * D ^ 2 * (rOf d q) ^ 2

/-- The signed error `ε = q/√d − round(q/√d)`. -/
noncomputable def epsOf (d q : ℕ) : ℝ :=
  (q : ℝ) * (1 / Real.sqrt d) - ((round ((q : ℝ) * (1 / Real.sqrt d)) : ℤ) : ℝ)

/-
Under the tight tolerance, the rounded value is `≥ 1`.
-/
theorem rOf_ge_one (D d q : ℕ) (hD : 1 ≤ D) (hd2 : 2 ≤ d) (hq : 1 ≤ q)
    (htol : |epsOf d q| ≤ 1 / (16 * (D : ℝ) * Real.sqrt d)) :
    1 ≤ round ((q : ℝ) * (1 / Real.sqrt d)) := by
  have h_round_pos : (q : ℝ) * (1 / Real.sqrt d) - round ((q : ℝ) * (1 / Real.sqrt d)) ≤ 1 / (16 * D * Real.sqrt d) := by
    exact le_of_abs_le htol;
  -- Since $q \geq 1$, we have $q / \sqrt{d} \geq 1 / \sqrt{d}$.
  have h_q_div_sqrt_d_ge_one_div_sqrt_d : (q : ℝ) * (1 / Real.sqrt d) ≥ 1 / Real.sqrt d := by
    exact le_mul_of_one_le_left ( by positivity ) ( by norm_cast );
  contrapose! h_round_pos;
  refine' lt_of_lt_of_le _ ( sub_le_sub_right h_q_div_sqrt_d_ge_one_div_sqrt_d _ );
  rw [ div_sub', div_lt_div_iff₀ ] <;> norm_num <;> try positivity;
  rw [ round_eq ] at *;
  norm_num [ show ⌊ ( q : ℝ ) * ( Real.sqrt d ) ⁻¹ + 1 / 2⌋ = 0 by exact le_antisymm ( Int.le_of_lt_add_one <| by simpa using h_round_pos ) ( Int.floor_nonneg.mpr <| by positivity ) ] ; nlinarith [ show ( D : ℝ ) ≥ 1 by norm_cast, show ( d : ℝ ) ≥ 2 by norm_cast, Real.sqrt_nonneg d, Real.sq_sqrt <| Nat.cast_nonneg d, mul_pos ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| zero_lt_two.trans_le hd2 ) <| show ( 0 :ℝ ) < D by positivity ]

/-
The key real identity, `m − n² = D²·(−2 q √d ε + d ε²)`.
-/
theorem mOf_sub_sq_eq (D d q : ℕ) (hD : 1 ≤ D) (hd2 : 2 ≤ d) (hq : 1 ≤ q)
    (htol : |epsOf d q| ≤ 1 / (16 * (D : ℝ) * Real.sqrt d)) :
    ((mOf D d q : ℕ) : ℝ) - ((D * q : ℕ) : ℝ) ^ 2
      = (D : ℝ) ^ 2 * (-2 * (q : ℝ) * Real.sqrt d * epsOf d q
          + (d : ℝ) * (epsOf d q) ^ 2) := by
  convert ( congr_arg ( fun x : ℝ => ( d : ℝ ) * D ^ 2 * ( x ) ^ 2 - ( D * q ) ^ 2 ) ( show ( round ( ( q : ℝ ) * ( 1 / Real.sqrt d ) ) : ℝ ) = ( q : ℝ ) * ( 1 / Real.sqrt d ) - epsOf d q from ?_ ) ) using 1 ; ring_nf;
  · norm_num [ mOf, rOf ];
    rw [ show ( round ( ( q : ℝ ) * ( Real.sqrt d ) ⁻¹ ) |> Int.toNat : ℝ ) = round ( ( q : ℝ ) * ( Real.sqrt d ) ⁻¹ ) from mod_cast Int.toNat_of_nonneg <| ?_ ] ; ring;
    convert rOf_ge_one D d q hD hd2 hq htol |> le_trans zero_le_one using 1;
    norm_num;
  · field_simp [epsOf]
    ring;
    grind;
  · unfold epsOf; ring;

/-
**Lemma B (window placement).**  With `D ≥ 1`, `d ≥ 2` squarefree dividing `D`, `q ≥ 1`,
and the tight tolerance on `ε = q/√d − round`, the number `m = mOf D d q` is `2`-full, has
`r ≥ 1`, and lands strictly inside one of the two windows adjacent to `n² = (Dq)²`.
-/
theorem placement_kfull_window (D d q : ℕ) (hD : 1 ≤ D) (hd2 : 2 ≤ d)
    (hd : Squarefree d) (hdvd : d ∣ D) (hq : 1 ≤ q)
    (htol : |epsOf d q| ≤ 1 / (16 * (D : ℝ) * Real.sqrt d)) :
    1 ≤ rOf d q ∧ KFull 2 (mOf D d q) ∧
      (mOf D d q ∈ Finset.Ioo ((D * q - 1) ^ 2) ((D * q) ^ 2) ∨
       mOf D d q ∈ Finset.Ioo ((D * q) ^ 2) ((D * q + 1) ^ 2)) := by
  constructor;
  · convert rOf_ge_one D d q hD hd2 hq htol using 1;
    grind +locals;
  · constructor;
    · convert kfull_construction 2 d D ( rOf d q ) hdvd using 1;
    · -- By the dichotomy on naturals, either $mOf D d q < (D * q)^2$ or $(D * q)^2 < mOf D d q$.
      have h_dichotomy : mOf D d q < (D * q) ^ 2 ∨ (D * q) ^ 2 < mOf D d q := by
        refine' lt_or_gt_of_ne _;
        intro h_eq
        have h_sqrt : Real.sqrt d = (q : ℝ) / (rOf d q) := by
          have h_sqrt : (d : ℝ) * (rOf d q) ^ 2 = q ^ 2 := by
            norm_cast;
            exact mul_left_cancel₀ ( pow_ne_zero 2 ( by positivity : D ≠ 0 ) ) ( by linarith! [ show mOf D d q = d * D ^ 2 * ( rOf d q ) ^ 2 from rfl ] );
          rw [ eq_div_iff ];
          · rw [ ← sq_eq_sq₀ ] <;> first | positivity | nlinarith [ Real.mul_self_sqrt ( Nat.cast_nonneg d ) ] ;
          · intro h; simp_all +decide ;
            exact absurd h_sqrt ( by positivity );
        exact absurd h_sqrt ( by exact fun h => by have := sqrt_irrational_of_squarefree d hd2 hd; exact this ⟨ q / rOf d q, by aesop ⟩ );
      have h_error_bound : |((mOf D d q : ℕ) : ℝ) - ((D * q : ℕ) : ℝ) ^ 2| ≤ (D * q : ℝ) / 8 + 1 / 256 := by
        have h_error_bound : |((mOf D d q : ℕ) : ℝ) - ((D * q : ℕ) : ℝ) ^ 2| ≤ (D : ℝ) ^ 2 * (2 * (q : ℝ) * Real.sqrt d * (1 / (16 * (D : ℝ) * Real.sqrt d)) + (d : ℝ) * (1 / (16 * (D : ℝ) * Real.sqrt d)) ^ 2) := by
          have h_error_bound : |((mOf D d q : ℕ) : ℝ) - ((D * q : ℕ) : ℝ) ^ 2| ≤ (D : ℝ) ^ 2 * (2 * (q : ℝ) * Real.sqrt d * |epsOf d q| + (d : ℝ) * (epsOf d q) ^ 2) := by
            rw [ mOf_sub_sq_eq D d q hD hd2 hq htol ];
            norm_num [ abs_mul, abs_of_nonneg, Real.sqrt_nonneg ];
            exact mul_le_mul_of_nonneg_left ( abs_le.mpr ⟨ by cases abs_cases ( epsOf d q ) <;> nlinarith [ show ( 0 : ℝ ) ≤ 2 * q * Real.sqrt d by positivity, show ( 0 : ℝ ) ≤ d * epsOf d q ^ 2 by positivity ], by cases abs_cases ( epsOf d q ) <;> nlinarith [ show ( 0 : ℝ ) ≤ 2 * q * Real.sqrt d by positivity, show ( 0 : ℝ ) ≤ d * epsOf d q ^ 2 by positivity ] ⟩ ) ( sq_nonneg _ );
          exact h_error_bound.trans ( mul_le_mul_of_nonneg_left ( add_le_add ( mul_le_mul_of_nonneg_left htol <| by positivity ) <| mul_le_mul_of_nonneg_left ( by simpa using pow_le_pow_left₀ ( by positivity ) htol 2 ) <| by positivity ) <| by positivity );
        convert h_error_bound using 1 ; ring_nf ; norm_num [ show D ≠ 0 by linarith, show d ≠ 0 by linarith ];
        -- Simplify the right-hand side of the inequality.
        field_simp
        ring;
      cases h_dichotomy <;> simp_all +decide [ abs_le ];
      · left;
        rw [ ← @Nat.cast_lt ℝ ] ; norm_num;
        rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith [ show ( D * q : ℝ ) ≥ 1 by norm_cast; nlinarith ];
      · exact Or.inr ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( D * q : ℝ ) ≥ 1 by norm_cast; nlinarith ] )

/-! ## Lemma C : assembly -/

/-
Injectivity-based card bound: a set `T` of squarefree numbers with `rOf ≥ 1`, all of whose
constructed values land in `W` and are `2`-full, injects into `W.filter (KFull 2)`.
-/
theorem window_card_bound (D q : ℕ) (hD : 1 ≤ D) (T : Finset ℕ)
    (hsq : ∀ p ∈ T, Squarefree p) (hr : ∀ p ∈ T, 1 ≤ rOf p q)
    (W : Finset ℕ) (hmem : ∀ p ∈ T, mOf D p q ∈ W ∧ KFull 2 (mOf D p q)) :
    T.card ≤ (W.filter (fun m => KFull 2 m)).card := by
  -- Apply Finset.card_le_card_of_injOn with the function f := fun p => mOf D p q, target W.filter (KFull 2).
  have h_inj : Finset.card (Finset.image (fun p => mOf D p q) T) = T.card := by
    refine' Finset.card_image_of_injOn fun p hp p' hp' h => _;
    convert construction_injective 2 p p' ( rOf p q ) ( rOf p' q ) ( by decide ) ( hsq p hp ) ( hsq p' hp' ) ( hr p hp ) ( hr p' hp' ) _;
    · aesop;
    · exact mul_left_cancel₀ ( pow_ne_zero 2 ( by positivity : D ≠ 0 ) ) ( by simpa [ mul_assoc, mul_comm, mul_left_comm, mOf ] using h );
  exact h_inj ▸ Finset.card_le_card ( Finset.image_subset_iff.mpr fun p hp => Finset.mem_filter.mpr ( hmem p hp ) )

/-
There is a finset of exactly `k` primes.
-/
theorem exists_prime_finset (k : ℕ) :
    ∃ S : Finset ℕ, S.card = k ∧ ∀ p ∈ S, p.Prime := by
  exact Exists.imp ( by aesop ) ( Nat.infinite_setOf_prime.exists_subset_card_eq k )

/-
**Main theorem (Erdős #942, qualitative form).**  For every `ℓ` there is an `n` with at
least `ℓ` powerful (`2`-full) numbers strictly between `n²` and `(n+1)²`.
-/
theorem powerful_count_unbounded :
    ∀ ℓ : ℕ, ∃ n : ℕ,
      ℓ ≤ ((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun m => KFull 2 m)).card := by
  intro ℓ;
  obtain ⟨ S, hS₁, hS₂ ⟩ := exists_prime_finset ( 2 * ℓ );
  -- Apply the simultaneous box principle to find $q$.
  obtain ⟨ q, hq₁, hq₂ ⟩ : ∃ q : ℕ, 1 ≤ q ∧ ∀ p ∈ S, |(q : ℝ) * (1 / Real.sqrt p) - ((round ((q : ℝ) * (1 / Real.sqrt p) : ℝ)) : ℝ)| ≤ 1 / (16 * (∏ p ∈ S, p : ℝ) * Real.sqrt p) := by
    have := box_principle_simultaneous ( fun p : S => 1 / Real.sqrt p ) ( fun p : S => 1 / ( 16 * ( ∏ p ∈ S, p : ℝ ) * Real.sqrt p ) ) ?_;
    · aesop;
    · exact fun i => one_div_pos.mpr ( mul_pos ( mul_pos ( by norm_num ) ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr ( Nat.Prime.pos ( hS₂ p hp ) ) ) ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hS₂ _ i.2 ) ) ) ) );
  set D := ∏ p ∈ S, p
  set n := D * q
  have hD : 1 ≤ D := by
    exact Finset.prod_pos fun p hp => Nat.Prime.pos ( hS₂ p hp )
  have hn : 1 ≤ n := by
    exact Nat.mul_pos hD hq₁
  have h_placement : ∀ p ∈ S, 1 ≤ rOf p q ∧ KFull 2 (mOf D p q) ∧ (mOf D p q ∈ Finset.Ioo ((n - 1) ^ 2) (n ^ 2) ∨ mOf D p q ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2)) := by
    intros p hp
    apply placement_kfull_window D p q hD (Nat.Prime.two_le (hS₂ p hp)) (Nat.prime_iff.mp (hS₂ p hp)).squarefree (Finset.dvd_prod_of_mem _ hp) hq₁ (by
    convert hq₂ p hp using 1 ; norm_num [ epsOf ];
    exact Or.inl <| by rw [ Nat.cast_prod ] ;);
  -- Define Shi and Slo.
  set Shi := S.filter (fun p => mOf D p q ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2))
  set Slo := S.filter (fun p => mOf D p q ∈ Finset.Ioo ((n - 1) ^ 2) (n ^ 2));
  -- By the pigeonhole principle, either Shi or Slo has cardinality at least ℓ.
  have h_pigeonhole : Shi.card ≥ ℓ ∨ Slo.card ≥ ℓ := by
    have h_pigeonhole : Shi.card + Slo.card ≥ S.card := by
      rw [ ← Finset.card_union_add_card_inter ];
      exact le_add_right ( Finset.card_le_card fun x hx => by specialize h_placement x hx; aesop );
    grind;
  cases' h_pigeonhole with h h;
  · use n;
    refine le_trans h ?_;
    convert window_card_bound D q hD Shi _ _ _ _ using 1;
    · exact fun p hp => Nat.prime_iff.mp ( hS₂ p ( Finset.mem_filter.mp hp |>.1 ) ) |> fun h => h.squarefree;
    · exact fun p hp => h_placement p ( Finset.filter_subset _ _ hp ) |>.1;
    · exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2, h_placement p ( Finset.mem_filter.mp hp |>.1 ) |>.2.1 ⟩;
  · use n - 1;
    refine le_trans h ?_;
    convert window_card_bound D q hD Slo _ _ _ _ using 1;
    · exact fun p hp => Nat.prime_iff.mp ( hS₂ p ( Finset.mem_filter.mp hp |>.1 ) ) |> fun h => h.squarefree;
    · exact fun p hp => h_placement p ( Finset.mem_filter.mp hp |>.1 ) |>.1;
    · grind

#print axioms powerful_count_unbounded