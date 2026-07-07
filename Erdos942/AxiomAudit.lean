import Erdos942.Core
import Erdos942.Construction
import Erdos942.Rate
import Erdos942.Frequency
import Erdos942.UpperBound
import Erdos942.GlobalCount

/-!
# Axiom audit

Building this file prints the axioms underlying each theorem.
Expected output: every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`. In particular, nothing below depends on `sorryAx` or on
`Lean.ofReduceBool`/`Lean.trustCompiler`.
-/

#print axioms kfull_construction               -- d ∣ D ⟹ d·D^κ·r^κ is κ-full
#print axioms construction_injective           -- d₁r₁^κ = d₂r₂^κ ⟹ d₁ = d₂, r₁ = r₂
#print axioms two_powerful_between_2909_2910   -- two powerful numbers in (2909², 2910²)

-- The construction (qualitative lower bound)
#print axioms box_principle_simultaneous       -- simultaneous Dirichlet box principle
#print axioms placement_kfull_window           -- window placement of the constructed numbers
#print axioms powerful_count_unbounded         -- h(n) is unbounded

-- The quantitative rate (paper Theorem 1.1, κ=2)
#print axioms nth_prime_upper                  -- p_h ≪ h log h, from Chebyshev.pi_ge
#print axioms box_principle_quantitative       -- box principle with denominator bound
#print axioms squarefree_many_divisors         -- 2^h − 1 squarefree divisors
#print axioms rate_inversion                   -- inversion of the size bound
#print axioms log_primorial_le                 -- log(primorial) ≪ h log h
#print axioms powerful_count_rate              -- κ=2 case (Erdős #942)
#print axioms powerful_count_rate_general      -- Theorem 1.1, all fixed κ≥2
#print axioms placement_kfull_window_general   -- general-κ window placement

-- The frequency-lower-bound CORE (Frequency.lean)
section FrequencyAudit
open Erdos942.Frequency
-- P1: elementary core — must be standard axioms only
#print axioms P1a_powerful                     -- m = d·(D r)² is 2-full
#print axioms window_iff_t_lt_one              -- EXACT abstract window iff (t < 1)
#print axioms mOf_sub_sq_factored              -- identity m − n² = 2 n t + t²
#print axioms window_upper_iff                 -- constructed m in upper window ⟺ t < 1
#print axioms P1c_distinct                     -- distinct squarefree kernels ⟹ distinct m
#print axioms P1d_count_ge                     -- the deduction h(n) ≥ |S|
#print axioms hOf_ge_of_directions             -- ℓ ≤ h(n) from ℓ directions
-- P2: algebraic Liouville core
#print axioms liouville_from_nonzero_int_norm  -- Liouville mechanism (no extra axioms)
#print axioms int_norm_ne_zero                 -- norm of nonzero elt is nonzero (Mathlib)
#print axioms multiquadratic_liouville_bound   -- |γ| ≥ M^{-(2^h−1)} (uses the ONE axiom)
-- P3 + headline conditional theorem
#print axioms frequency_lower_bound            -- Theorem A, conditional on the analytic axiom
end FrequencyAudit

-- The upper bound CORE (UpperBound.lean)
section UpperBoundAudit
open Erdos942.UpperBound
-- Elementary reduction — must be standard axioms only (NO sorryAx, NO ft_curve_count)
#print axioms powerful_rep                     -- m powerful ⟹ m = a²b³, b squarefree, a,b ≥ 1
#print axioms at_most_one_per_b                -- fixed b ≥ 2: ≤ one a in the window
#print axioms at_most_one_per_a                -- fixed a ≥ 1: ≤ one b in the window
#print axioms min_pow_le                       -- split: min a b ^ 5 ≤ (n+1)²
#print axioms hUp_le_aspects                   -- reduction h(n) ≤ #bAspect + #aAspect
-- Headline conditional theorem (standard 3 + the single analytic axiom ft_curve_count)
#print axioms upper_bound                      -- h(n) ≤ C·n^{6/25+ε}, on ft_curve_count
end UpperBoundAudit

-- The UNCONDITIONAL global count (GlobalCount.lean)
section GlobalCountAudit
open Erdos942.GlobalCount
-- Elementary reduction and analytic bounds — must be standard axioms only
#print axioms powerful_card_le_pair_card       -- #powerful ≤ #admissible pairs (a,b)
#print axioms pair_card_le_sum                 -- #pairs ≤ ∑_b Nat.sqrt (x/b³)
#print axioms term_le_telescope                -- 1/B^{3/2} ≤ 2/√(B-1) − 2/√B
#print axioms sum_recip_le                     -- ∑_{b=1}^N 1/(b√b) ≤ 3 − 2/√N
#print axioms sqrt_div_le                      -- Nat.sqrt(x/b³) ≤ √x · 1/(b√b)
-- Headline UNCONDITIONAL theorem (standard 3 axioms only)
#print axioms powerful_global_count            -- #{powerful m ≤ x} ≤ 3√x
end GlobalCountAudit
