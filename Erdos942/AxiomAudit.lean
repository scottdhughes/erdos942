import Erdos942.Core
import Erdos942.Construction
import Erdos942.Rate

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
