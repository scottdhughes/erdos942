import Erdos942.Core
import Erdos942.Construction

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
