import LatticeProb.Prob.Percolation.LatticeBondFiniteFlip
import LatticeProb.External.SupercriticalBondUniquenessInput

/-!
# Unique infinite components after every finite flip

The explicit classical supercritical uniqueness input gives probability one for the
actual measurable uniqueness event. Finite-energy transport yields a conull stable
subset, and hence an actual configuration with uniqueness after every finite bond flip.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory LatticeProb.External

/-- Conditional only on the classical input, simultaneous finite-flip uniqueness
has mass one for the actual supercritical canonical lattice law. -/
theorem latticeBondLaw_all_finite_flips_unique
    (hclassical : SupercriticalBondUniqueness)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    latticeBondLaw d p
      {ω | ∀ F : Finset (Bond d), HasUniqueInfiniteOpenComponent (finiteBondFlip F ω)} =
        1 := by
  exact latticeBondLaw_allFiniteBondFlipsEvent p
    (lt_of_le_of_lt (criticalProbability_nonneg d) hpc) hp1
    (measurableSet_uniqueInfiniteComponentEvent d) (hclassical.2 d hd p hpc hp1)

/-- There is an actual configuration with a unique infinite open component after
all finite flips; the only literature hypothesis is the explicit classical input. -/
theorem exists_all_finite_flips_unique
    (hclassical : SupercriticalBondUniqueness)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ ω : Configuration d, ∀ F : Finset (Bond d),
      HasUniqueInfiniteOpenComponent (finiteBondFlip F ω) := by
  have hfull := latticeBondLaw_all_finite_flips_unique hclassical d hd p hpc hp1
  have hae : ∀ᵐ ω ∂latticeBondLaw d p, ∀ F : Finset (Bond d),
      HasUniqueInfiniteOpenComponent (finiteBondFlip F ω) :=
    (mem_ae_iff_prob_eq_one
      (measurableSet_allFiniteBondFlipsEvent
        (measurableSet_uniqueInfiniteComponentEvent d))).mpr hfull
  exact hae.exists

end LatticeProb.Percolation
