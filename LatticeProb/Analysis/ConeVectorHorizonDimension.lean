import LatticeProb.Analysis.ConeVectorMembership
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Countable horizon decomposition for backward cone vectors

A backward cone vector has a positive gap between its cone time and its
first backward exit. A countable family of reciprocal horizons therefore
suffices for Hausdorff-dimension estimates, including on restricted sets.
-/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace LatticeProb

/-- A set of backward cone vectors is the union of its reciprocal-horizon
subsets, using the first backward exit. -/
theorem backwardConeVectors_inter_eq_iUnion_horizon
    (X Y : ℝ → ℝ) (S : Set (ℝ × ℝ)) :
    backwardConeVectors X Y ∩ S =
      ⋃ k : ℕ, {p ∈ backwardConeVectors X Y ∩ S |
        1 / (k + 1 : ℝ) < p.2 - coneFirstExitBackward X Y p.2} := by
  ext p
  constructor
  · intro hp
    have hpos : 0 < p.2 - coneFirstExitBackward X Y p.2 := by
      have h := hp.1.2.2.1
      linarith
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact mem_iUnion.mpr ⟨k, hp, hk⟩
  · intro hp
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact hk.1

/-- A common Hausdorff-dimension bound for reciprocal-horizon subsets bounds
all backward cone vectors in the given set. -/
theorem dimH_backwardConeVectors_inter_le_of_horizons
    (X Y : ℝ → ℝ) (S : Set (ℝ × ℝ)) (d : ℝ≥0∞)
    (h : ∀ k : ℕ, dimH {p ∈ backwardConeVectors X Y ∩ S |
      1 / (k + 1 : ℝ) < p.2 - coneFirstExitBackward X Y p.2} ≤ d) :
    dimH (backwardConeVectors X Y ∩ S) ≤ d := by
  rw [backwardConeVectors_inter_eq_iUnion_horizon, dimH_iUnion]
  exact iSup_le h

end LatticeProb
