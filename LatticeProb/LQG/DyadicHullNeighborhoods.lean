import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_1B
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom

/-! # Neighborhoods of compact sets and dyadic hulls -/

set_option autoImplicit false

open Set Metric
open LQGMetric.Blueprint LQGMetric.LocalEvent LQGMetric.CONF

namespace LatticeProb.LQG

/-- A sufficiently fine dyadic hull lies in any prescribed positive thickening. -/
theorem exists_dyadicHull_subset_thickening (A : Set ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, dyadicHull n A ⊆ thickening ε A := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hn' : (2 : ℝ) / 2 ^ n < ε := by
    rw [one_div_pow] at hn
    have heq : (2 : ℝ) / 2 ^ n = 2 * (1 / 2 ^ n) := by ring
    rw [heq]
    linarith
  refine ⟨n, ?_⟩
  intro x hx
  simp only [dyadicHull, mem_iUnion] at hx
  obtain ⟨k, ⟨y, hyk, hyA⟩, hxk⟩ := hx
  exact mem_thickening_iff.2 ⟨y, hyA, lt_of_le_of_lt (conf21_sq_dist hxk hyk) hn'⟩

/-- Every dyadic hull interior contains a positive thickening of a compact set. -/
theorem exists_thickening_subset_interior_dyadicHull {A : Set ℂ}
    (hA : IsCompact A) (n : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ thickening ε A ⊆ interior (dyadicHull n A) :=
  hA.exists_thickening_subset_open isOpen_interior (subset_interior_dyadicHull n A)

end LatticeProb.LQG
