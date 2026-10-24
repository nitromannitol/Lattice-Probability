import LatticeProb.Prob.BrownianDirichlet.ScaledExit
import Mathlib.Topology.Piecewise

/-!
# Zero extensions of continuous boundary data

Continuous data on the closure of an open Euclidean domain have measurable zero
extensions. Zero boundary values make these extensions continuous, and killed
path integrands depend only on the data inside the domain.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LatticeProb

variable {d : ℕ} {B : Set (Euc d)} {g v : Euc d → ℝ}

/-- Continuous data on the closure of an open domain extend measurably by zero. -/
theorem measurable_indicator_of_continuousOn (hB : IsOpen B)
    (hg : ContinuousOn g (closure B)) : Measurable (B.indicator g) := by
  classical
  exact (hg.mono subset_closure).measurable_piecewise continuousOn_const hB.measurableSet

/-- Zero frontier values allow continuous pasting with zero outside the domain. -/
theorem continuous_indicator_of_zero_frontier
    (hv : ContinuousOn v (closure B)) (hzero : ∀ y ∈ frontier B, v y = 0) :
    Continuous (B.indicator v) := by
  classical
  exact continuous_piecewise hzero hv continuousOn_const

/-- The zero extension from the closed domain is also continuous. -/
theorem continuous_closure_indicator_of_zero_frontier
    (hv : ContinuousOn v (closure B)) (hzero : ∀ y ∈ frontier B, v y = 0) :
    Continuous ((closure B).indicator v) := by
  classical
  apply continuous_piecewise
  · intro y hy
    exact hzero y (frontier_closure_subset hy)
  · simpa only [closure_closure] using hv
  · exact continuousOn_const

/-- Continuous real data on a bounded Euclidean domain's closure are bounded. -/
theorem isBounded_image_closure (hB : Bornology.IsBounded B)
    (hg : ContinuousOn g (closure B)) : ∃ M : ℝ, ∀ y ∈ closure B, |g y| ≤ M := by
  simpa only [Real.norm_eq_abs] using hB.isCompact_closure.exists_bound_of_continuousOn hg

/-- Before exit, killed path integrands use only values inside the exit domain. -/
theorem killed_integrand_congr {g g' : Euc d → ℝ} (hgg' : EqOn g g' B)
    (σ : ℝ) (x : Euc d) (t : ℝ≥0) (ω : BrownianPath d) :
    (if (t : ℝ≥0∞) < scaledExit B σ x ω then g (x + σ • ω t) else 0) =
      (if (t : ℝ≥0∞) < scaledExit B σ x ω then g' (x + σ • ω t) else 0) := by
  split_ifs with ht
  · exact hgg' (mem_of_lt_scaledExit ht)
  · rfl

/-- Expectations of killed integrands are independent of extensions outside the domain. -/
theorem integral_killed_integrand_congr {g g' : Euc d → ℝ} (hgg' : EqOn g g' B)
    (σ : ℝ) (x : Euc d) (t : ℝ≥0) (P : Measure (BrownianPath d)) :
    (∫ ω, if (t : ℝ≥0∞) < scaledExit B σ x ω then g (x + σ • ω t) else 0 ∂P) =
      ∫ ω, if (t : ℝ≥0∞) < scaledExit B σ x ω then g' (x + σ • ω t) else 0 ∂P := by
  exact integral_congr_ae (Filter.Eventually.of_forall (killed_integrand_congr hgg' σ x t))

end LatticeProb
