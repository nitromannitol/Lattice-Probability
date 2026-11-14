import LatticeProb.Topology.UnboundedRayLocalDistance
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Finiteness of the local interval distance -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LatticeProb.LocalCurveIntervalDistance

variable {E : Type*} [PseudoEMetricSpace E]

/-- The local interval distance is bounded by the exponential tail from radius one. -/
theorem localEDist_le_exp_neg_one (clock : (ℝ≥0 → E) → ℝ → ℝ≥0∞)
    (f g : ℝ≥0 → E) : localEDist clock f g ≤ ENNReal.ofReal (Real.exp (-1)) := by
  calc
    _ ≤ ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-r)) := by
      apply lintegral_mono
      intro r
      exact mul_le_of_le_one_right' (min_le_left _ _)
    _ = ENNReal.ofReal (Real.exp (-1)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 1)
        (ae_of_all _ fun r => (Real.exp_pos (-r)).le), integral_exp_neg_Ioi]

theorem localEDist_ne_top (clock : (ℝ≥0 → E) → ℝ → ℝ≥0∞)
    (f g : ℝ≥0 → E) : localEDist clock f g ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (localEDist_le_exp_neg_one clock f g) ENNReal.ofReal_lt_top)

end LatticeProb.LocalCurveIntervalDistance

namespace LatticeProb.UnboundedRayLocalDistance

open UnboundedRayIntervalIntegrand

variable {d : ℕ}

theorem localEDist_le_exp_neg_one (f g : UnboundedRay d) :
    localEDist f g ≤ ENNReal.ofReal (Real.exp (-1)) :=
  LocalCurveIntervalDistance.localEDist_le_exp_neg_one rayClock f.1 g.1

theorem localEDist_ne_top (f g : UnboundedRay d) : localEDist f g ≠ ∞ :=
  LocalCurveIntervalDistance.localEDist_ne_top rayClock f.1 g.1

end LatticeProb.UnboundedRayLocalDistance
