import LatticeProb.Prob.BrownianCenteredExitEndpoint

/-! # Normalization of Brownian exit endpoints from balls -/

set_option autoImplicit false
noncomputable section

open MeasureTheory BouRabeeGwynne Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- Normalization about the center and by the radius sends a Brownian exit
endpoint law from a ball to the exit endpoint law from the unit ball. -/
theorem brownian_exit_endpoint_law_ball_normalize {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (c z : Euc d) {r : ℝ} (hr : 0 < r) :
    ((stoppedBrownianLaw (Metric.ball c r) z μ).map
        BouRabeeGwynne.CurveSpace.endPoint).map (fun x => r⁻¹ • (x - c)) =
      (stoppedBrownianLaw (Metric.ball (0 : Euc d) 1)
        (r⁻¹ • (z - c)) μ).map BouRabeeGwynne.CurveSpace.endPoint := by
  have hset : (fun x : Euc d => c + r • x) ⁻¹' Metric.ball c r =
      Metric.ball (0 : Euc d) 1 := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      sub_zero, norm_smul, Real.norm_of_nonneg hr.le]
    simpa only [mul_one] using (mul_lt_mul_iff_right₀ hr : r * ‖x‖ < r * 1 ↔ ‖x‖ < 1)
  simpa only [hset] using brownian_exit_endpoint_law_normalize hd hμ c z hr
    Metric.isOpen_ball (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball c r))

end LatticeProb
end
