/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianScaledLanding at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianScaling
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianUniformLanding

/-! The actual Gaussian landing lower bound at every positive parabolic scale. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- One positive landing probability works at all positive spatial scales,
for all starting points and centers at distance at most twice the scale. -/
theorem standardBrownianLaw_uniform_scaled_landing_probability {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ r : ℝ≥0, 0 < r → ∀ x c : Euc d,
      dist c x ≤ 2 * (r : ℝ) →
      ENNReal.ofReal p ≤
        μ {ω : BrownianPath d | x + ω (r ^ 2) ∈ ball c (κ * (r : ℝ))} := by
  obtain ⟨p, hp, hp1, hunit⟩ := standardBrownianLaw_uniform_landing_probability hμ hκ
  refine ⟨p, hp, hp1, ?_⟩
  intro r hr x c hc
  have hrR : 0 < (r : ℝ) := hr
  let a : Euc d := (r : ℝ)⁻¹ • (c - x)
  have hnorm : ‖a‖ ≤ 2 := by
    have hcnorm : ‖c - x‖ ≤ 2 * (r : ℝ) := by simpa only [dist_eq_norm] using hc
    calc
      ‖a‖ = ‖c - x‖ / (r : ℝ) := by
        simp only [a, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos hrR, div_eq_inv_mul]
      _ ≤ 2 := (div_le_iff₀ hrR).mpr hcnorm
  let E : Set (BrownianPath d) := {ω | ω 1 ∈ ball a κ}
  have hE : MeasurableSet E := isOpen_ball.measurableSet.preimage
    (by fun_prop : Continuous (fun ω : BrownianPath d => ω 1)).measurable
  have hdist (v : Euc d) : dist (x + v) c = dist v (c - x) := by
    simp only [dist_eq_norm]
    congr 1
    abel
  have hevent : scaledBrownianPath r ⁻¹' E =
      {ω : BrownianPath d | x + ω (r ^ 2) ∈ ball c (κ * (r : ℝ))} := by
    ext ω
    change scaledBrownianPath r ω 1 ∈ ball a κ ↔
      x + ω (r ^ 2) ∈ ball c (κ * (r : ℝ))
    simp only [scaledBrownianPath_apply, mul_one, mem_ball, a, dist_smul₀,
      norm_inv, Real.norm_eq_abs, abs_of_pos hrR]
    rw [hdist, ← div_eq_inv_mul, div_lt_iff₀ hrR]
  calc
    ENNReal.ofReal p ≤ μ E := hunit a hnorm
    _ = (μ.map (scaledBrownianPath r)) E := by
      rw [standardBrownianLaw_map_scale hμ hr]
    _ = μ {ω : BrownianPath d | x + ω (r ^ 2) ∈ ball c (κ * (r : ℝ))} := by
      rw [Measure.map_apply (measurable_scaledBrownianPath r) hE, hevent]

end BouRabeeGwynne
