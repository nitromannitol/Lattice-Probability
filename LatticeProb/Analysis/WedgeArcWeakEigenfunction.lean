import LatticeProb.Analysis.DirichletWeakEigenfunction
import LatticeProb.Analysis.WedgeArcSineBasis

/-! # Weak eigenfunction identity on a circular arc -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

open LQGMetric.HeatSq

/-- Integration of a continuous function of the argument against arc surface measure. -/
theorem integral_arg_wedgeArcSurfaceMeasure {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ z, f (Complex.arg z) ∂wedgeArcSurfaceMeasure θ) =
      ∫ x in (-θ / 2)..(θ / 2), f x := by
  have hm : Measurable (fun z : sphere (0 : ℂ) 1 => f (Complex.arg z)) :=
    hf.measurable.comp (Complex.measurable_arg.comp measurable_subtype_coe)
  rw [wedgeArcSurfaceMeasure, ← map_unitCircleParam_restrict hθ',
    integral_map measurable_unitCircleParam.aemeasurable hm.aestronglyMeasurable]
  rw [intervalIntegral.integral_of_le (by linarith : -θ / 2 ≤ θ / 2)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simp only [unitCircleParam, arg_circleMap_mem_wedge hθ' hx]

/-- The normalized angular sine mode satisfies the weak Dirichlet equation
against continuously differentiable angular tests vanishing at the endpoints. -/
theorem wedgeArc_sine_weak_eigenfunction {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (n : ℕ) {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (-θ / 2) (θ / 2), HasDerivAt g (g' x) x)
    (hgc : Continuous g) (hg'c : Continuous g')
    (ha : g (-θ / 2) = 0) (hb : g (θ / 2) = 0) :
    (∫ z, g' (Complex.arg z) *
      deriv (fun x => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x)
        (Complex.arg z) ∂wedgeArcSurfaceMeasure θ) =
      (Real.pi * (n + 1 : ℕ) / θ) ^ 2 *
      ∫ z, g (Complex.arg z) *
        (Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) (Complex.arg z))
        ∂wedgeArcSurfaceMeasure θ := by
  have hd : Continuous (deriv (fun x => Real.sqrt (2 / θ) *
      sinMode (-θ / 2) θ (n + 1) x)) := by
    have he : deriv (fun x => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x) =
        fun x => Real.sqrt (2 / θ) * (Real.pi * (n + 1 : ℕ) / θ *
          Real.cos (Real.pi * (n + 1 : ℕ) / θ * (x - (-θ / 2)))) := by
      funext x
      exact (hasDerivAt_const_mul_sinMode _ _ _ _ x).deriv
    rw [he]
    fun_prop
  have hf : Continuous (fun x => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_const_mul_sinMode _ _ _ _ x).continuousAt
  rw [integral_arg_wedgeArcSurfaceMeasure (f := fun x => g' x *
        deriv (fun y => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) y) x)
        hθ hθ' (hg'c.mul hd),
      integral_arg_wedgeArcSurfaceMeasure (f := fun x => g x *
        (Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x)) hθ hθ' (hgc.mul hf)]
  have he : -θ / 2 + θ = θ / 2 := by ring
  have hh := sinMode_weak_eigenfunction (a := -θ / 2) (c := Real.sqrt (2 / θ))
    hθ (n + 1) (by simpa only [he] using hg)
    (by simpa only [he] using hg'c.continuousOn) ha (by simpa only [he] using hb)
  simpa only [he] using hh

end LatticeProb
