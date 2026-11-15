import LatticeProb.Analysis.IntervalWedgeArcSineIsometry
import LatticeProb.Analysis.WedgeArcSineEigenmodes

/-! # Angular pullback of the interval and arc isometry -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- The angular parametrization sends interval Lebesgue measure to arc surface measure. -/
theorem measurePreserving_unitCircleParam {θ : ℝ} (hθ : θ ≤ 2 * Real.pi) :
    MeasurePreserving unitCircleParam
      (volume.restrict (Ioo (-θ / 2) (θ / 2))) (wedgeArcSurfaceMeasure θ) := by
  refine ⟨measurable_unitCircleParam, ?_⟩
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact map_unitCircleParam_restrict hθ

/-- Angular pullback of a normalized arc mode is the corresponding interval mode. -/
theorem comp_unitCircleParam_wedgeArcSineLp {θ : ℝ} (hθ : θ ≤ 2 * Real.pi)
    (n : ℕ) :
    Lp.compMeasurePreserving unitCircleParam (measurePreserving_unitCircleParam hθ)
      (wedgeArcSineLp θ n) = intervalNormalizedSineLp (-θ / 2) (θ / 2) n := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (wedgeArcSineLp θ n)
      (measurePreserving_unitCircleParam hθ),
    (measurePreserving_unitCircleParam hθ).quasiMeasurePreserving.ae_eq_comp
      (wedgeArcSineMode_memLp θ n).coeFn_toLp,
    Lp.coeFn_smul (Real.sqrt (2 / (θ / 2 - -θ / 2)) : ℂ)
      ((intervalSineMode_memLp (-θ / 2) (θ / 2) n).toLp
        (intervalSineMode (-θ / 2) (θ / 2 - -θ / 2) n)),
    (intervalSineMode_memLp (-θ / 2) (θ / 2) n).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioo] with x h1 h2 h3 h4 hx
  rw [h1]
  simp only [Function.comp_apply]
  change wedgeArcSineLp θ n (unitCircleParam x) = _ at h2
  rw [h2]
  change _ = ((Real.sqrt (2 / (θ / 2 - -θ / 2)) : ℂ) •
    (intervalSineMode_memLp (-θ / 2) (θ / 2) n).toLp
      (intervalSineMode (-θ / 2) (θ / 2 - -θ / 2) n)) x
  rw [h3]
  simp only [Function.comp_apply, Pi.smul_apply]
  rw [h4, wedgeArcSineMode_unitCircleParam hθ ⟨hx.1, hx.2.le⟩]
  have he : θ / 2 - -θ / 2 = θ := by ring
  simp only [he, intervalSineMode, smul_eq_mul, Complex.ofReal_mul]

/-- The inverse sine isometry is angular pullback. -/
theorem intervalWedgeArcSineIsometry_symm_eq_comp {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi)
    (f : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) :
    (intervalWedgeArcSineIsometry hθ hθ').symm f =
      Lp.compMeasurePreserving unitCircleParam (measurePreserving_unitCircleParam hθ') f := by
  let b := wedgeArcSineHilbertBasis hθ hθ'
  let F := (intervalWedgeArcSineIsometry hθ hθ').symm.toContinuousLinearEquiv.toContinuousLinearMap
  let G := (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ unitCircleParam
    (measurePreserving_unitCircleParam hθ')).toContinuousLinearMap
  have hm : ∀ n, F (b n) = G (b n) := by
    intro n
    change (intervalWedgeArcSineIsometry hθ hθ').symm (b n) =
      Lp.compMeasurePreserving unitCircleParam (measurePreserving_unitCircleParam hθ') (b n)
    rw [show b n = wedgeArcSineLp θ n from wedgeArcSineHilbertBasis_apply hθ hθ' n]
    exact (intervalWedgeArcSineIsometry_symm_apply_mode hθ hθ' n).trans
      (comp_unitCircleParam_wedgeArcSineLp hθ' n).symm
  have hf := (b.hasSum_repr f).mapL F
  have hg := (b.hasSum_repr f).mapL G
  have he : (fun n => F (b.repr f n • b n)) =
      (fun n => G (b.repr f n • b n)) := by
    funext n
    rw [map_smul, map_smul, hm n]
  rw [he] at hf
  exact hf.unique hg

/-- Representatives of the inverse isometry agree almost everywhere with composition. -/
theorem intervalWedgeArcSineIsometry_symm_ae {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi)
    (f : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) :
    (intervalWedgeArcSineIsometry hθ hθ').symm f =ᵐ[
      volume.restrict (Ioo (-θ / 2) (θ / 2))] f ∘ unitCircleParam := by
  rw [intervalWedgeArcSineIsometry_symm_eq_comp hθ hθ' f]
  exact Lp.coeFn_compMeasurePreserving f (measurePreserving_unitCircleParam hθ')

end LatticeProb
