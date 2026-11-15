import LatticeProb.Analysis.WedgeArcParameterMeasure
import LatticeProb.Analysis.TranslatedIntervalSineUniqueness

/-! # Sine completeness on circular arcs -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- The sine coefficients determine a square-integrable function on a circular arc. -/
theorem ae_eq_zero_of_wedge_arc_sine_integrals_eq_zero {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi)
    {f : sphere (0 : ℂ) 1 → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℂ).toSphere.restrict
      {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)}))
    (hsine : ∀ n : ℕ, (∫ z : sphere (0 : ℂ) 1,
      (Real.sin (Real.pi * (n : ℝ) * (Complex.arg z - (-θ / 2)) / θ) : ℂ) * f z
      ∂((volume : Measure ℂ).toSphere.restrict
        {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})) = 0) :
    f =ᵐ[((volume : Measure ℂ).toSphere.restrict
      {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)})] 0 := by
  let μ := (volume : Measure ℂ).toSphere.restrict
    {z : sphere (0 : ℂ) 1 | Complex.arg z ∈ Ioo (-θ / 2) (θ / 2)}
  let ν := volume.restrict (Ioc (-θ / 2) (θ / 2))
  have hmap : Measure.map unitCircleParam ν = μ := map_unitCircleParam_restrict hθ'
  have hends : -θ / 2 + θ = θ / 2 := by ring
  have hν : volume.restrict (Ioo (-θ / 2) (θ / 2)) = ν :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  have hfp : MemLp (f ∘ unitCircleParam) 2
      (volume.restrict (Ioo (-θ / 2) (-θ / 2 + θ))) := by
    rw [hends, hν]
    exact memLp_comp_unitCircleParam hθ' hf
  have hc : ∀ n : ℕ, (∫ x in (-θ / 2)..(-θ / 2 + θ),
      (Real.sin (Real.pi * (n : ℝ) * (x - (-θ / 2)) / θ) : ℂ) *
        (f ∘ unitCircleParam) x) = 0 := by
    intro n
    let g : sphere (0 : ℂ) 1 → ℂ := fun z =>
      (Real.sin (Real.pi * (n : ℝ) * (Complex.arg z - (-θ / 2)) / θ) : ℂ) * f z
    have hm : Measurable (fun z : sphere (0 : ℂ) 1 =>
        (Real.sin (Real.pi * (n : ℝ) * (Complex.arg z - (-θ / 2)) / θ) : ℂ)) := by
      fun_prop (disch := exact Complex.measurable_arg)
    have hg : AEStronglyMeasurable g μ := hm.aestronglyMeasurable.mul hf.aestronglyMeasurable
    have hi := integral_comp_unitCircleParam hθ' hg
    have heq : (fun x : ℝ => g (unitCircleParam x)) =ᵐ[ν]
        (fun x => (Real.sin (Real.pi * (n : ℝ) * (x - (-θ / 2)) / θ) : ℂ) *
          (f ∘ unitCircleParam) x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      simp only [g, unitCircleParam, Function.comp_apply, arg_circleMap_mem_wedge hθ' hx]
    rw [hends, intervalIntegral.integral_of_le (by linarith : -θ / 2 ≤ θ / 2)]
    exact (integral_congr_ae heq).symm.trans (hi.symm.trans (hsine n))
  have hz := ae_eq_zero_of_translated_interval_sine_integrals_eq_zero hθ hfp hc
  rw [hends, hν] at hz
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hfgp := ae_of_ae_map measurable_unitCircleParam.aemeasurable (hmap ▸ hfg)
  have hgp : ∀ᵐ x ∂ν, g (unitCircleParam x) = 0 := by
    filter_upwards [hz, hfgp] with x hx hy
    simpa only [Function.comp_apply, Pi.zero_apply] using hy.symm.trans hx
  have hg0 : ∀ᵐ z ∂μ, g z = 0 := by
    rw [← hmap]
    exact (ae_map_iff measurable_unitCircleParam.aemeasurable
      (measurableSet_eq_fun hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
        measurable_const)).2 hgp
  filter_upwards [hfg, hg0] with z hz hz0
  simpa only [Pi.zero_apply] using hz.trans hz0

end LatticeProb
