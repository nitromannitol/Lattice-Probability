import LatticeProb.Analysis.IntervalSineCompleteness

/-! # Completeness of the sine functions on an interval -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- An L² function with vanishing sine coefficients vanishes almost everywhere. -/
theorem ae_eq_zero_of_interval_sine_integrals_eq_zero {θ : ℝ} [Fact (0 < 2 * θ)]
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioo 0 θ)))
    (hsine : ∀ n : ℕ, (∫ x in (0 : ℝ)..θ,
      (Real.sin (Real.pi * (n : ℝ) * x / θ) : ℂ) * f x) = 0) :
    f =ᵐ[volume.restrict (Ioo 0 θ)] 0 := by
  have hθ : 0 < θ := by linarith [Fact.out (p := 0 < 2 * θ)]
  let F := AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f)
  have hcoeff : ∀ n : ℕ, fourierCoeff F (n : ℤ) = fourierCoeff F (-(n : ℤ)) := by
    intro n
    have h := fourierCoeff_sub_neg_oddLift_eq_sine hf (n : ℤ)
    simp only [Int.cast_natCast, hsine n, mul_zero, sub_eq_zero] at h
    exact h
  have hhaar : F =ᵐ[AddCircle.haarAddCircle] 0 :=
    ae_eq_zero_of_ae_odd_of_fourierCoeff_eq_neg F
      (memLp_haar_lift_oddIntervalExtension hθ hf)
      (ae_lift_oddIntervalExtension_neg f) hcoeff
  have hvol : F =ᵐ[(volume : Measure (AddCircle (2 * θ)))] 0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,
      Measure.ae_ennreal_smul_measure_eq (by positivity)]
    exact hhaar
  have hpull : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioc (-θ) (-θ + 2 * θ))),
      F (x : AddCircle (2 * θ)) = 0 := by
    have hp := AddCircle.measurePreserving_mk (2 * θ) (-θ)
    rw [← hp.map_eq] at hvol
    exact ae_of_ae_map hp.measurable.aemeasurable hvol
  have hsub : Ioo (0 : ℝ) θ ⊆ Ioc (-θ) (-θ + 2 * θ) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hpull' := ae_restrict_of_ae_restrict_of_subset hsub hpull
  filter_upwards [hpull', ae_restrict_mem measurableSet_Ioo] with x hx hmem
  have hx' : x ∈ Ioc (-θ) (-θ + 2 * θ) := hsub hmem
  change f x = 0
  simpa only [F, AddCircle.liftIoc_coe_apply hx', oddIntervalExtension_of_pos f hmem.1] using hx

end LatticeProb
