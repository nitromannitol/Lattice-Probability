import LatticeProb.Analysis.IntervalSineUniqueness

/-! # Sine completeness on translated intervals -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Sine coefficients determine an L² function on any interval of positive length. -/
theorem ae_eq_zero_of_translated_interval_sine_integrals_eq_zero {a θ : ℝ}
    (hθ : 0 < θ) {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioo a (a + θ))))
    (hsine : ∀ n : ℕ, (∫ x in a..(a + θ),
      (Real.sin (Real.pi * (n : ℝ) * (x - a) / θ) : ℂ) * f x) = 0) :
    f =ᵐ[volume.restrict (Ioo a (a + θ))] 0 := by
  let : Fact (0 < 2 * θ) := ⟨by linarith⟩
  have hmap : Measure.map (fun x : ℝ => x + a) (volume.restrict (Ioo 0 θ)) =
      volume.restrict (Ioo a (a + θ)) := by
    have h := ((measurePreserving_add_right (volume : Measure ℝ) a).restrict_image_emb
      (measurableEmbedding_addRight a) (Ioo 0 θ)).map_eq
    simpa only [image_add_const_Ioo, zero_add, add_comm θ a] using h
  have hback : Measure.map (fun x : ℝ => x + -a) (volume.restrict (Ioo a (a + θ))) =
      volume.restrict (Ioo 0 θ) := by
    have h := ((measurePreserving_add_right (volume : Measure ℝ) (-a)).restrict_image_emb
      (measurableEmbedding_addRight (-a)) (Ioo a (a + θ))).map_eq
    have hcancel : a + θ + -a = θ := by ring
    simpa only [image_add_const_Ioo, add_neg_cancel, hcancel] using h
  have hg : MemLp (fun x : ℝ => f (x + a)) 2 (volume.restrict (Ioo 0 θ)) := by
    have hfm : MemLp f 2 (Measure.map (fun x : ℝ => x + a) (volume.restrict (Ioo 0 θ))) := by
      rw [hmap]
      exact hf
    exact hfm.comp_of_map (measurable_id.add_const a).aemeasurable
  have hc : ∀ n : ℕ, (∫ x in (0 : ℝ)..θ,
      (Real.sin (Real.pi * (n : ℝ) * x / θ) : ℂ) * f (x + a)) = 0 := by
    intro n
    have h := intervalIntegral.integral_comp_add_right (a := 0) (b := θ)
      (fun x : ℝ => (Real.sin (Real.pi * (n : ℝ) * (x - a) / θ) : ℂ) * f x) a
    have h' : (∫ x in (0 : ℝ)..θ,
        (Real.sin (Real.pi * (n : ℝ) * x / θ) : ℂ) * f (x + a)) =
        (∫ x in a..(a + θ),
        (Real.sin (Real.pi * (n : ℝ) * (x - a) / θ) : ℂ) * f x) := by
      simpa only [add_sub_cancel_right, zero_add, add_comm θ a] using h
    exact h'.trans (hsine n)
  have hz := ae_eq_zero_of_interval_sine_integrals_eq_zero hg hc
  rw [← hback] at hz
  have hz' := ae_of_ae_map (measurable_id.add_const (-a)).aemeasurable hz
  filter_upwards [hz'] with x hx
  simpa only [Pi.zero_apply, id_eq, add_assoc, neg_add_cancel, add_zero] using hx

end LatticeProb
