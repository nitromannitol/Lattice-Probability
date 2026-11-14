import Mathlib

/-! # Segment bounds for differentiable functions -/

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb.PegdenSmart

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The oscillation between two points is bounded by the integral of the derivative along the
segment joining them. -/
theorem enorm_sub_le_segment_integral {f : E → F} {a z y : E} {r : ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball a r))
    (hz : z ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) :
    ‖f y - f z‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
      ‖fderiv ℝ f (z + t • (y - z))‖ₑ * ‖y - z‖ₑ := by
  let g : ℝ → E := fun t => z + t • (y - z)
  have hg : ContDiff ℝ 1 g := by
    dsimp [g]
    fun_prop
  have hmem : MapsTo g (Icc 0 1) (Metric.ball a r) := by
    intro t ht
    simpa [g, AffineMap.lineMap_apply, add_comm] using
      (convex_ball a r).lineMap_mem hz hy ht
  have hfg : ContDiffOn ℝ 1 (f ∘ g) (Icc 0 1) := hf.comp hg.contDiffOn hmem
  have hbound := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hfg (by norm_num)
  simpa only [Function.comp_apply, g, zero_smul, add_zero, one_smul, add_sub_cancel] using
    hbound.trans (lintegral_mono_ae (by
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t htmem
      have ht : HasDerivAt g (y - z) t := by
        dsimp [g]
        simpa using (hasDerivAt_id t).smul_const (y - z) |>.const_add z
      have hm := hmem htmem
      have hd := (hf (g t) hm).contDiffAt (Metric.isOpen_ball.mem_nhds hm)
        |>.differentiableAt (by norm_num)
      rw [hd.hasFDerivAt.comp_hasDerivAt t ht |>.deriv]
      exact ContinuousLinearMap.le_opENorm _ _))

/-- Averaging the segment estimate over a ball. -/
theorem lintegral_enorm_sub_le_segment_integral
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) {f : E → F} {a z : E} {r : ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball a r)) (hz : z ∈ Metric.ball a r) :
    ∫⁻ y in Metric.ball a r, ‖f z - f y‖ₑ ∂μ ≤
      ∫⁻ y in Metric.ball a r, ∫⁻ t in Icc (0 : ℝ) 1,
        ‖fderiv ℝ f (z + t • (y - z))‖ₑ * ‖y - z‖ₑ ∂volume ∂μ := by
  apply lintegral_mono_ae
  filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet] with y hy
  simpa only [enorm_sub_rev] using enorm_sub_le_segment_integral hf hz hy

/-- Haar measure under a homothety around a fixed point. -/
theorem map_addHaar_segment [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (z : E) {t : ℝ} (ht : t ≠ 0) :
    Measure.map (fun y : E => z + t • (y - z)) μ =
      ENNReal.ofReal (abs (t ^ Module.finrank ℝ E)⁻¹) • μ := by
  have heq : (fun y : E => z + t • (y - z)) =
      (fun y : E => (z - t • z) + y) ∘ (fun y : E => t • y) := by
    funext y
    simp only [Function.comp_apply, smul_sub]
    abel
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), Measure.map_addHaar_smul μ ht,
    Measure.map_smul _ (by fun_prop), Measure.IsAddLeftInvariant.map_add_left_eq_self]

/-- Change variables under a homothety around a fixed point. -/
theorem lintegral_segment_homothety [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : E) {t : ℝ} (ht : t ≠ 0)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g (z + t • (y - z)) ∂μ =
      ENNReal.ofReal (abs (t ^ Module.finrank ℝ E)⁻¹) * ∫⁻ w, g w ∂μ := by
  rw [← lintegral_map hg (by fun_prop), map_addHaar_segment μ z ht,
    lintegral_smul_measure]
  rfl

/-- A point on a segment in a ball remains in the ball and its distance from the
initial point is controlled by the diameter. -/
theorem segment_mem_ball_and_norm_le {a z y : E} {r t : ℝ}
    (hz : z ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) (ht : t ∈ Icc 0 1) :
    z + t • (y - z) ∈ Metric.ball a r ∧ ‖(z + t • (y - z)) - z‖ ≤ 2 * r * t := by
  constructor
  · simpa [AffineMap.lineMap_apply, add_comm] using
      (convex_ball a r).lineMap_mem hz hy ht
  · have hdist : ‖y - z‖ ≤ 2 * r := by
      have h := dist_triangle y a z
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev a z] at h
      have hy' : ‖y - a‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      have hz' : ‖z - a‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      linarith
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [mul_le_mul_of_nonneg_left hdist ht.1]

/-- The tail integral of the power kernel arising from a homothety. -/
theorem lintegral_rpow_tail {d b : ℝ} (hd : 0 < d) (hb : 0 < b) :
    ∫⁻ t in Ioi b, ENNReal.ofReal (t ^ (-d - 1)) =
      ENNReal.ofReal (b ^ (-d) / d) := by
  have he : -d - 1 < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt he hb)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (le_of_lt (lt_trans hb ht)) _)]
  rw [integral_Ioi_rpow_of_lt he hb]
  congr 1
  have heq : -d - 1 + 1 = -d := by ring
  rw [heq]
  ring

/-- The derivative norm, extended by zero outside the ball, is measurable. -/
theorem measurable_indicator_enorm_fderiv [MeasurableSpace E] [BorelSpace E]
    {f : E → F} {a : E} {r : ℝ} (hf : ContDiffOn ℝ 1 f (Metric.ball a r)) :
    Measurable ((Metric.ball a r).indicator fun x => ‖fderiv ℝ f x‖ₑ) := by
  classical
  have h := (hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).enorm
  convert h.measurable_piecewise (g := fun _ => (0 : ℝ≥0∞)) continuousOn_const
    Metric.isOpen_ball.measurableSet using 1
  ext x
  simp [Set.indicator, Set.piecewise]

/-- Tonelli's theorem for the segment integral. -/
theorem lintegral_segment_swap [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (a z : E) (r : ℝ)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y in Metric.ball a r, ∫⁻ t in Icc (0 : ℝ) 1,
      g (z + t • (y - z)) * ‖y - z‖ₑ ∂volume ∂μ =
    ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Metric.ball a r,
      g (z + t • (y - z)) * ‖y - z‖ₑ ∂μ ∂volume := by
  have hmeas : Measurable (fun p : E × ℝ =>
      g (z + p.2 • (p.1 - z)) * ‖p.1 - z‖ₑ) := by
    fun_prop
  exact lintegral_lintegral_swap hmeas.aemeasurable

/-- Change variables for a segment integral weighted by distance from the center. -/
theorem lintegral_segment_homothety_weighted [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : E) {t : ℝ} (ht : t ≠ 0)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g (z + t • (y - z)) * ‖(z + t • (y - z)) - z‖ₑ ∂μ =
      ENNReal.ofReal (abs (t ^ Module.finrank ℝ E)⁻¹) *
        ∫⁻ w, g w * ‖w - z‖ₑ ∂μ := by
  exact lintegral_segment_homothety μ z ht (g := fun w => g w * ‖w - z‖ₑ) (by fun_prop)

/-- The distance factor under a nonzero homothety. -/
theorem enorm_sub_eq_inv_mul_segment {z y : E} {t : ℝ} (ht : t ≠ 0) :
    ‖y - z‖ₑ = ‖t⁻¹‖ₑ * ‖(z + t • (y - z)) - z‖ₑ := by
  calc
    ‖y - z‖ₑ = ‖t⁻¹ • ((z + t • (y - z)) - z)‖ₑ := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = _ := enorm_smul _ _

/-- Restricted change of variables for segment integrals. -/
theorem lintegral_segment_le_homothety [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {a z : E} {r t : ℝ}
    (hz : z ∈ Metric.ball a r) (ht : t ∈ Icc 0 1) (ht0 : t ≠ 0)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y in Metric.ball a r, g (z + t • (y - z)) * ‖y - z‖ₑ ∂μ ≤
      ‖t⁻¹‖ₑ * (ENNReal.ofReal (abs (t ^ Module.finrank ℝ E)⁻¹) *
        ∫⁻ w in Metric.ball a r ∩ Metric.closedBall z (2 * r * t),
          g w * ‖w - z‖ₑ ∂μ) := by
  classical
  let s := Metric.ball a r ∩ Metric.closedBall z (2 * r * t)
  have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet.inter
    Metric.isClosed_closedBall.measurableSet
  have hg' : Measurable (s.indicator g) := hg.indicator hs
  calc
    _ = ‖t⁻¹‖ₑ * ∫⁻ y in Metric.ball a r,
        (s.indicator g) (z + t • (y - z)) * ‖(z + t • (y - z)) - z‖ₑ ∂μ := by
      rw [← lintegral_const_mul' _ _ (enorm_ne_top)]
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet] with y hy
      have h := segment_mem_ball_and_norm_le hz hy ht
      have hmem : z + t • (y - z) ∈ s := by
        refine ⟨h.1, ?_⟩
        simpa [Metric.mem_closedBall, dist_eq_norm] using h.2
      rw [Set.indicator_of_mem hmem, enorm_sub_eq_inv_mul_segment ht0]
      ac_rfl
    _ ≤ ‖t⁻¹‖ₑ * ∫⁻ y,
        (s.indicator g) (z + t • (y - z)) * ‖(z + t • (y - z)) - z‖ₑ ∂μ := by
      gcongr
      exact Measure.restrict_le_self
    _ = _ := by
      rw [lintegral_segment_homothety_weighted μ z ht0 hg']
      congr 2
      rw [← lintegral_indicator hs]
      apply lintegral_congr
      intro w
      by_cases hw : w ∈ s <;> simp [hw]

/-- The density of the weighted homothety is a negative power. -/
theorem homothety_density_eq_rpow {t : ℝ} (ht : 0 < t) (d : ℕ) :
    ‖t⁻¹‖ₑ * ENNReal.ofReal (abs (t ^ d)⁻¹) =
      ENNReal.ofReal (t ^ (-(d : ℝ) - 1)) := by
  rw [Real.enorm_eq_ofReal (inv_nonneg.mpr ht.le), abs_of_pos (inv_pos.mpr (pow_pos ht d)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  congr 1
  rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_natCast,
    Real.rpow_neg_one]
  ring

/-- Restricting the power kernel to times above a positive cutoff. -/
theorem lintegral_rpow_cutoff {d b : ℝ} (hd : 0 < d) (hb : 0 < b) :
    ∫⁻ t in Icc (0 : ℝ) 1 ∩ Ici b, ENNReal.ofReal (t ^ (-d - 1)) ≤
      ENNReal.ofReal (b ^ (-d) / d) := by
  calc
    _ ≤ ∫⁻ t in Ici b, ENNReal.ofReal (t ^ (-d - 1)) :=
      lintegral_mono_set inter_subset_right
    _ = _ := by rw [← restrict_Ioi_eq_restrict_Ici, lintegral_rpow_tail hd hb]

/-- Algebraic form of the Riesz kernel coefficient. -/
theorem rpow_cutoff_mul {x R : ℝ} (hx : 0 < x) (hR : 0 < R) (d : ℕ) :
    ((x / R) ^ (-(d : ℝ)) / d) * x =
      (R ^ d / d) * x ^ (1 - (d : ℝ)) := by
  rw [Real.div_rpow hx.le hR.le, Real.rpow_neg hR.le, Real.rpow_natCast,
    Real.rpow_sub hx, Real.rpow_one, Real.rpow_natCast, Real.rpow_neg hx.le,
    Real.rpow_natCast]
  field_simp

/-- Extended-nonnegative-real form of the Riesz kernel coefficient. -/
theorem ofReal_rpow_cutoff_mul {x R : ℝ} (hx : 0 < x) (hR : 0 < R) (d : ℕ) :
    ENNReal.ofReal ((x / R) ^ (-(d : ℝ)) / d) * ENNReal.ofReal x =
      ENNReal.ofReal (R ^ d / d) * (ENNReal.ofReal x) ^ (1 - (d : ℝ)) := by
  rw [ENNReal.ofReal_rpow_of_pos hx, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), rpow_cutoff_mul hx hR d]

/-- The power kernel with a cutoff contributes the Riesz kernel. -/
theorem lintegral_cutoff_riesz {x R : ℝ} (hx : 0 < x) (hR : 0 < R)
    {d : ℕ} (hd : 0 < d) :
    (∫⁻ t in Icc (0 : ℝ) 1,
      (Ici (x / R)).indicator (fun t => ENNReal.ofReal (t ^ (-(d : ℝ) - 1))) t) *
        ENNReal.ofReal x ≤
      ENNReal.ofReal (R ^ d / d) * (ENNReal.ofReal x) ^ (1 - (d : ℝ)) := by
  have hcast : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    _ = (∫⁻ t in Icc (0 : ℝ) 1 ∩ Ici (x / R),
        ENNReal.ofReal (t ^ (-(d : ℝ) - 1))) * ENNReal.ofReal x := by
      rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
      rw [inter_comm]
    _ ≤ ENNReal.ofReal ((x / R) ^ (-(d : ℝ)) / d) * ENNReal.ofReal x := by
      gcongr
      exact lintegral_rpow_cutoff hcast (div_pos hx hR)
    _ = _ := ofReal_rpow_cutoff_mul hx hR d

/-- The averaged oscillation is bounded by the time-first segment integral. -/
theorem lintegral_enorm_sub_le_segment_integral_swapped
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F} {a z : E} {r : ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball a r)) (hz : z ∈ Metric.ball a r) :
    ∫⁻ y in Metric.ball a r, ‖f z - f y‖ₑ ∂μ ≤
      ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Metric.ball a r,
        ‖fderiv ℝ f (z + t • (y - z))‖ₑ * ‖y - z‖ₑ ∂μ ∂volume := by
  let g := (Metric.ball a r).indicator (fun x => ‖fderiv ℝ f x‖ₑ)
  have hg : Measurable g := measurable_indicator_enorm_fderiv hf
  have hpoint : ∀ y ∈ Metric.ball a r, ∀ t ∈ Icc (0 : ℝ) 1,
      g (z + t • (y - z)) = ‖fderiv ℝ f (z + t • (y - z))‖ₑ := by
    intro y hy t ht
    exact Set.indicator_of_mem (segment_mem_ball_and_norm_le hz hy ht).1 _
  have heq : ∫⁻ y in Metric.ball a r, ∫⁻ t in Icc (0 : ℝ) 1,
      g (z + t • (y - z)) * ‖y - z‖ₑ ∂volume ∂μ =
      ∫⁻ y in Metric.ball a r, ∫⁻ t in Icc (0 : ℝ) 1,
        ‖fderiv ℝ f (z + t • (y - z))‖ₑ * ‖y - z‖ₑ ∂volume ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet] with y hy
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    rw [hpoint y hy t ht]
  have heq' : ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Metric.ball a r,
      g (z + t • (y - z)) * ‖y - z‖ₑ ∂μ ∂volume =
      ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Metric.ball a r,
        ‖fderiv ℝ f (z + t • (y - z))‖ₑ * ‖y - z‖ₑ ∂μ ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet] with y hy
    rw [hpoint y hy t ht]
  calc
    _ ≤ _ := lintegral_enorm_sub_le_segment_integral μ hf hz
    _ = _ := heq.symm
    _ = _ := lintegral_segment_swap μ a z r hg
    _ = _ := heq'

/-- The time-first segment integral is bounded by a radial cutoff integral. -/
theorem lintegral_segment_le_radial_cutoff [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {a z : E} {r : ℝ}
    (hz : z ∈ Metric.ball a r) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Metric.ball a r,
      g (z + t • (y - z)) * ‖y - z‖ₑ ∂μ ∂volume ≤
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(Module.finrank ℝ E : ℝ) - 1)) *
      ∫⁻ w in Metric.ball a r ∩ Metric.closedBall z (2 * r * t),
        g w * ‖w - z‖ₑ ∂μ ∂volume := by
  apply lintegral_mono_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  convert lintegral_segment_le_homothety μ hz ht ht0 hg using 1
  rw [← mul_assoc, homothety_density_eq_rpow htpos]

/-- Tonelli's theorem for a radial cutoff. -/
theorem lintegral_radial_cutoff_swap [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (a z : E) (r : ℝ)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    let s : Set (ℝ × E) := {p | ‖p.2 - z‖ ≤ 2 * r * p.1}
    let h : ℝ × E → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (p.1 ^ (-(Module.finrank ℝ E : ℝ) - 1)) * (g p.2 * ‖p.2 - z‖ₑ)
    (∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ w in Metric.ball a r, s.indicator h (t, w) ∂μ ∂volume) =
      ∫⁻ w in Metric.ball a r, ∫⁻ t in Icc (0 : ℝ) 1, s.indicator h (t, w) ∂volume ∂μ := by
  dsimp only
  have hs : MeasurableSet {p : ℝ × E | ‖p.2 - z‖ ≤ 2 * r * p.1} := by
    exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hh : Measurable (fun p : ℝ × E =>
      ENNReal.ofReal (p.1 ^ (-(Module.finrank ℝ E : ℝ) - 1)) *
        (g p.2 * ‖p.2 - z‖ₑ)) := by
    fun_prop
  exact lintegral_lintegral_swap (hh.indicator hs).aemeasurable

end LatticeProb.PegdenSmart
