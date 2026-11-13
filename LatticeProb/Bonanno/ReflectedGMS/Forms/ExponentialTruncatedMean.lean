/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ExponentialTruncatedMean at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessGeneralSide
import Mathlib.Probability.Distributions.Exponential

/-!
# The truncated mean of an exponential holding time

For `L ~ Exponential(r)` and a cutoff `c ≥ 0`,

  `E[min(L, c)] = (1/r) · P(L ≤ c)`.

This is the one-variable identity behind the sojourn-by-sojourn energy accounting: the
expected squared edge jump of a sojourn that ends before the horizon equals the carré du
champ times the expected Lebesgue length of the sojourn inside the horizon, with no error
term.  It is stated for the law `(expMeasure r).map toWithTop` on `[0, ∞]` used by property
(iii) of the reflected walk.

The proof is the layer-cake formula `E[min(L,c)] = ∫_0^c P(L > y) dy` together with
`P(L > y) = e^{−ry} = (1/r) · pdf_r(y)`, so that the integral is `(1/r)` times the mass of
`(0, c)`, which is `P(L ≤ c)` since the exponential law has no atoms and no mass on `(−∞,0]`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.ExponentialTruncatedMean

open ReflectedWalk.Theorem16

variable {r : ℝ} (hr : 0 < r)
include hr

theorem expMeasure_Iic_eq (c : ℝ) (hc : 0 ≤ c) :
    expMeasure r (Iic c) = ENNReal.ofReal (1 - Real.exp (-(r * c))) := by
  haveI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hc]

theorem expMeasure_Ioi_eq (y : ℝ) (hy : 0 ≤ y) :
    expMeasure r (Ioi y) = ENNReal.ofReal (Real.exp (-(r * y))) := by
  haveI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hcompl : Ioi y = (Iic y)ᶜ := (compl_Iic).symm
  rw [hcompl, prob_compl_eq_one_sub measurableSet_Iic, expMeasure_Iic_eq hr y hy]
  have he : Real.exp (-(r * y)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hr.le])
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (sub_nonneg.2 he)]
  congr 1
  ring

/-- The exponential law charges no point. -/
theorem expMeasure_singleton (c : ℝ) : expMeasure r {c} = 0 := by
  unfold expMeasure gammaMeasure
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- The mass of `[0, c]` is carried by the open interval `(0, c)`. -/
theorem expMeasure_Ioo_eq_Iic (c : ℝ) (hc : 0 ≤ c) :
    expMeasure r (Ioo 0 c) = expMeasure r (Iic c) := by
  apply le_antisymm (measure_mono (Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self))
  have hsub : Iic c ⊆ Iic 0 ∪ Ioo 0 c ∪ {c} := by
    intro x hx
    simp only [mem_Iic] at hx
    rcases le_or_gt x 0 with h0 | h0
    · exact Or.inl (Or.inl h0)
    · rcases lt_or_eq_of_le hx with hxc | hxc
      · exact Or.inl (Or.inr ⟨h0, hxc⟩)
      · exact Or.inr hxc
  calc expMeasure r (Iic c) ≤ expMeasure r (Iic 0 ∪ Ioo 0 c ∪ {c}) := measure_mono hsub
    _ ≤ expMeasure r (Iic 0 ∪ Ioo 0 c) + expMeasure r {c} := measure_union_le _ _
    _ ≤ expMeasure r (Iic 0) + expMeasure r (Ioo 0 c) + expMeasure r {c} :=
        add_le_add (measure_union_le _ _) le_rfl
    _ = expMeasure r (Ioo 0 c) := by
        rw [expMeasure_Iic_zero hr, expMeasure_singleton hr, zero_add, add_zero]

/-- The exponential density on `(0, ∞)` is `r e^{−ry}`, so `e^{−ry} = (1/r) · pdf(y)`. -/
theorem ofReal_exp_eq_pdf (y : ℝ) (hy : 0 ≤ y) :
    ENNReal.ofReal (Real.exp (-(r * y))) = ENNReal.ofReal (1 / r) * exponentialPDF r y := by
  rw [exponentialPDF_of_nonneg hy, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

omit hr in
/-- The exponential measure of a measurable set is the integral of its density. -/
theorem expMeasure_apply_eq_lintegral {s : Set ℝ} (hs : MeasurableSet s) :
    expMeasure r s = ∫⁻ y in s, exponentialPDF r y := by
  unfold expMeasure gammaMeasure
  rw [withDensity_apply _ hs]
  rfl

/-- **The truncated mean of an exponential holding time, on `ℝ`.** -/
theorem lintegral_ofReal_min_expMeasure (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ t, ENNReal.ofReal (min t c) ∂expMeasure r) =
      ENNReal.ofReal (1 / r) * expMeasure r (Iic c) := by
  haveI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hpos : ∀ᵐ t ∂expMeasure r, (0 : ℝ) < t := by
    rw [ae_iff]
    have he : {t : ℝ | ¬ (0 : ℝ) < t} = Iic 0 := by ext t; simp
    rw [he]
    exact expMeasure_Iic_zero hr
  have hnn : 0 ≤ᵐ[expMeasure r] fun t => min t c := by
    filter_upwards [hpos] with t ht
    exact le_min ht.le hc
  rw [lintegral_eq_lintegral_meas_lt _ hnn (measurable_id.min measurable_const).aemeasurable]
  -- the level sets of `min t c`
  have hlevel : ∀ y : ℝ, expMeasure r {t | y < min t c} =
      (Iio c).indicator (fun y => expMeasure r (Ioi y)) y := by
    intro y
    by_cases hyc : y < c
    · rw [indicator_of_mem (mem_Iio.2 hyc)]
      congr 1
      ext t
      simp [lt_min_iff, hyc]
    · rw [indicator_of_notMem (fun h => hyc (mem_Iio.1 h))]
      have he : {t : ℝ | y < min t c} = ∅ := by
        ext t
        simp only [mem_setOf_eq, lt_min_iff, mem_empty_iff_false, iff_false, not_and]
        intro _
        exact hyc
      rw [he, measure_empty]
  simp_rw [hlevel]
  rw [← lintegral_indicator measurableSet_Ioi]
  have hcomb : ∀ y, (Ioi (0 : ℝ)).indicator
      (fun y => (Iio c).indicator (fun y => expMeasure r (Ioi y)) y) y =
      (Ioo 0 c).indicator (fun y => ENNReal.ofReal (1 / r) * exponentialPDF r y) y := by
    intro y
    by_cases hy : y ∈ Ioo 0 c
    · rw [indicator_of_mem hy, indicator_of_mem (mem_Ioi.2 hy.1), indicator_of_mem (mem_Iio.2 hy.2),
        expMeasure_Ioi_eq hr y hy.1.le, ofReal_exp_eq_pdf hr y hy.1.le]
    · rw [indicator_of_notMem hy]
      by_cases hy0 : y ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hy0]
        have hyc : y ∉ Iio c := fun h => hy ⟨mem_Ioi.1 hy0, mem_Iio.1 h⟩
        rw [indicator_of_notMem hyc]
      · rw [indicator_of_notMem hy0]
  have hpdf : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  refine (lintegral_congr hcomb).trans ?_
  rw [lintegral_indicator measurableSet_Ioo, lintegral_const_mul _ hpdf,
    ← expMeasure_apply_eq_lintegral measurableSet_Ioo, expMeasure_Ioo_eq_Iic hr c hc]

omit hr in
/-- The truncation of the lifted holding time on `[0, ∞]` is the lift of the real truncation. -/
theorem min_toWithTop_eq (t : ℝ) (c : ℝ≥0) :
    min (toWithTop t) (c : WithTop ℝ≥0) = ENNReal.ofReal (min t c) := by
  rcases le_total t c with h | h
  · rw [min_eq_left h]
    have hle : toWithTop t ≤ (c : WithTop ℝ≥0) :=
      WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 h)
    rw [min_eq_left hle]
    rfl
  · rw [min_eq_right h]
    have h0 : (0 : ℝ) ≤ t := (c.2 : (0 : ℝ) ≤ c).trans h
    have hle : (c : WithTop ℝ≥0) ≤ toWithTop t :=
      WithTop.coe_le_coe.2 ((Real.le_toNNReal_iff_coe_le h0).2 h)
    rw [min_eq_right hle]
    exact (ENNReal.ofReal_coe_nnreal).symm

omit hr in
/-- The lifted law of `[0, c]`. -/
theorem map_toWithTop_expMeasure_Iic (c : ℝ≥0) :
    ((expMeasure r).map toWithTop) (Iic (c : WithTop ℝ≥0)) = expMeasure r (Iic (c : ℝ)) := by
  rw [Measure.map_apply measurable_toWithTop measurableSet_Iic]
  congr 1
  ext t
  simp only [mem_preimage, mem_Iic, toWithTop, WithTop.coe_le_coe]
  exact Real.toNNReal_le_iff_le_coe

/-- **The truncated mean of an exponential holding time, on `[0, ∞]`:**
`E[min(L, c)] = (1/r) · P(L ≤ c)`. -/
theorem lintegral_min_map_toWithTop_expMeasure (c : ℝ≥0) :
    (∫⁻ l, min l (c : WithTop ℝ≥0) ∂(expMeasure r).map toWithTop) =
      ENNReal.ofReal (1 / r) * ((expMeasure r).map toWithTop) (Iic (c : WithTop ℝ≥0)) := by
  have hf : Measurable (fun l : WithTop ℝ≥0 => min l (c : WithTop ℝ≥0)) :=
    measurable_id.min measurable_const
  calc (∫⁻ l, min l (c : WithTop ℝ≥0) ∂(expMeasure r).map toWithTop) =
        ∫⁻ t, min (toWithTop t) (c : WithTop ℝ≥0) ∂expMeasure r :=
        lintegral_map hf measurable_toWithTop
    _ = ∫⁻ t, ENNReal.ofReal (min t c) ∂expMeasure r :=
        lintegral_congr fun t => min_toWithTop_eq t c
    _ = ENNReal.ofReal (1 / r) * expMeasure r (Iic (c : ℝ)) :=
        lintegral_ofReal_min_expMeasure hr c c.2
    _ = _ := by rw [map_toWithTop_expMeasure_Iic c]

end ReflectedGMS.ExponentialTruncatedMean
