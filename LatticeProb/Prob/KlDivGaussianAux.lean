/-
The relative entropy between two Gaussians of a common variance.

Mathlib has `InformationTheory.klDiv` and the Gaussian density, but no relative
entropy between two Gaussians.  The one-dimensional value is `m²/(2v)` for means
`0` and `m` and variance `v`; the finite product form is in
`LatticeProb/Prob/KlDivGaussianPi.lean`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

theorem toReal_inv_mul_ofReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((ENNReal.ofReal b)⁻¹ * ENNReal.ofReal a).toReal = a / b := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal hb.le, inv_mul_eq_div]

theorem llr_gaussianReal_eq {v : ℝ≥0} (hv : v ≠ 0) (m : ℝ) :
    MeasureTheory.llr (ProbabilityTheory.gaussianReal 0 v)
        (ProbabilityTheory.gaussianReal m v)
      =ᵐ[(MeasureTheory.volume : Measure ℝ)] fun x =>
        Real.log (ProbabilityTheory.gaussianPDFReal 0 v x /
          ProbabilityTheory.gaussianPDFReal m v x) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hv,
    ProbabilityTheory.gaussianReal_of_var_ne_zero m hv]
  haveI : SigmaFinite (MeasureTheory.volume.withDensity (ProbabilityTheory.gaussianPDF 0 v)) :=
    SigmaFinite.withDensity_of_ne_top
      (Filter.Eventually.of_forall fun x => (ProbabilityTheory.gaussianPDF_lt_top (μ := 0) (v := v)).ne)
  filter_upwards [MeasureTheory.Measure.rnDeriv_withDensity_right
      (MeasureTheory.volume.withDensity (ProbabilityTheory.gaussianPDF 0 v)) MeasureTheory.volume
      (ProbabilityTheory.measurable_gaussianPDF m v).aemeasurable
      (Filter.Eventually.of_forall fun x => (ProbabilityTheory.gaussianPDF_pos m hv x).ne')
      (Filter.Eventually.of_forall fun x => (ProbabilityTheory.gaussianPDF_lt_top (μ := m) (v := v)).ne),
    MeasureTheory.Measure.rnDeriv_withDensity MeasureTheory.volume
      (ProbabilityTheory.measurable_gaussianPDF 0 v)] with x hx hx0
  show Real.log ((MeasureTheory.Measure.rnDeriv (MeasureTheory.volume.withDensity (ProbabilityTheory.gaussianPDF 0 v)) (MeasureTheory.volume.withDensity (ProbabilityTheory.gaussianPDF m v)) x).toReal) = _
  rw [hx, hx0]
  rw [ProbabilityTheory.gaussianPDF_def, ProbabilityTheory.gaussianPDF_def]
  rw [toReal_inv_mul_ofReal (ProbabilityTheory.gaussianPDFReal_pos 0 v x hv)
    (ProbabilityTheory.gaussianPDFReal_pos m v x hv)]

theorem log_gaussianPDFReal_div {v : ℝ≥0} (hv : v ≠ 0) (m x : ℝ) :
    Real.log (ProbabilityTheory.gaussianPDFReal 0 v x /
        ProbabilityTheory.gaussianPDFReal m v x) = (m ^ 2 - 2 * m * x) / (2 * v) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by
    have h : (0 : ℝ≥0) < v := lt_of_le_of_ne v.coe_nonneg (Ne.symm hv)
    exact_mod_cast h
  have hc : (√(2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  rw [ProbabilityTheory.gaussianPDFReal_def, ProbabilityTheory.gaussianPDFReal_def]
  simp only [sub_zero]
  rw [show (√(2 * Real.pi * ↑v))⁻¹ * Real.exp (-x ^ 2 / (2 * ↑v)) /
        ((√(2 * Real.pi * ↑v))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * ↑v)))
      = Real.exp (-x ^ 2 / (2 * ↑v)) / Real.exp (-(x - m) ^ 2 / (2 * ↑v)) from by
    rw [mul_div_mul_left _ _ hc]]
  rw [← Real.exp_sub, Real.log_exp]
  field_simp
  ring

theorem integral_llr_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) (m : ℝ) :
    ∫ x, (m ^ 2 - 2 * m * x) / (2 * v) ∂(ProbabilityTheory.gaussianReal 0 v)
      = m ^ 2 / (2 * v) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by
    have h : (0 : ℝ≥0) < v := lt_of_le_of_ne v.coe_nonneg (Ne.symm hv)
    exact_mod_cast h
  have hint : Integrable (fun x : ℝ => x) (ProbabilityTheory.gaussianReal 0 v) :=
    ProbabilityTheory.IsGaussian.integrable_id
  have h2 : ∫ x, (m ^ 2 / (2 * v) - (2 * m / (2 * v)) * x)
        ∂(ProbabilityTheory.gaussianReal 0 v)
      = ∫ x, (m ^ 2 / (2 * v)) ∂(ProbabilityTheory.gaussianReal 0 v)
        - ∫ x, (2 * m / (2 * v)) * x ∂(ProbabilityTheory.gaussianReal 0 v) :=
    integral_sub (integrable_const _) (hint.const_mul _)
  rw [show (fun x => (m ^ 2 - 2 * m * x) / (2 * v))
      = fun x => (m ^ 2) / (2 * v) - (2 * m / (2 * v)) * x from by
    funext x; ring]
  rw [h2, integral_const_mul, integral_const,
    ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := v)]
  simp

end LatticeProb
