import Mathlib

/-!
# Small-ball probabilities of a centred Gaussian variable

Lower bounds for the probability `P(|N| ≤ r)` that a centred real Gaussian variable `N` of variance `v > 0` lies in
the interval `[-r, r]`:

* `ofReal_le_gaussianReal_Icc_neg`: `2 e^{-1/2} r / √(2π v) ≤ P(|N| ≤ r)` for `0 ≤ r ≤ √v`, since the density is at
  least `e^{-1/2} / √(2π v)` on `[-√v, √v]`;
* `ofReal_mul_min_le_gaussianReal_Icc_neg`: `(2 e^{-1/2} / √(2π)) min 1 (r / √v) ≤ P(|N| ≤ r)` for every `r ≥ 0`.

With the upper bound `P(N ∈ [c, d]) ≤ (d - c) / √(2π v)` (`LatticeProb.gaussianReal_Icc_le`) they give the order
`min 1 (r / √v)` of the small-ball probability.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- **Small-ball lower bound for a centred Gaussian variable, small radius.** For variance `v > 0` and
`0 ≤ r` with `r ^ 2 ≤ v`, `P(|N| ≤ r) ≥ 2 e^{-1/2} r / √(2π v)`. -/
theorem ofReal_le_gaussianReal_Icc_neg {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 ≤ r) (hrv : r ^ 2 ≤ v) :
    ENNReal.ofReal (2 * r * Real.exp (-(1 / 2)) / √(2 * Real.pi * v)) ≤
      gaussianReal 0 v (Set.Icc (-r) r) := by
  rw [gaussianReal_apply_eq_integral 0 hv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hv0 : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.2 hv
  have hsq : 0 < √(2 * Real.pi * v) := by positivity
  calc 2 * r * Real.exp (-(1 / 2)) / √(2 * Real.pi * v)
      = ∫ _ in Set.Icc (-r) r, (√(2 * Real.pi * v))⁻¹ * Real.exp (-(1 / 2)) := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        field_simp
        ring
    _ ≤ ∫ x in Set.Icc (-r) r, gaussianPDFReal 0 v x := by
        refine setIntegral_mono_on (integrableOn_const (by simp))
          ((integrable_gaussianPDFReal 0 v).integrableOn) measurableSet_Icc fun x hx => ?_
        simp only [gaussianPDFReal_def, sub_zero]
        gcongr
        have hx2 : x ^ 2 ≤ v := by
          have : |x| ≤ r := abs_le.2 hx
          calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
            _ ≤ r ^ 2 := by gcongr
            _ ≤ v := hrv
        rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
        linarith

/-- **Small-ball lower bound for a centred Gaussian variable.** For variance `v > 0` and every `r ≥ 0`,
`P(|N| ≤ r) ≥ (2 e^{-1/2} / √(2π)) min 1 (r / √v)`. -/
theorem ofReal_mul_min_le_gaussianReal_Icc_neg {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (2 * Real.exp (-(1 / 2)) / √(2 * Real.pi) * min 1 (r / √v)) ≤
      gaussianReal 0 v (Set.Icc (-r) r) := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.2 hv
  have hsv : 0 < √(v : ℝ) := Real.sqrt_pos.2 hv0
  have hpi : 0 < √(2 * Real.pi) := by positivity
  have hsplit : √(2 * Real.pi * v) = √(2 * Real.pi) * √v :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi) v
  rcases le_total r (√v) with h | h
  · have hrv : r ^ 2 ≤ (v : ℝ) := by
      calc r ^ 2 ≤ (√(v : ℝ)) ^ 2 := by gcongr
        _ = (v : ℝ) := Real.sq_sqrt hv0.le
    refine le_trans (le_of_eq ?_) (ofReal_le_gaussianReal_Icc_neg hv hr hrv)
    congr 1
    rw [min_eq_right ((div_le_one hsv).2 h), hsplit]
    field_simp
  · have hrv : (√(v : ℝ)) ^ 2 ≤ (v : ℝ) := (Real.sq_sqrt hv0.le).le
    refine le_trans (le_of_eq ?_) ((ofReal_le_gaussianReal_Icc_neg hv hsv.le hrv).trans
      (measure_mono (Set.Icc_subset_Icc (by linarith) h)))
    congr 1
    rw [min_eq_left ((one_le_div hsv).2 h), hsplit]
    field_simp

end LatticeProb
