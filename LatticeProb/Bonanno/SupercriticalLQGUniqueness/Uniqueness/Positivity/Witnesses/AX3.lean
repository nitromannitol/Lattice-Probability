/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SLUFieldSupport
import LatticeProb.Bonanno.SLUMetricAPI
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling




 



set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses

open LQGMetric (DistC IsGFFPlusCont addFun)
open SupercriticalLQGUniqueness

 
theorem len_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) : E.len P a b = c * D.len P a b := by
  have h := @LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
    ℂ ℂ
    (@EMetricSpace.toPseudoEMetricSpace ℂ (E.instEMetricSpace))
    (@EMetricSpace.toPseudoEMetricSpace ℂ (D.instEMetricSpace))
    P P c (fun s t => hscale (P s) (P t)) (Icc a b)
  exact h

theorem isCurve_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b) : E.IsCurve P a b := by
  refine ⟨hP.1, ?_⟩
  intro t ht
  have hDt := hP.2 t ht
  have hDlim := tendsto_iff_edist_tendsto_0.mp hDt
  change Filter.Tendsto (fun s => D (P s, P t)) (𝓝[Icc a b] t) (𝓝 0) at hDlim
  apply tendsto_iff_edist_tendsto_0.mpr
  change Filter.Tendsto (fun s => E (P s, P t)) (𝓝[Icc a b] t) (𝓝 0)
  simpa only [hscale, mul_zero] using
    ENNReal.Tendsto.mul (tendsto_const_nhds (x := c)) (Or.inr (by simp))
      hDlim (Or.inr hc)

 
theorem isCurve_iff_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) : E.IsCurve P a b ↔ D.IsCurve P a b := by
  have hInv : ∀ x y : ℂ, D (x, y) = c⁻¹ * E (x, y) := by
    intro x y
    rw [hscale, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hcTop, one_mul]
  constructor
  · exact isCurve_of_dist_scale E D c⁻¹ (ENNReal.inv_ne_top.mpr hc0) hInv P a b
  · exact isCurve_of_dist_scale D E c hcTop hscale P a b

 
theorem acrossDist_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (A : EuclideanAnnulus) : acrossDist E A = c * acrossDist D A := by
  unfold acrossDist
  simp only [hscale, ENNReal.mul_iInf_of_ne hc0 hcTop]

 
theorem aroundDist_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (A : EuclideanAnnulus) : aroundDist E A = c * aroundDist D A := by
  unfold aroundDist
  simp only [isCurve_iff_of_dist_scale D E c hc0 hcTop hscale,
    len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

theorem weylScale_const (ξ t : ℝ) (D : LSCMetric) (hD : D.IsLengthSpace)
    (p : ℂ × ℂ) :
    weylScale ξ (ContinuousMap.const ℂ t) D p =
      ENNReal.ofReal (Real.exp (ξ * t)) * D p :=
  SupercriticalLQGUniqueness.weylScale_const ξ t D hD p

 
end SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses
