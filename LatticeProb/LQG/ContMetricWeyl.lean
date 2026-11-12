import LatticeProb.LQG.ContMetricLength
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling

/-!
# Weyl scaling of a continuous metric

For a continuous metric `d` on `ℂ` (`LQGMetric.ContMetric`) and `D u v = d (u, v)`, a curve is parametrized by
`D`-length on `[0, T]` exactly when it is a unit-speed curve in `(ℂ, d)` on `[0, T]` (the identity `ℂ → (ℂ, d)` being a
homeomorphism). Hence the Weyl scaling `e^{ξ f} · D` of `LatticeProb.LQG.weylScaling` (Gwynne-Miller, arXiv:1905.00383,
(1.8)) is the Weyl scaling `LQGMetric.weylScale ξ f d` of the continuous metric, for every continuous `f`.

## Main statements

* `LatticeProb.LQG.isLengthParametrized_contMetric_iff`
* `LatticeProb.LQG.weylScaling_contMetric`
-/

open Set
open scoped ENNReal

namespace LatticeProb.LQG

variable (d : LQGMetric.ContMetric)

/-- A curve is parametrized by `D`-length for `D u v = d (u, v)` iff it is a continuous unit-speed curve in
`(ℂ, d)`. -/
theorem isLengthParametrized_contMetric_iff (p : ℝ → ℂ) (T : ℝ) :
    IsLengthParametrized (fun u v => d.1 (u, v)) p T ↔
      0 ≤ T ∧ ContinuousOn (d.pt ∘ p) (Icc 0 T) ∧ HasUnitSpeedOn (d.pt ∘ p) (Icc 0 T) := by
  have hc : ContinuousOn (d.pt ∘ p) (Icc 0 T) ↔ ContinuousOn p (Icc 0 T) :=
    d.ptHomeomorph.comp_continuousOn_iff p (Icc 0 T)
  rw [IsLengthParametrized, LQGMetric.MetricGeometry.hasUnitSpeedOn_Icc_iff, hc]
  simp only [curveLength_contMetric]

/-- The Weyl scaling of `D u v = d (u, v)` by a continuous function is the Weyl scaling of the continuous metric `d`. -/
theorem weylScaling_contMetric (ξ : ℝ) (f : C(ℂ, ℝ)) (u v : ℂ) :
    weylScaling (fun u v => d.1 (u, v)) ξ f u v = LQGMetric.weylScale ξ f d u v := by
  simp only [weylScaling, LQGMetric.weylScale, isLengthParametrized_contMetric_iff, iInf_and]

end LatticeProb.LQG
