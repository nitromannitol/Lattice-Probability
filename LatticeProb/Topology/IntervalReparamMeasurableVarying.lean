import LatticeProb.Topology.IntervalReparamScale
import LatticeProb.Topology.IntervalReparamZero
import LatticeProb.Prob.NormalizedPrefixCurve

/-! # Measurability of interval distance for varying paths -/

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb.IntervalReparamEDist

/-- The interval distance of measurable continuous paths at measurable finite durations
is measurable, including zero durations. -/
theorem measurable_intervalEDist_of_measurable_finite {X : Type*} [MeasurableSpace X]
    {d : ℕ} (f g : X → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (c e : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hc : Measurable c) (he : Measurable e)
    (hcf : ∀ x, c x ≠ ⊤) (hef : ∀ x, e x ≠ ⊤) :
    Measurable (fun x => intervalEDist (f x) (g x) (c x) (e x)) := by
  classical
  have hzero_c : MeasurableSet {x | c x = 0} := hc (measurableSet_singleton 0)
  have hzero_e : MeasurableSet {x | e x = 0} := he (measurableSet_singleton 0)
  have hstart_f : Measurable (fun x => f x 0) :=
    (ContinuousMap.measurable_eval 0).comp hf
  have hstart_g : Measurable (fun x => g x 0) :=
    (ContinuousMap.measurable_eval 0).comp hg
  have hcurve_c : Measurable (fun x => normalizedPrefixCurve (f x) (c x).toNNReal) :=
    measurable_normalizedPrefixCurve_toNNReal.comp (hf.prodMk hc)
  have hcurve_e : Measurable (fun x => normalizedPrefixCurve (g x) (e x).toNNReal) :=
    measurable_normalizedPrefixCurve_toNNReal.comp (hg.prodMk he)
  have hbranch : Measurable (fun x =>
      if c x = 0 then
        if e x = 0 then edist (f x 0) (g x 0) else ⊤
      else if e x = 0 then ⊤ else
        edist (normalizedPrefixCurve (f x) (c x).toNNReal)
          (normalizedPrefixCurve (g x) (e x).toNNReal)) :=
    Measurable.ite hzero_c (Measurable.ite hzero_e (hstart_f.edist hstart_g) measurable_const)
      (Measurable.ite hzero_e measurable_const (hcurve_c.edist hcurve_e))
  convert hbranch using 1
  funext x
  by_cases hz : c x = 0
  · by_cases hw : e x = 0
    · simp only [hz, hw, ite_true, intervalEDist_zero_zero]
    · simp only [hz, hw, ite_true, ite_false]
      exact intervalEDist_zero_of_pos (f x) (g x) (pos_iff_ne_zero.mpr hw)
  · by_cases hw : e x = 0
    · simp only [hz, hw, ite_true, ite_false]
      exact intervalEDist_of_pos_zero (f x) (g x) (pos_iff_ne_zero.mpr hz)
    · simp only [hz, hw, ite_false]
      have hcp : 0 < (c x).toNNReal := by
        apply ENNReal.coe_pos.mp
        rw [ENNReal.coe_toNNReal (hcf x)]
        exact pos_iff_ne_zero.mpr hz
      have hep : 0 < (e x).toNNReal := by
        apply ENNReal.coe_pos.mp
        rw [ENNReal.coe_toNNReal (hef x)]
        exact pos_iff_ne_zero.mpr hw
      simpa only [ENNReal.coe_toNNReal (hcf x), ENNReal.coe_toNNReal (hef x)] using
        intervalEDist_eq_edist_normalizedPrefixCurve (f x) (g x)
          (c x).toNNReal (e x).toNNReal hcp hep

end LatticeProb.IntervalReparamEDist
