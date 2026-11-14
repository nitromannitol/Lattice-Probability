import LatticeProb.Topology.IntervalReparamScale
import LatticeProb.Topology.IntervalReparamZero
import LatticeProb.Prob.NormalizedPrefixCurve

/-! # Measurability of finite interval reparametrization distance -/

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb.IntervalReparamEDist

/-- For continuous paths, the interval distance at measurable finite durations is measurable. -/
theorem measurable_intervalEDist_of_finite {X : Type*} [MeasurableSpace X] {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (c e : X → ℝ≥0∞)
    (hc : Measurable c) (he : Measurable e)
    (hcf : ∀ x, c x ≠ ⊤) (hef : ∀ x, e x ≠ ⊤) :
    Measurable (fun x => intervalEDist f g (c x) (e x)) := by
  classical
  have hzero_c : MeasurableSet {x | c x = 0} :=
    hc (measurableSet_singleton 0)
  have hzero_e : MeasurableSet {x | e x = 0} :=
    he (measurableSet_singleton 0)
  have hcurve_c : Measurable (fun x => normalizedPrefixCurve f (c x).toNNReal) :=
    measurable_normalizedPrefixCurve_toNNReal.comp (measurable_const.prodMk hc)
  have hcurve_e : Measurable (fun x => normalizedPrefixCurve g (e x).toNNReal) :=
    measurable_normalizedPrefixCurve_toNNReal.comp (measurable_const.prodMk he)
  have hbranch : Measurable (fun x =>
      if c x = 0 then
        if e x = 0 then edist (f 0) (g 0) else ⊤
      else if e x = 0 then ⊤ else
        edist (normalizedPrefixCurve f (c x).toNNReal)
          (normalizedPrefixCurve g (e x).toNNReal)) :=
    Measurable.ite hzero_c (Measurable.ite hzero_e measurable_const measurable_const)
      (Measurable.ite hzero_e measurable_const (hcurve_c.edist hcurve_e))
  convert hbranch using 1
  funext x
  by_cases hz : c x = 0
  · by_cases hw : e x = 0
    · simp only [hz, hw, ite_true, intervalEDist_zero_zero]
    · simp only [hz, hw, ite_true, ite_false]
      exact intervalEDist_zero_of_pos f g (pos_iff_ne_zero.mpr hw)
  · by_cases hw : e x = 0
    · simp only [hz, hw, ite_true, ite_false]
      exact intervalEDist_of_pos_zero f g (pos_iff_ne_zero.mpr hz)
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
        intervalEDist_eq_edist_normalizedPrefixCurve f g (c x).toNNReal (e x).toNNReal hcp hep

end LatticeProb.IntervalReparamEDist
