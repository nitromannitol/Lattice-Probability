import LatticeProb.Topology.UnboundedRayProjectionContinuity
import LatticeProb.Topology.UnboundedRayCurveSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Continuity of the projection to unbounded curve classes -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Filter MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand UnboundedRayLocalDistance

variable {d : ℕ}

/-- The local interval distance tends to zero under locally uniform convergence. -/
theorem tendsto_localEDist {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {F : α → UnboundedRay d} {f : UnboundedRay d} (hF : Tendsto F l (𝓝 f)) :
    Tendsto (fun i => localEDist (F i) f) l (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (1 : ℝ))) (l := l)
    (F := fun i r => ENNReal.ofReal (Real.exp (-r)) *
      min 1 (IntervalReparamEDist.intervalEDist (F i).1 f.1
        (ballClock (F i).1 r) (ballClock f.1 r)))
    (f := fun _ => 0) (fun r => ENNReal.ofReal (Real.exp (-r)))
  have hm : ∀ i, Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r)) *
      min 1 (IntervalReparamEDist.intervalEDist (F i).1 f.1
        (ballClock (F i).1 r) (ballClock f.1 r))) := by
    intro i
    have hp : Measurable (fun r : ℝ => ((F i, f), r)) :=
      measurable_const.prodMk measurable_id
    exact (measurable_weighted_intervalEDist (d := d)).comp hp
  have hbound : ∀ i, ∀ᵐ r ∂volume.restrict (Ioi (1 : ℝ)),
      ENNReal.ofReal (Real.exp (-r)) *
        min 1 (IntervalReparamEDist.intervalEDist (F i).1 f.1
          (ballClock (F i).1 r) (ballClock f.1 r)) ≤ ENNReal.ofReal (Real.exp (-r)) :=
    fun i => ae_of_all _ fun r => mul_le_of_le_one_right' (min_le_left _ _)
  have hfin : (∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-r))) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 1)
      (ae_of_all _ fun r => (Real.exp_pos (-r)).le), integral_exp_neg_Ioi]
    exact ENNReal.ofReal_ne_top
  have hlim : ∀ᵐ r ∂volume.restrict (Ioi (1 : ℝ)),
      Tendsto (fun i => ENNReal.ofReal (Real.exp (-r)) *
        min 1 (IntervalReparamEDist.intervalEDist (F i).1 f.1
          (ballClock (F i).1 r) (ballClock f.1 r))) l (𝓝 0) := by
    filter_upwards [UnboundedRayIntervalIntegrand.ae_tendsto_intervalEDist hF] with r hr
    have ht := (tendsto_const_nhds : Tendsto (fun _ : α => (1 : ℝ≥0∞)) l (𝓝 1)).min hr
    have hc := (ENNReal.continuous_const_mul (a := ENNReal.ofReal (Real.exp (-r)))
      ENNReal.ofReal_ne_top).tendsto 0 |>.comp (by simpa using ht)
    rw [mul_zero] at hc
    exact hc
  have hres := h (Eventually.of_forall hm) (Eventually.of_forall hbound) hfin hlim
  rw [lintegral_zero] at hres
  exact hres

end LatticeProb.UnboundedRayCurveSpace
