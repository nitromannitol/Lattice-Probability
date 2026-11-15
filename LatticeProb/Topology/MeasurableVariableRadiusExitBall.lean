import LatticeProb.Topology.UnboundedRayIntervalIntegrand
import LatticeProb.Topology.MeasurableSegmentBall
import LatticeProb.Topology.RealFirstExitClock

/-! # Measurable ball containment in variable-radius exit traces -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- The forward exit time from a ball is measurable jointly in the path and radius. -/
theorem measurable_forward_variableBallExitTime
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))} {r : Ω → ℝ}
    (hf : Measurable f) (hr : Measurable r) :
    Measurable (fun ω => openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ)))
      (ball 0 (r ω)) ()) := by
  simp only [zero_add]
  let ray : Ω → UnboundedRayIntervalIntegrand.Path d := fun ω =>
    (f ω).comp ⟨fun t : ℝ≥0 => (t : ℝ), NNReal.continuous_coe⟩
  have hray : Measurable ray :=
    (ContinuousMap.continuous_precomp
      (⟨fun t : ℝ≥0 => (t : ℝ), NNReal.continuous_coe⟩ : C(ℝ≥0, ℝ))).measurable.comp hf
  have hm := UnboundedRayIntervalIntegrand.measurable_ballClock.comp (hray.prodMk hr)
  simpa only [UnboundedRayIntervalIntegrand.ballClock, openExitTime, ray, ContinuousMap.coe_comp,
    Function.comp_def, ContinuousMap.coe_mk, zero_add] using hm

/-- For a measurable continuous path and measurable radii, containment of a closed ball
in the finite forward exit trace from the ball centered at zero is measurable. -/
theorem measurableSet_forward_variableBallExitTrace_contains_closedBall
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))} {r δ : Ω → ℝ}
    (hf : Measurable f) (hr : Measurable r) (hδ : Measurable δ) :
    MeasurableSet {ω | openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ)))
        (ball 0 (r ω)) () ≠ ⊤ ∧
      0 ≤ δ ω ∧ ∃ z, closedBall z (δ ω) ⊆
        f ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 (r ω)})} := by
  let τ : Ω → ℝ≥0∞ := fun ω => openExitTime
    (fun s (_ : Unit) => f ω (0 + (s : ℝ))) (ball 0 (r ω)) ()
  have hτ : Measurable τ := measurable_forward_variableBallExitTime hf hr
  have hb : Measurable (fun ω => ((τ ω).toNNReal : ℝ)) :=
    NNReal.continuous_coe.measurable.comp (ENNReal.measurable_toNNReal.comp hτ)
  have hevent := measurableSet_exists_closedBall_subset_segment (a := fun _ => 0)
    hf measurable_const hb hδ
  have hfinite : MeasurableSet {ω | τ ω ≠ ⊤} := by
    simpa only [lt_top_iff_ne_top] using
      (measurableSet_lt hτ (measurable_const : Measurable (fun _ : Ω => (⊤ : ℝ≥0∞))))
  convert hfinite.inter hevent using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨hfin, hδ0, z, hz⟩
    refine ⟨hfin, (τ ω).toNNReal.coe_nonneg, hδ0, z, ?_⟩
    rw [sInf_outside_eq_forward_openExitTime (f ω) (ball 0 (r ω)) 0
      (f ω).continuous isOpen_ball hfin] at hz
    simpa only [zero_add, τ] using hz
  · rintro ⟨hfin, _, hδ0, z, hz⟩
    refine ⟨hfin, hδ0, z, ?_⟩
    rw [sInf_outside_eq_forward_openExitTime (f ω) (ball 0 (r ω)) 0
      (f ω).continuous isOpen_ball hfin]
    simpa only [zero_add, τ] using hz

end LatticeProb
