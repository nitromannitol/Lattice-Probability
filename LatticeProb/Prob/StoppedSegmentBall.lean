import LatticeProb.Prob.BrownianPathPaste
import LatticeProb.Topology.ObservedSegmentBall

/-! # Ball containment between stopping times -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace LatticeProb

/-- For a continuous Euclidean-valued process, ball containment in the trace between two
ordered finite stopping times is measurable for the sigma algebra at the later time. -/
theorem measurableSet_ball_subset_stopped_segment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (natFiltration X hm) fun ω => (σ ω : ℝ≥0∞))
    (hτ : IsStoppingTime (natFiltration X hm) fun ω => (τ ω : ℝ≥0∞))
    (hστ : ∀ ω, σ ω ≤ τ ω) {r : ℝ} (hr : 0 < r) :
    MeasurableSet[hτ.measurableSpace]
      {ω | ∃ z, ball z r ⊆ (fun t : ℝ => X t.toNNReal ω) ''
        Icc (σ ω : ℝ) (τ ω : ℝ)} := by
  have hσm : Measurable[hτ.measurableSpace] σ := by
    have h := ENNReal.measurable_toNNReal.comp hσ.measurable
    have hh : Measurable[hσ.measurableSpace] σ := by
      simpa only [Function.comp_def, ENNReal.toNNReal_coe] using h
    exact hh.mono (hσ.measurableSpace_mono hτ fun ω => ENNReal.coe_le_coe.mpr (hστ ω)) le_rfl
  have hτm : Measurable[hτ.measurableSpace] τ := by
    have h := ENNReal.measurable_toNNReal.comp hτ.measurable
    simpa only [Function.comp_def, ENNReal.toNNReal_coe] using h
  let f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d)) := fun ω =>
    ⟨fun t => stopPath X hc τ ω t.toNNReal,
      (stopPath X hc τ ω).continuous.comp continuous_real_toNNReal⟩
  have hs := measurable_stopPath hm hc hτ
  have hf : Measurable[hτ.measurableSpace] f := by
    let _ : MeasurableSpace Ω := hτ.measurableSpace
    apply ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2
    intro t
    exact (ContinuousMap.measurable_eval t.toNNReal).comp hs
  let _ : MeasurableSpace Ω := hτ.measurableSpace
  apply measurableSet_exists_ball_subset_observed_segment hf
    (NNReal.continuous_coe.measurable.comp hσm) (NNReal.continuous_coe.measurable.comp hτm)
    (fun ω => by exact_mod_cast hστ ω) hr
  intro ω t ht
  change X (min t.toNNReal (τ ω)) ω = X t.toNNReal ω
  rw [min_eq_left]
  exact Real.toNNReal_le_iff_le_coe.mpr ht.2

end LatticeProb
