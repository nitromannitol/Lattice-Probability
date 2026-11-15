import LatticeProb.Topology.RealFirstExitClock
import LatticeProb.Topology.MeasurableSegmentBall
import LatticeProb.Prob.BrownianOpenExitStopping

/-! # Measurable ball containment in finite first-exit traces -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Ball containment in the forward first-exit trace is measurable on finite exits. -/
theorem measurableSet_forward_firstExitTrace_contains_closedBall
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))} {δ : Ω → ℝ}
    (hf : Measurable f) (hδ : Measurable δ)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (t₀ : ℝ) :
    MeasurableSet {ω | openExitTime (fun s (_ : Unit) => f ω (t₀ + (s : ℝ))) U () ≠ ⊤ ∧
      0 ≤ δ ω ∧ ∃ z, closedBall z (δ ω) ⊆
        f ω '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ f ω t ∉ U})} := by
  let τ : Ω → ℝ≥0∞ := fun ω =>
    openExitTime (fun s (_ : Unit) => f ω (t₀ + (s : ℝ))) U ()
  have hτ : Measurable τ := by
    apply measurable_openExitTime (B := fun s ω => f ω (t₀ + (s : ℝ)))
    · intro s
      exact ((ContinuousMap.measurable_eval _).comp hf).stronglyMeasurable
    · intro ω
      exact (f ω).continuous.comp (continuous_const.add NNReal.continuous_coe)
    · exact hU
  have hb : Measurable (fun ω => t₀ + ((τ ω).toNNReal : ℝ)) :=
    measurable_const.add (NNReal.continuous_coe.measurable.comp
      (ENNReal.measurable_toNNReal.comp hτ))
  have hevent := measurableSet_exists_closedBall_subset_segment (a := fun _ => t₀) hf measurable_const hb hδ
  have hfinite : MeasurableSet {ω | τ ω ≠ ⊤} := by
    simpa only [lt_top_iff_ne_top] using (measurableSet_lt hτ (measurable_const : Measurable (fun _ : Ω => (⊤ : ℝ≥0∞))))
  convert hfinite.inter hevent using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff]
  have horder : t₀ ≤ t₀ + ((τ ω).toNNReal : ℝ) :=
    le_add_of_nonneg_right (τ ω).toNNReal.coe_nonneg
  constructor
  · rintro ⟨hfin, hδ0, z, hz⟩
    refine ⟨hfin, horder, hδ0, z, ?_⟩
    rw [sInf_outside_eq_forward_openExitTime (f ω) U t₀ (f ω).continuous hU hfin] at hz
    exact hz
  · rintro ⟨hfin, _, hδ0, z, hz⟩
    refine ⟨hfin, hδ0, z, ?_⟩
    rw [sInf_outside_eq_forward_openExitTime (f ω) U t₀ (f ω).continuous hU hfin]
    exact hz

/-- Ball containment in the backward first-exit trace is measurable on finite exits. -/
theorem measurableSet_backward_firstExitTrace_contains_closedBall
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))} {δ : Ω → ℝ}
    (hf : Measurable f) (hδ : Measurable δ)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (t₀ : ℝ) :
    MeasurableSet {ω | openExitTime (fun s (_ : Unit) => f ω (t₀ - (s : ℝ))) U () ≠ ⊤ ∧
      0 ≤ δ ω ∧ ∃ z, closedBall z (δ ω) ⊆
        f ω '' Icc (sSup {t : ℝ | t ≤ t₀ ∧ f ω t ∉ U}) t₀} := by
  let τ : Ω → ℝ≥0∞ := fun ω =>
    openExitTime (fun s (_ : Unit) => f ω (t₀ - (s : ℝ))) U ()
  have hτ : Measurable τ := by
    apply measurable_openExitTime (B := fun s ω => f ω (t₀ - (s : ℝ)))
    · intro s
      exact ((ContinuousMap.measurable_eval _).comp hf).stronglyMeasurable
    · intro ω
      exact (f ω).continuous.comp (continuous_const.sub NNReal.continuous_coe)
    · exact hU
  have ha : Measurable (fun ω => t₀ - ((τ ω).toNNReal : ℝ)) :=
    measurable_const.sub (NNReal.continuous_coe.measurable.comp
      (ENNReal.measurable_toNNReal.comp hτ))
  have hevent := measurableSet_exists_closedBall_subset_segment (b := fun _ => t₀) hf ha measurable_const hδ
  have hfinite : MeasurableSet {ω | τ ω ≠ ⊤} := by
    simpa only [lt_top_iff_ne_top] using (measurableSet_lt hτ (measurable_const : Measurable (fun _ : Ω => (⊤ : ℝ≥0∞))))
  convert hfinite.inter hevent using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff]
  have horder : t₀ - ((τ ω).toNNReal : ℝ) ≤ t₀ :=
    sub_le_self _ (τ ω).toNNReal.coe_nonneg
  constructor
  · rintro ⟨hfin, hδ0, z, hz⟩
    refine ⟨hfin, horder, hδ0, z, ?_⟩
    rw [sSup_outside_eq_backward_openExitTime (f ω) U t₀ (f ω).continuous hU hfin] at hz
    exact hz
  · rintro ⟨hfin, _, hδ0, z, hz⟩
    refine ⟨hfin, hδ0, z, ?_⟩
    rw [sSup_outside_eq_backward_openExitTime (f ω) U t₀ (f ω).continuous hU hfin]
    exact hz

end LatticeProb
