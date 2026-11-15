import LatticeProb.Prob.StoppedSegmentBall

/-! # Localization of stopped segment events -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped NNReal ENNReal

namespace LatticeProb

/-- A finite-exit segment event has a representative measurable at the later
stopping time, even when that time may be infinite on exceptional paths. -/
theorem exists_measurableSet_ball_subset_segment_ae
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    {σ τ : Ω → ℝ≥0∞}
    (hσ : IsStoppingTime (natFiltration X hm) σ)
    (hτ : IsStoppingTime (natFiltration X hm) τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) (hfin : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {a : ℝ} (ha : 0 < a) :
    ∃ s : Set Ω, MeasurableSet[hτ.measurableSpace] s ∧
      ∀ᵐ ω ∂μ, (ω ∈ s ↔ ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) ''
        Icc ((σ ω).toNNReal : ℝ) ((τ ω).toNNReal : ℝ)) := by
  let σn : ℕ → Ω → ℝ≥0 := fun n ω => (min (σ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
  let τn : ℕ → Ω → ℝ≥0 := fun n ω => (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
  have hσn : ∀ n, IsStoppingTime (natFiltration X hm) (fun ω => (σn n ω : ℝ≥0∞)) := by
    intro n
    have he : (fun ω => (σn n ω : ℝ≥0∞)) =
        (fun ω => min (σ ω) ((n : ℝ≥0) : ℝ≥0∞)) := by
      funext ω
      exact ENNReal.coe_toNNReal ((min_le_right _ _).trans_lt ENNReal.coe_lt_top).ne
    rw [he]
    exact hσ.min_const (n : ℝ≥0)
  have hτn : ∀ n, IsStoppingTime (natFiltration X hm) (fun ω => (τn n ω : ℝ≥0∞)) := by
    intro n
    have he : (fun ω => (τn n ω : ℝ≥0∞)) =
        (fun ω => min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)) := by
      funext ω
      exact ENNReal.coe_toNNReal ((min_le_right _ _).trans_lt ENNReal.coe_lt_top).ne
    rw [he]
    exact hτ.min_const (n : ℝ≥0)
  have hord : ∀ n ω, σn n ω ≤ τn n ω := by
    intro n ω
    apply (ENNReal.toNNReal_le_toNNReal
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))).2
    exact min_le_min_right _ (hστ ω)
  let S : ℕ → Set Ω := fun n => {ω | τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)} ∩
    {ω | ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) ''
      Icc (σn n ω : ℝ) (τn n ω : ℝ)}
  have hS : ∀ n, MeasurableSet[hτ.measurableSpace] (S n) := by
    intro n
    have hbound : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)} :=
      hτ.measurableSet_le' (n : ℝ≥0)
    have hevent := measurableSet_ball_subset_stopped_segment hm hc (hσn n) (hτn n) (hord n) ha
    have hsub : (hτn n).measurableSpace ≤ hτ.measurableSpace :=
      IsStoppingTime.measurableSpace_mono (hτn n) hτ (fun ω => by
        simp only [τn, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
        exact min_le_left _ _)
    exact hbound.inter (hsub _ hevent)
  refine ⟨⋃ n, S n, MeasurableSet.iUnion hS, ?_⟩
  filter_upwards [hfin] with ω hω
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hω
  have hτle : τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞) := le_of_lt hn
  have hσle : σ ω ≤ ((n : ℝ≥0) : ℝ≥0∞) := (hστ ω).trans hτle
  have heqσ : σn n ω = (σ ω).toNNReal := by simp only [σn, min_eq_left hσle]
  have heqτ : τn n ω = (τ ω).toNNReal := by simp only [τn, min_eq_left hτle]
  constructor
  · intro hh
    obtain ⟨k, hk, he⟩ := mem_iUnion.mp hh
    change τ ω ≤ ((k : ℝ≥0) : ℝ≥0∞) at hk
    have hσk : σ ω ≤ ((k : ℝ≥0) : ℝ≥0∞) := (hστ ω).trans hk
    change ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc (σn k ω : ℝ) (τn k ω : ℝ) at he
    simpa only [σn, τn, min_eq_left hσk, min_eq_left hk] using he
  · intro hh
    apply mem_iUnion.mpr
    refine ⟨n, hτle, ?_⟩
    change ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc (σn n ω : ℝ) (τn n ω : ℝ)
    simpa only [heqσ, heqτ] using hh

end LatticeProb
