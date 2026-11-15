import LatticeProb.Topology.MeasurableCurveComponentInterval
import LatticeProb.Prob.AnalyticUniversalMeasurable
import LatticeProb.LQG.MatingOfTreesCouplingLaw

/-! # Interval witnesses for curve components -/

set_option autoImplicit false

open Set MeasureTheory Topology

namespace LatticeProb

/-- The bounded interval-image relation for the selected component is Borel. -/
theorem measurableSet_bounded_component_interval (s t : ℝ) :
    MeasurableSet {p : (C(ℝ, ℂ) × ℂ) × (ℝ × ℝ) |
      s ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.2.2 ≤ t ∧
      closure (connectedComponentIn (interior (p.1.1 '' Icc s t)) p.1.2) =
        p.1.1 '' Icc p.2.1 p.2.2} := by
  have h := measurableSet_component_closure_eq_image_Icc
    (fun p : (C(ℝ, ℂ) × ℂ) × (ℝ × ℝ) => p.1.1) (fun p => p.1.2)
    (fun p => p.2.1) (fun p => p.2.2) (K := Icc s t) isCompact_Icc
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  have hs : MeasurableSet {p : (C(ℝ, ℂ) × ℂ) × (ℝ × ℝ) | s ≤ p.2.1} :=
    measurableSet_le measurable_const (measurable_fst.comp measurable_snd)
  have ht : MeasurableSet {p : (C(ℝ, ℂ) × ℂ) × (ℝ × ℝ) | p.2.2 ≤ t} :=
    measurableSet_le (measurable_snd.comp measurable_snd) measurable_const
  convert hs.inter (ht.inter h) using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff]
  tauto

/-- The existence of bounded interval-image witnesses is an analytic property
of the curve and its selected point. -/
theorem analyticSet_exists_bounded_component_interval (s t : ℝ) :
    AnalyticSet {p : C(ℝ, ℂ) × ℂ | ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (p.1 '' Icc s t)) p.2) =
        p.1 '' Icc a b} := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  have heq : {p : C(ℝ, ℂ) × ℂ | ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (p.1 '' Icc s t)) p.2) =
        p.1 '' Icc a b} =
      Prod.fst '' {p : (C(ℝ, ℂ) × ℂ) × (ℝ × ℝ) |
        s ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.2.2 ≤ t ∧
        closure (connectedComponentIn (interior (p.1.1 '' Icc s t)) p.1.2) =
          p.1.1 '' Icc p.2.1 p.2.2} := by
    ext p
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨(p, (a, b)), h, rfl⟩
    · rintro ⟨⟨q, a, b⟩, h, rfl⟩
      exact ⟨a, b, h⟩
  rw [heq]
  exact (measurableSet_bounded_component_interval s t).analyticSet.image_of_continuous
    continuous_fst

/-- The bounded interval-witness event is null-measurable for any finite law. -/
theorem nullMeasurableSet_exists_bounded_component_interval (s t : ℝ)
    (μ : Measure (C(ℝ, ℂ) × ℂ)) [IsFiniteMeasure μ] :
    NullMeasurableSet {p : C(ℝ, ℂ) × ℂ | ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (p.1 '' Icc s t)) p.2) =
        p.1 '' Icc a b} μ := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  exact AnalyticSet.nullMeasurableSet μ (analyticSet_exists_bounded_component_interval s t)

/-- Equal laws transfer almost-sure existence of bounded component interval
witnesses, without selecting the witnesses measurably. -/
theorem ae_exists_bounded_component_interval_of_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsFiniteMeasure P] (P' : Measure Ω')
    (V : Ω → C(ℝ, ℂ) × ℂ) (V' : Ω' → C(ℝ, ℂ) × ℂ)
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    (s t : ℝ) (h : ∀ᵐ ω ∂P, ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior ((V ω).1 '' Icc s t)) (V ω).2) =
        (V ω).1 '' Icc a b) :
    ∀ᵐ ω ∂P', ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior ((V' ω).1 '' Icc s t)) (V' ω).2) =
        (V' ω).1 '' Icc a b := by
  have : IsFiniteMeasure (P.map V) := Measure.isFiniteMeasure_map P V
  exact ae_comp_of_map_eq_of_nullMeasurableSet hV hV' hlaw
    (nullMeasurableSet_exists_bounded_component_interval s t (P.map V)) h

end LatticeProb
