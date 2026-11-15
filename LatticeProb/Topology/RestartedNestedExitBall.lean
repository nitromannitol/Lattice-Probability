import LatticeProb.Topology.ScaledNestedExitBall
import LatticeProb.Topology.RestartedNestedExitTrace

/-! # Conditional ball events for restarted nested exits -/

set_option autoImplicit false

open Set Metric MeasureTheory

namespace LatticeProb

/-- Conditional ball-event bounds transfer along an almost-everywhere inclusion. -/
theorem condExp_ball_event_mono_ae
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (m₀ : MeasurableSpace Ω) (S T : Ω → Set E) {a b p : ℝ}
    (hab : a ≤ b) (hST : ∀ᵐ ω ∂μ, S ω ⊆ T ω)
    (hS : MeasurableSet[m] {ω | ∃ x, ball x b ⊆ S ω})
    (hT : MeasurableSet[m] {ω | ∃ x, ball x a ⊆ T ω})
    (hp : ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ x, ball x b ⊆ S ω}).indicator
      (fun _ => (1 : ℝ)) | m₀] ω) :
    ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ x, ball x a ⊆ T ω}).indicator
      (fun _ => (1 : ℝ)) | m₀] ω := by
  have hmono : ∀ᵐ ω ∂μ,
      ({ω | ∃ x, ball x b ⊆ S ω}).indicator (fun _ => (1 : ℝ)) ω ≤
      ({ω | ∃ x, ball x a ⊆ T ω}).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hST] with ω hω
    by_cases hs : ω ∈ {ω | ∃ x, ball x b ⊆ S ω}
    · obtain ⟨x, hx⟩ := hs
      have ht : ω ∈ {ω | ∃ x, ball x a ⊆ T ω} :=
        ⟨x, (ball_subset_ball hab).trans (hx.trans hω)⟩
      simp only [indicator_of_mem (show ω ∈ {ω | ∃ x, ball x b ⊆ S ω} from ⟨x, hx⟩),
        indicator_of_mem ht, le_refl]
    · rw [indicator_of_notMem hs]
      exact indicator_nonneg (fun _ _ => zero_le_one) ω
  have hc := condExp_mono (μ := μ) (m := m₀)
    ((integrable_const (1 : ℝ)).indicator hS)
    ((integrable_const (1 : ℝ)).indicator hT) hmono
  filter_upwards [hp, hc] with ω hω hle
  exact hω.trans hle

/-- A conditional ball-event bound for a restarted intermediate exit trace
transfers to the full nested trace when the paths are continuous and exit the
outer ball in finite time almost surely. -/
theorem condExp_restarted_nested_exit_ball
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (m₀ : MeasurableSpace Ω) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : Ω → E) {r s R a b p : ℝ}
    (hrs : r ≤ s) (hsR : s ≤ R) (hab : a ≤ b)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω))
    (hfin : ∀ᵐ ω ∂μ, openExitTime
      (fun u (_ : Unit) => η ω (t₀ ω + (u : ℝ))) (ball (z ω) R) () ≠ ⊤)
    (hS : MeasurableSet[m] {ω | ∃ x, ball x b ⊆
      η ω '' Icc (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball (z ω) r})
        (sInf {t : ℝ | sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball (z ω) r} ≤ t ∧
          η ω t ∉ ball (z ω) s})})
    (hT : MeasurableSet[m] {ω | ∃ x, ball x a ⊆
      η ω '' Icc (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball (z ω) r})
        (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball (z ω) R})})
    (hp : ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ x, ball x b ⊆
      η ω '' Icc (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball (z ω) r})
        (sInf {t : ℝ | sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball (z ω) r} ≤ t ∧
          η ω t ∉ ball (z ω) s})}).indicator (fun _ => (1 : ℝ)) | m₀] ω) :
    ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ x, ball x a ⊆
      η ω '' Icc (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball (z ω) r})
        (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball (z ω) R})}).indicator
          (fun _ => (1 : ℝ)) | m₀] ω := by
  apply condExp_ball_event_mono_ae m₀ _ _ hab _ hS hT hp
  filter_upwards [hpath, hfin] with ω hω hf
  exact restarted_nested_exit_trace_subset (η ω) (t₀ ω) (z ω) hrs hsR hω hf

end LatticeProb
