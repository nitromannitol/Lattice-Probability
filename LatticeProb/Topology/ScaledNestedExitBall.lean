import LatticeProb.Topology.SpacedNestedExitTrial

/-! # Scaled ball events in nested exit trials -/

set_option autoImplicit false

open Set Metric MeasureTheory

namespace LatticeProb

/-- Half of the width of an equally spaced annulus, normalized by its inner
radius, is strictly between zero and one. -/
theorem half_spaced_width_ratio (k : ℕ) {C ε R : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hR : 0 < R) :
    let d := C * ε * R
    let r := ((k + 1 : ℕ) : ℝ) * d
    0 < d / (2 * r) ∧ d / (2 * r) < 1 ∧
      (d / (2 * r)) * r = d / 2 := by
  dsimp
  have hd : 0 < C * ε * R := mul_pos (mul_pos hC hε) hR
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : k + 1 ≠ 0)
  have hr : 0 < ((k + 1 : ℕ) : ℝ) * (C * ε * R) := mul_pos (by positivity) hd
  constructor
  · positivity
  constructor
  · apply (div_lt_one (by positivity)).2
    nlinarith
  · field_simp

/-- A lower bound for the conditional probability of a larger ball in a
smaller set transfers to a smaller ball in the larger set. -/
theorem condExp_ball_event_mono
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (m₀ : MeasurableSpace Ω) (S T : Ω → Set E) {a b p : ℝ}
    (hab : a ≤ b) (hST : ∀ ω, S ω ⊆ T ω)
    (hS : MeasurableSet[m] {ω | ∃ x, ball x b ⊆ S ω})
    (hT : MeasurableSet[m] {ω | ∃ x, ball x a ⊆ T ω})
    (hp : ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ x, ball x b ⊆ S ω}).indicator
      (fun _ => (1 : ℝ)) | m₀] ω) :
    ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ x, ball x a ⊆ T ω}).indicator
      (fun _ => (1 : ℝ)) | m₀] ω := by
  have hsub : {ω | ∃ x, ball x b ⊆ S ω} ⊆ {ω | ∃ x, ball x a ⊆ T ω} := by
    intro ω hω
    obtain ⟨x, hx⟩ := hω
    exact ⟨x, (ball_subset_ball hab).trans (hx.trans (hST ω))⟩
  have hm := condExp_mono (μ := μ) (m := m₀)
    ((integrable_const (1 : ℝ)).indicator hS)
    ((integrable_const (1 : ℝ)).indicator hT)
    (Filter.Eventually.of_forall (Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le_one)))
  filter_upwards [hp, hm] with ω hω hmono
  exact hω.trans hmono

/-- A half-width ball has the target radius when the scaling constant is
large enough. -/
theorem target_radius_le_half_width {δ C ε R : ℝ}
    (hε : 0 ≤ ε) (hR : 0 ≤ R) (hδC : 2 ≤ δ * C) :
    ε * R ≤ δ * (C * ε * R) / 2 := by
  have h := mul_nonneg (sub_nonneg.mpr hδC) (mul_nonneg hε hR)
  nlinarith

end LatticeProb
