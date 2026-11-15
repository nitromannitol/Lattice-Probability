import LatticeProb.MeasureTheory.MeasurableProfileWindowBounds
import LatticeProb.MeasureTheory.ProfileWindowRunEndpoints

/-! # Measurable endpoints of almost-everywhere constant profile runs -/

set_option autoImplicit false

open Set MeasureTheory Filter

namespace LatticeProb

open scoped Classical in
/-- A jointly measurable profile admits a measurable pair of bounds which recovers
any absorbing almost-everywhere constant run containing the given anchor. -/
theorem exists_measurable_profile_run_endpoints
    {Θ : Type*} [MeasurableSpace Θ] (a u b : ℝ)
    (F : Θ × ℝ → ℝ) (hF : Measurable F) :
    ∃ E : Θ → ℝ × ℝ, Measurable E ∧
      ∀ (θ : Θ) (l r c : ℝ), a ≤ l → l < u → u < r → r ≤ b →
        (∀ᵐ t ∂(volume.restrict (Ioo l r)), F (θ, t) = c) →
        (∀ p q : ℝ, Ioo p q ⊆ Ioo a b →
          (Ioo l r ∩ Ioo p q).Nonempty → ∀ d : ℝ,
          (∀ᵐ t ∂(volume.restrict (Ioo p q)), F (θ, t) = d) →
          Ioo p q ⊆ Ioo l r) → E θ = (l, r) := by
  classical
  refine ⟨fun θ => (⨅ pq : ℚ × ℚ,
    if a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧ u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b ∧
      ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))), F (θ, t) = c
    then (pq.1 : ℝ) else b,
    ⨆ pq : ℚ × ℚ,
    if a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧ u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b ∧
      ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))), F (θ, t) = c
    then (pq.2 : ℝ) else a), ?_, ?_⟩
  · exact (measurable_profile_window_bounds a u b F hF).1.prodMk
      (measurable_profile_window_bounds a u b F hF).2
  · intro θ l r c hal hlu hur hrb hrun habsorb
    exact Prod.ext (profile_window_bounds_eq_run_endpoints
      (fun t => F (θ, t)) a u b l r c hal hlu hur hrb hrun habsorb).1
      (profile_window_bounds_eq_run_endpoints
        (fun t => F (θ, t)) a u b l r c hal hlu hur hrb hrun habsorb).2

end LatticeProb
