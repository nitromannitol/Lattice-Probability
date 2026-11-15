import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Common neighborhoods for coupled selectors -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- If two points have the same active selector and are within its margin,
then both lie in the selected neighborhood. -/
theorem exists_common_selected_neighborhood
    {X J : Type*} [PseudoMetricSpace X] (f : X → Option J)
    (C : Set X) (G : J → Set X) {r : ℝ} (hr : 0 < r)
    (hactive : ∀ y ∈ C, f y ≠ none)
    (hmargin : ∀ y j, f y = some j → ball y r ⊆ G j)
    {x y : X} (hy : y ∈ C) (heq : f x = f y) (hxy : dist x y < r) :
    ∃ j, f x = some j ∧ f y = some j ∧ x ∈ G j ∧ y ∈ G j := by
  cases hfy : f y with
  | none => exact (hactive y hy hfy).elim
  | some j =>
    refine ⟨j, heq.trans hfy, rfl, ?_, ?_⟩
    · exact hmargin y j hfy (by simpa only [mem_ball] using hxy)
    · exact hmargin y j hfy (mem_ball_self hr)

/-- The measure of failure to share a selected neighborhood is controlled by
selector disagreement or separation, on the active region of the second point. -/
theorem measure_not_common_selected_neighborhood_le
    {X J : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (f : X → Option J) (C : Set X) (G : J → Set X) {r : ℝ} (hr : 0 < r)
    (hactive : ∀ y ∈ C, f y ≠ none)
    (hmargin : ∀ y j, f y = some j → ball y r ⊆ G j)
    (π : Measure (X × X)) :
    π {p | p.2 ∈ C ∧ ¬ ∃ j, f p.1 = some j ∧ f p.2 = some j ∧
        p.1 ∈ G j ∧ p.2 ∈ G j} ≤
      π {p | f p.1 ≠ f p.2 ∨ r ≤ dist p.1 p.2} := by
  apply measure_mono
  intro p hp
  by_contra hn
  have heq : f p.1 = f p.2 := by
    by_contra hne
    exact hn (Or.inl hne)
  have hdist : dist p.1 p.2 < r := by
    by_contra hle
    exact hn (Or.inr (le_of_not_gt hle))
  exact hp.2 (exists_common_selected_neighborhood f C G hr hactive hmargin hp.1 heq hdist)

end LatticeProb
