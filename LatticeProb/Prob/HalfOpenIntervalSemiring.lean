import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Basic.Real.Basic

/-! Half-open intervals form a semiring of sets. -/

open Set MeasureTheory

namespace LatticeProb

/-- The half-open real intervals, including the empty interval, form a set semiring. -/
theorem isSetSemiring_Ico_real :
    IsSetSemiring {s : Set ℝ | ∃ u v : ℝ, s = Ico u v} := by
  have h := (IsSetSemiring.Ioc (α := ℝᵒᵈ))
  have heq : {s : Set ℝᵒᵈ | ∃ u v : ℝᵒᵈ, u ≤ v ∧ s = Ioc u v} =
      {s : Set ℝ | ∃ u v : ℝ, s = Ico u v} := by
    ext s
    constructor
    · rintro ⟨u, v, huv, rfl⟩
      refine ⟨v, u, ?_⟩
      ext x
      simp only [mem_Ioc]
      exact and_comm
    · rintro ⟨u, v, rfl⟩
      let w : ℝ := max u v
      refine ⟨w, u, ?_, ?_⟩
      · change u ≤ w
        exact le_max_left _ _
      ext x
      change (u ≤ x ∧ x < v) ↔ (x < max u v ∧ u ≤ x)
      constructor
      · rintro ⟨hux, hx⟩
        exact ⟨lt_of_lt_of_le hx (le_max_right _ _), hux⟩
      · rintro ⟨hx, hux⟩
        refine ⟨hux, ?_⟩
        rcases le_total u v with huv | hvu
        · simpa only [max_eq_right huv] using hx
        · have hxu : x < u := by simpa only [max_eq_left hvu] using hx
          exact False.elim ((not_lt_of_ge hux) hxu)
  rw [heq] at h
  exact h

end LatticeProb
