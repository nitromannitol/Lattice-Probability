import Mathlib
import LatticeProb.Prob.StopFunctional

/-!
# The minimum of two stopping functionals

If `Ψ₁` and `Ψ₂` are stopping functionals of continuous paths, so is `w ↦ min (Ψ₁ w) (Ψ₂ w)`
(for instance the first exit time of an interval, the minimum of two hitting times).
-/

open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- A stopping functional only increases when evaluated on the path stopped at a time `t` which
is at most the functional on the original path. -/
lemma IsStopFun.le_stopAt {Φ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hΦ : IsStopFun Φ) (w : C(ℝ≥0, ℝ)) (t : ℝ≥0)
    {x : ℝ≥0∞} (hxt : x ≤ t) (hxΦ : x ≤ Φ w) : x ≤ Φ (stopAt (t : ℝ≥0∞) w) := by
  by_cases hΦt : Φ w ≤ t
  · rw [(hΦ w t).1 hΦt]; exact hxΦ
  · rw [not_le] at hΦt
    by_contra hcon
    rw [not_le] at hcon
    exact absurd ((hΦ w t).2 (hcon.le.trans hxt)) (not_le.2 hΦt)

/-- The minimum of two stopping functionals is a stopping functional. -/
theorem IsStopFun.min {Ψ₁ Ψ₂ : C(ℝ≥0, ℝ) → ℝ≥0∞} (h₁ : IsStopFun Ψ₁) (h₂ : IsStopFun Ψ₂) :
    IsStopFun fun w => Min.min (Ψ₁ w) (Ψ₂ w) := by
  have one : ∀ {Φ₁ Φ₂ : C(ℝ≥0, ℝ) → ℝ≥0∞}, IsStopFun Φ₁ → IsStopFun Φ₂ →
      ∀ (w : C(ℝ≥0, ℝ)) (t : ℝ≥0), Φ₁ w ≤ t → Φ₁ w ≤ Φ₂ w →
        Min.min (Φ₁ (stopAt (t : ℝ≥0∞) w)) (Φ₂ (stopAt (t : ℝ≥0∞) w)) = Min.min (Φ₁ w) (Φ₂ w) := by
    intro Φ₁ Φ₂ hΦ₁ hΦ₂ w t ht hle
    rw [min_eq_left hle, (hΦ₁ w t).1 ht]
    exact min_eq_left (hΦ₂.le_stopAt w t ht hle)
  intro w t
  refine ⟨fun h => ?_, fun h => ?_⟩
  · beta_reduce at h ⊢
    rcases le_total (Ψ₁ w) (Ψ₂ w) with h12 | h12
    · exact one h₁ h₂ w t (by rwa [min_eq_left h12] at h) h12
    · rw [min_comm (Ψ₁ (stopAt (t : ℝ≥0∞) w)), min_comm (Ψ₁ w)]
      exact one h₂ h₁ w t (by rwa [min_eq_right h12] at h) h12
  · beta_reduce at h ⊢
    rcases min_le_iff.1 h with h | h
    · exact (min_le_left _ _).trans ((h₁ w t).2 h)
    · exact (min_le_right _ _).trans ((h₂ w t).2 h)

end LatticeProb
