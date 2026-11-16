import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

/-! # Excision of parameter loops -/

set_option autoImplicit false

namespace LatticeProb

/-- If the endpoints of every gap of `K` have the same image, excising an
open interval whose endpoints have the same image preserves that property. -/
theorem equal_of_gap_after_loop_excision {Y : Type*} (f : ℝ → Y) (K : Set ℝ)
    {s t : ℝ} (hs : s ∈ K) (ht : t ∈ K) (heq : f s = f t)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v) :
    ∀ u ∈ K \ Set.Ioo s t, ∀ v ∈ K \ Set.Ioo s t, u < v →
      (∀ w ∈ K \ Set.Ioo s t, ¬ (u < w ∧ w < v)) → f u = f v := by
  intro u hu v hv huv hbetween
  have hs' : s ∈ K \ Set.Ioo s t := ⟨hs, by simp⟩
  have ht' : t ∈ K \ Set.Ioo s t := ⟨ht, by simp⟩
  by_cases h : ∃ w ∈ K, u < w ∧ w < v
  · obtain ⟨w, hw, huw, hwv⟩ := h
    have hwcut : s < w ∧ w < t := by
      by_contra hn
      exact hbetween w ⟨hw, hn⟩ ⟨huw, hwv⟩
    have hsn := hbetween s hs'
    have htn := hbetween t ht'
    have huout := hu.2
    have hvout := hv.2
    simp only [Set.mem_Ioo, not_and_or, not_lt] at huout hvout hsn htn
    have hus : u = s := by rcases huout with h | h <;> rcases hsn with h₁ | h₁ <;> linarith
    have hvt : v = t := by rcases hvout with h | h <;> rcases htn with h₁ | h₁ <;> linarith
    simpa only [hus, hvt] using heq
  · exact hgap u hu.1 v hv.1 huv (by
      intro w hw hwbetween
      exact h ⟨w, hw, hwbetween⟩)

end LatticeProb
