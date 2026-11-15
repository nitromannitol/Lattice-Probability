import LatticeProb.MeasureTheory.MeasurableEssentialConstancy
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Measurable bounds from almost-everywhere constant windows -/

set_option autoImplicit false

open MeasureTheory Filter Set

namespace LatticeProb

open scoped Classical in
/-- Rational windows of essential constancy give measurable lower and upper bounds.
When no window qualifies, the bounds are respectively `b` and `a`. -/
theorem measurable_profile_window_bounds
    {Θ : Type*} [MeasurableSpace Θ] (a u b : ℝ)
    (F : Θ × ℝ → ℝ) (hF : Measurable F) :
    Measurable (fun θ : Θ => ⨅ pq : ℚ × ℚ,
      if a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧ u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b ∧
        ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))), F (θ, t) = c
      then (pq.1 : ℝ) else b) ∧
    Measurable (fun θ : Θ => ⨆ pq : ℚ × ℚ,
      if a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧ u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b ∧
        ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))), F (θ, t) = c
      then (pq.2 : ℝ) else a) := by
  classical
  have hw (pq : ℚ × ℚ) : MeasurableSet {θ : Θ |
      a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧ u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b ∧
        ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))), F (θ, t) = c} := by
    by_cases h : a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧ u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b
    · have hne : volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ)) ≠ 0 := by
        intro hz
        have hz' := Measure.restrict_eq_zero.mp hz
        rw [Real.volume_Ioo] at hz'
        exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr (lt_trans h.2.1 h.2.2.1))).ne' hz'
      simpa only [h, true_and] using
        measurableSet_ae_constant_section (volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))) hne F hF
    · have he : {θ : Θ | a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧
          u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b ∧
          ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))), F (θ, t) = c} = ∅ := by
        ext θ
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hθ
        exact h ⟨hθ.1, hθ.2.1, hθ.2.2.1, hθ.2.2.2.1⟩
      rw [he]
      exact MeasurableSet.empty
  constructor
  · exact Measurable.iInf fun pq => measurable_const.ite (hw pq) measurable_const
  · exact Measurable.iSup fun pq => measurable_const.ite (hw pq) measurable_const

end LatticeProb
