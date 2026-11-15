import LatticeProb.Analysis.LocalMinCountable

/-! # Equal values at grid points -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- If the zero set of each nonzero grid-lag increment is null, then almost every
phase gives distinct values at distinct grid points. -/
theorem measure_grid_value_collisions_eq_zero (f : ℝ → ℝ) (ε : ℝ)
    (hn : ∀ n : ℤ, n ≠ 0 → volume {t : ℝ | f t = f (t + ε * n)} = 0) :
    volume {c : ℝ | ∃ k l : ℤ, k ≠ l ∧ f (c + ε * k) = f (c + ε * l)} = 0 := by
  have hshift (k l : ℤ) :
      volume {c : ℝ | k ≠ l ∧ f (c + ε * k) = f (c + ε * l)} = 0 := by
    by_cases hkl : k = l
    · simp only [hkl, ne_eq, not_true_eq_false, false_and, ofPred_false, measure_empty]
    · have hdiff : l - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hkl)
      have hnull := hn (l - k) hdiff
      have htranslate : volume {c : ℝ |
          f (c + ε * k) = f ((c + ε * k) + ε * (l - k))} = 0 := by
        change volume ((fun c : ℝ => c + ε * k) ⁻¹'
          {t : ℝ | f t = f (t + ε * (l - k))}) = 0
        rw [measure_preimage_add_right]
        simpa only [Int.cast_sub] using hnull
      apply measure_mono_null _ htranslate
      intro c hc
      have heq : (c + ε * k) + ε * ((l : ℝ) - (k : ℝ)) = c + ε * l := by
        ring
      change f (c + ε * k) = f ((c + ε * k) + ε * ((l : ℝ) - (k : ℝ)))
      rw [heq]
      exact hc.2
  apply measure_mono_null _ (measure_iUnion_null fun k : ℤ =>
    measure_iUnion_null fun l : ℤ => hshift k l)
  intro c hc
  obtain ⟨k, l, hne, heq⟩ := hc
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨l, hne, heq⟩⟩

end LatticeProb
