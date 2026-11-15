import LatticeProb.Analysis.LocalMinCountable

/-! # Grid phases and local-minimum levels -/

set_option autoImplicit false

open MeasureTheory Set Filter

namespace LatticeProb

/-- If local-minimum times are countable and their level sets are null, then
almost every phase avoids all local-minimum values at all integer grid points. -/
theorem measure_grid_localMin_levels_eq_zero (f : ℝ → ℝ) (ε : ℝ)
    (hc : {t | IsLocalMin f t}.Countable)
    (hn : ∀ t, IsLocalMin f t → volume {s | f s = f t} = 0) :
    volume {c : ℝ | ∃ (k : ℤ) (t : ℝ), IsLocalMin f t ∧
      f (c + ε * k) = f t} = 0 := by
  let A : Set ℝ := f '' {t | IsLocalMin f t}
  have hA : A.Countable := hc.image f
  have hnull : volume (f ⁻¹' A) = 0 := by
    apply (measure_preimage_eq_zero_iff_of_countable hA).2
    intro a ha
    obtain ⟨t, ht, rfl⟩ := ha
    exact hn t ht
  have hshift (k : ℤ) : volume {c : ℝ | f (c + ε * k) ∈ A} = 0 := by
    change volume ((fun c : ℝ => c + ε * k) ⁻¹' (f ⁻¹' A)) = 0
    rw [measure_preimage_add_right]
    exact hnull
  apply measure_mono_null _ (measure_iUnion_null hshift)
  intro c hc'
  obtain ⟨k, t, ht, heq⟩ := hc'
  refine mem_iUnion.mpr ⟨k, ?_⟩
  exact ⟨t, ht, heq.symm⟩

end LatticeProb
