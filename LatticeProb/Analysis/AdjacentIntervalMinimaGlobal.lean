import LatticeProb.Analysis.AdjacentIntervalMinimaCountable

/-! # Countability of matching adjacent interval minima -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- For a continuous function with distinct values at distinct local minima,
matching adjacent interval minima occur at only countably many starting points. -/
theorem countable_adjacent_interval_minima (f : ℝ → ℝ) (hf : Continuous f)
    (δ D : ℝ) (hδ : 0 < δ) (hδD : δ < D)
    (hdist : ∀ x y, x ≠ y → IsLocalMin f x → IsLocalMin f y → f x ≠ f y) :
    {t : ℝ | sInf (f '' Icc t (t + δ)) = sInf (f '' Icc (t + δ) (t + D))}.Countable := by
  let S : Set ℝ := {t : ℝ | sInf (f '' Icc t (t + δ)) =
    sInf (f '' Icc (t + δ) (t + D))}
  let h : ℝ := min δ (D - δ)
  have hh : 0 < h := lt_min hδ (sub_pos.mpr hδD)
  have hpieces : ∀ q : ℚ, (S ∩ Ioo (q : ℝ) ((q : ℝ) + h)).Countable := by
    intro q
    apply countable_adjacent_interval_minima_on_slab f hf δ D hδ hδD _ hdist
    · intro t ht u hu htu
      have h1 : h ≤ δ := min_le_left _ _
      have h2 : h ≤ D - δ := min_le_right _ _
      constructor <;> linarith [ht.2.1, ht.2.2, hu.2.1, hu.2.2]
    · intro t ht
      exact ht.1
  apply (countable_iUnion hpieces).mono
  intro t ht
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show t - h < t by linarith)
  exact mem_iUnion.mpr ⟨q, ht, hq₂, by linarith⟩

end LatticeProb
