import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector

/-! # Outer buffers for active selectors -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- If a selector is active on a set and every selected region contains a
fixed ball around its selected point, an outer set containing those regions
also contains the corresponding thickening of the active set. -/
theorem thickening_subset_of_selector_margin
    {X J : Type*} [PseudoMetricSpace X]
    (select : X → Option J) (W : J → Set X) (D T : Set X) (r : ℝ)
    (hactive : ∀ x ∈ D, select x ≠ none)
    (hmargin : ∀ x j, select x = some j → ball x r ⊆ W j)
    (houter : ∀ j, W j ⊆ T) : thickening r D ⊆ T := by
  intro y hy
  obtain ⟨x, hx, hyx⟩ := mem_thickening_iff.mp hy
  cases h : select x with
  | none => exact False.elim (hactive x hx h)
  | some j => exact houter j (hmargin x j h hyx)

end LatticeProb
