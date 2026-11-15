import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianCoupling

/-! # Selector conditions for stopped walk and Brownian paths -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne

namespace LatticeProb

/-- A selector active on a closed thickening supplies the stopping hypotheses
for the walk and its shifted Brownian selector on the open thickening. -/
theorem selector_stopping_conditions {d : ℕ} {J : Type*}
    [MeasurableSpace (Option J)] (U : Set (Euc d)) {δ : ℝ} (hδ : 0 < δ)
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (hactive : ∀ i x, x ∈ cthickening δ U → select i x ≠ none) :
    (∀ i x, select i x = none → x ∉ thickening δ U) ∧
    (∀ i x, select i x = none → x ∉ U) ∧
    (∀ i, Measurable (brownianSelectorForWalk select i)) ∧
    (∀ i x, brownianSelectorForWalk select i x = none → x ∉ thickening δ U) := by
  have hn : ∀ i x, select i x = none → x ∉ thickening δ U := by
    intro i x hx hmem
    exact hactive i x (thickening_subset_cthickening δ U hmem) hx
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro i x hx hmem
    exact hn i x hx (self_subset_thickening hδ U hmem)
  · intro i
    exact hs (i - 1)
  · intro i x hx
    exact hn (i - 1) x hx

end LatticeProb
