import LatticeProb.Walk.SelectorBallOuterContainment

/-! # Eventual containment of selector balls -/

set_option autoImplicit false

open Set Metric Filter

namespace LatticeProb

/-- Uniformly close position maps eventually pull every selector ball into
an open region containing the corresponding closed balls. -/
theorem eventually_selectorBall_preimage_subset_outer {E ι : Type*}
    [MetricSpace E] [ProperSpace E] (l : Filter ι) (V : ι → Type*)
    (centers : Finset E) (r : ℝ) {W : Set E} (hW : IsOpen W)
    (hballs : ∀ c ∈ centers, closedBall c r ⊆ W)
    (p q : ∀ i, V i → E)
    (hclose : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, ∀ v, dist (p i v) (q i v) < δ) :
    ∀ᶠ i in l, ∀ c ∈ centers, (q i) ⁻¹' ball c r ⊆ (p i) ⁻¹' W := by
  obtain ⟨δ, hδ, hcontain⟩ :=
    exists_selectorBall_preimage_subset_outer (V := Unit) centers r hW hballs
  filter_upwards [hclose δ hδ] with i hi
  intro c hc v hv
  exact hcontain (fun _ => p i v) (fun _ => q i v)
    (fun _ => (hi v).le) c hc (a := ()) hv

end LatticeProb
