import LatticeProb.Walk.EventualSelectorBallContainment

/-! # Eventual containment for indexed balls -/

set_option autoImplicit false

open Set Metric Filter

namespace LatticeProb

/-- For a finite family of balls contained in an open region, uniformly close
position maps eventually pull both ball preimages into the same outer set. -/
theorem eventually_indexedBall_preimages_subset_outer {E ι J : Type*}
    [MetricSpace E] [ProperSpace E] [Fintype J] (l : Filter ι) (V : ι → Type*)
    (center : J → E) (r : J → ℝ) {W : Set E} (hW : IsOpen W)
    (hballs : ∀ j, closedBall (center j) (r j) ⊆ W)
    (p q : ∀ i, V i → E)
    (hclose : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, ∀ v, dist (p i v) (q i v) < δ) :
    ∀ᶠ i in l, ∀ j,
      (p i) ⁻¹' ball (center j) (r j) ⊆ (p i) ⁻¹' W ∧
      (q i) ⁻¹' ball (center j) (r j) ⊆ (p i) ⁻¹' W := by
  classical
  have hq (j : J) : ∀ᶠ i in l,
      (q i) ⁻¹' ball (center j) (r j) ⊆ (p i) ⁻¹' W := by
    filter_upwards [eventually_selectorBall_preimage_subset_outer l V
      {center j} (r j) hW (by simpa using hballs j) p q hclose] with i hi
    exact hi (center j) (Finset.mem_singleton_self _)
  filter_upwards [Filter.eventually_all.mpr hq] with i hi
  intro j
  refine ⟨?_, hi j⟩
  intro v hv
  exact hballs j (ball_subset_closedBall hv)

end LatticeProb
