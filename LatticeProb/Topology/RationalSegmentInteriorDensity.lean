import LatticeProb.Topology.RationalSegmentDensity

/-! # Density of interiors of rational curve subsegments -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- If each rational subsegment image is the closure of its interior, then
those interiors are dense in any enclosing nondegenerate curve segment. -/
theorem closure_iUnion_interior_rational_subsegment_image
    {X : Type*} [TopologicalSpace X] [T2Space X] (f : ℝ → X)
    (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hregular : ∀ (p q : ℚ), a < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < b →
      closure (interior (f '' Icc (p : ℝ) (q : ℝ))) = f '' Icc (p : ℝ) (q : ℝ)) :
    closure (⋃ (p : ℚ) (q : ℚ) (_ : a < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) < b),
      interior (f '' Icc (p : ℝ) (q : ℝ))) = f '' Icc a b := by
  let U : Set X := ⋃ (p : ℚ) (q : ℚ)
    (_ : a < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) < b),
      interior (f '' Icc (p : ℝ) (q : ℝ))
  have hsub : U ⊆ f '' Icc a b := by
    rintro x hx
    simp only [U, mem_iUnion] at hx
    obtain ⟨p, q, ⟨hap, hpq, hqb⟩, hx⟩ := hx
    obtain ⟨t, ⟨hpt, htq⟩, rfl⟩ := interior_subset hx
    exact ⟨t, ⟨hap.le.trans hpt, htq.trans hqb.le⟩, rfl⟩
  have hdense : (⋃ (p : ℚ) (q : ℚ)
      (_ : a < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) < b),
        f '' Icc (p : ℝ) (q : ℝ)) ⊆ closure U := by
    simp only [iUnion_subset_iff]
    intro p q h
    rw [← hregular p q h.1 h.2.1 h.2.2]
    apply closure_mono
    intro x hx
    simp only [U, mem_iUnion]
    exact ⟨p, q, h, hx⟩
  change closure U = f '' Icc a b
  apply Subset.antisymm
  · exact closure_minimal hsub (isCompact_Icc.image hf).isClosed
  · rw [← closure_iUnion_rational_subsegment_image f hf hab]
    exact closure_minimal hdense isClosed_closure

end LatticeProb
