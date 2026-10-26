import LatticeProb.Prob.Percolation.OpenComponentTranslation

/-!
# Translation on component vertices and neighbor sums

The induced support equivalence is the literal addition/subtraction map. Its graph
isomorphism transports the finite neighbor sum, including every summand.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- Restriction of lattice translation to the actual component vertex subtypes. -/
def openComponentTranslationIso (z : Vertex d) (C : OpenComponent ω) :
    componentGraph C ≃g componentGraph (openComponentTranslation z ω C) where
  toEquiv := SimpleGraph.ConnectedComponent.isoEquivSupp (openGraphTranslation z ω) C
  map_rel_iff' := (openGraphTranslation z ω).map_rel_iff

/-- The forward component vertex map is addition by the displacement. -/
theorem openComponentTranslationIso_val (z : Vertex d) (C : OpenComponent ω) (x : C) :
    (openComponentTranslationIso z C x).val = x.val + z := rfl

/-- The inverse component vertex map is subtraction by the displacement. -/
theorem openComponentTranslationIso_symm_val (z : Vertex d) (C : OpenComponent ω)
    (y : openComponentTranslation z ω C) :
    ((openComponentTranslationIso z C).symm y).val = y.val - z := rfl

/-- The literal inverse-composition pullback preserves the actual finite Laplacian. -/
theorem componentLaplacian_translation (z : Vertex d) (C : OpenComponent ω)
    (u : C → ℝ) (x : C) :
    componentLaplacian (openComponentTranslation z ω C)
      (fun y => u ((openComponentTranslationIso z C).symm y))
      (openComponentTranslationIso z C x) = componentLaplacian C u x := by
  classical
  let e := openComponentTranslationIso z C
  unfold componentLaplacian
  symm
  apply Finset.sum_bij (fun y _ => e y)
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact e.map_rel_iff.mpr hy
  · intro y _ y' _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact e.map_rel_iff.mp (by simpa only [e.apply_symm_apply] using hy)
  · intro y _
    change u y - u x = u (e.symm (e y)) - u (e.symm (e x))
    rw [e.symm_apply_apply, e.symm_apply_apply]

/-- Integer differences on all actual component edges are preserved and reflected. -/
theorem component_integer_gradient_translation_iff (z : Vertex d) (C : OpenComponent ω)
    (u : C → ℝ) :
    (∀ x y : openComponentTranslation z ω C,
      (componentGraph (openComponentTranslation z ω C)).Adj x y →
      ∃ n : ℤ, u ((openComponentTranslationIso z C).symm y) -
        u ((openComponentTranslationIso z C).symm x) = (n : ℝ)) ↔
    (∀ x y : C, (componentGraph C).Adj x y → ∃ n : ℤ, u y - u x = (n : ℝ)) := by
  let e := openComponentTranslationIso z C
  constructor
  · intro h x y hxy
    have ht := h (e x) (e y) (e.map_rel_iff.mpr hxy)
    change ∃ n : ℤ, u (e.symm (e y)) - u (e.symm (e x)) = (n : ℝ) at ht
    simpa only [e.symm_apply_apply] using ht
  · intro h x y hxy
    exact h (e.symm x) (e.symm y) (e.symm.map_rel_iff.mpr hxy)

end

end LatticeProb.Percolation
