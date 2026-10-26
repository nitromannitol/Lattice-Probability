import LatticeProb.Network.IntegerGradientEnergy
import LatticeProb.Prob.Percolation.DeletedInfiniteComponent

/-!
# The canonical patch of nonzero component gradients

Unordered edges on an actual open component map by the subtype inclusion to ambient
unordered pairs. The finite patch consists of precisely these pairs, regarded as genuine
lattice bonds. Both the ambient image and the full component preimage are exact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open scoped BigOperators

variable {d : ℕ} {ω : Configuration d}

/-- All actual component edges across which the real function changes value. -/
def componentGradientEdges (C : OpenComponent ω) (w : C → ℝ) : Set (Sym2 C) :=
  {e | ∃ x y, e = s(x, y) ∧ (componentGraph C).Adj x y ∧ w x ≠ w y}

/-- Genuine ambient bonds whose whole unordered pair is the image of a gradient edge. -/
def componentGradientBonds (C : OpenComponent ω) (w : C → ℝ) : Set (Bond d) :=
  Subtype.val ⁻¹' (Sym2.map (Subtype.val : C → Vertex d) '' componentGradientEdges C w)

/-- The exact bond set is finite whenever the exact component edge set is finite. -/
theorem componentGradientBonds_finite (C : OpenComponent ω) (w : C → ℝ)
    (hfinite : (componentGradientEdges C w).Finite) :
    (componentGradientBonds C w).Finite :=
  Set.Finite.preimage (fun _ _ _ _ h => Subtype.val_injective h)
    (hfinite.image (Sym2.map (Subtype.val : C → Vertex d)))

/-- The finite patch enumerates exactly the ambient gradient bonds, without orientations. -/
noncomputable def componentGradientPatch (C : OpenComponent ω) (w : C → ℝ)
    (hfinite : (componentGradientEdges C w).Finite) : Finset (Bond d) :=
  (componentGradientBonds_finite C w hfinite).toFinset

/-- Complete membership characterization of the canonical finite patch. -/
theorem mem_componentGradientPatch (C : OpenComponent ω) (w : C → ℝ)
    (hfinite : (componentGradientEdges C w).Finite) (e : Bond d) :
    e ∈ componentGradientPatch C w hfinite ↔
      ∃ x y : C, e.val = s(x.val, y.val) ∧ (componentGraph C).Adj x y ∧ w x ≠ w y := by
  rw [componentGradientPatch, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨a, ⟨x, y, rfl, hxy, hne⟩, he⟩
    exact ⟨x, y, he.symm, hxy, hne⟩
  · rintro ⟨x, y, he, hxy, hne⟩
    exact ⟨s(x, y), ⟨x, y, rfl, hxy, hne⟩, he.symm⟩

/-- Every selected bond is open in the actual configuration. -/
theorem componentGradientPatch_all_open (C : OpenComponent ω) (w : C → ℝ)
    (hfinite : (componentGradientEdges C w).Finite) :
    ∀ e ∈ componentGradientPatch C w hfinite, ω e = true := by
  intro e he
  obtain ⟨x, y, heq, hxy, _⟩ := (mem_componentGradientPatch C w hfinite e).mp he
  obtain ⟨h, ho⟩ := (openGraph_adj_iff ω x.val y.val).mp hxy
  have hb : e = bondOfAdjacent h := Subtype.ext heq
  exact hb ▸ ho

/-- The ambient deleted edge set is exactly the image of all component gradient edges. -/
theorem deletedBondEdges_componentGradientPatch (C : OpenComponent ω) (w : C → ℝ)
    (hfinite : (componentGradientEdges C w).Finite) :
    deletedBondEdges (componentGradientPatch C w hfinite) =
      Sym2.map (Subtype.val : C → Vertex d) '' componentGradientEdges C w := by
  ext e
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨x, y, he, hxy, hne⟩ := (mem_componentGradientPatch C w hfinite b).mp hb
    exact ⟨s(x, y), ⟨x, y, rfl, hxy, hne⟩, he.symm⟩
  · rintro ⟨a, ⟨x, y, rfl, hxy, hne⟩, rfl⟩
    obtain ⟨h, _⟩ := (openGraph_adj_iff ω x.val y.val).mp hxy
    refine ⟨bondOfAdjacent h, ?_, rfl⟩
    exact (mem_componentGradientPatch C w hfinite _).mpr ⟨x, y, rfl, hxy, hne⟩

/-- The preimage on the entire unordered-pair carrier contains exactly the gradient edges. -/
theorem componentGradientPatch_preimage (C : OpenComponent ω) (w : C → ℝ)
    (hfinite : (componentGradientEdges C w).Finite) :
    Sym2.map (Subtype.val : C → Vertex d) ⁻¹'
        deletedBondEdges (componentGradientPatch C w hfinite) = componentGradientEdges C w := by
  rw [deletedBondEdges_componentGradientPatch]
  exact Set.preimage_image_eq _ (Sym2.map.injective Subtype.val_injective)

/-- Flipping the canonical patch deletes exactly the nonzero-gradient edges on the old carrier. -/
theorem componentGradientPatch_induce_eq_deleteEdges (C : OpenComponent ω) (w : C → ℝ)
    (hfinite : (componentGradientEdges C w).Finite) :
    (openGraph (finiteBondFlip (componentGradientPatch C w hfinite) ω)).induce C.supp =
      (componentGraph C).deleteEdges (componentGradientEdges C w) := by
  rw [finiteBondFlip_induce_eq_deleteEdges _ (componentGradientPatch_all_open C w hfinite) C,
    componentGradientPatch_preimage]

end LatticeProb.Percolation
