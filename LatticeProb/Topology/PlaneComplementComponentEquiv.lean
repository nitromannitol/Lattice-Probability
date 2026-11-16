import LatticeProb.Topology.CompactPlaneComponentCardinality

/-!
# Complementary components as a quotient

The represented components of a plane complement are equivalent to the connected components
of the complement as a subspace.
-/

open Set Bornology

namespace LatticeProb.Topology

/-- The represented complementary component of a point. -/
def planeComplementComponentOfPoint (K : Set ℂ) (x : ↥(Kᶜ)) : PlaneComplementComponent K :=
  ⟨connectedComponentIn Kᶜ x, x, x.property, rfl⟩

/-- Represented components coincide exactly when their points have the same subspace component. -/
theorem planeComplementComponentOfPoint_eq_iff (K : Set ℂ) (x y : ↥(Kᶜ)) :
    planeComplementComponentOfPoint K x = planeComplementComponentOfPoint K y ↔
      ConnectedComponents.mk x = ConnectedComponents.mk y := by
  rw [ConnectedComponents.coe_eq_coe]
  change (⟨connectedComponentIn Kᶜ x, _⟩ : PlaneComplementComponent K) =
    ⟨connectedComponentIn Kᶜ y, _⟩ ↔ _
  rw [Subtype.mk.injEq]
  rw [connectedComponentIn_eq_image x.property, connectedComponentIn_eq_image y.property,
    Subtype.val_injective.image_injective.eq_iff]

/-- Complementary components represented as subsets are equivalent to the component quotient. -/
noncomputable def planeComplementComponentEquiv (K : Set ℂ) :
    ConnectedComponents ↥(Kᶜ) ≃ PlaneComplementComponent K := by
  let f : ConnectedComponents ↥(Kᶜ) → PlaneComplementComponent K :=
    Quotient.lift (planeComplementComponentOfPoint K) (by
      intro x y h
      exact (planeComplementComponentOfPoint_eq_iff K x y).2
        (ConnectedComponents.coe_eq_coe.2 h))
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
        exact (planeComplementComponentOfPoint_eq_iff K x y).1 h
  · intro U
    obtain ⟨x, hx, hU⟩ := U.property
    refine ⟨ConnectedComponents.mk ⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hU.symm

/-- The components of a compact plane complement are its bounded components and one more. -/
theorem cardinal_connectedComponents_compl_eq_bounded_add_one {K : Set ℂ}
    (hK : IsCompact K) :
    Cardinal.mk (ConnectedComponents ↥(Kᶜ)) =
      Cardinal.mk (BoundedPlaneComplementComponent K) + 1 := by
  rw [(planeComplementComponentEquiv K).cardinal_eq,
    cardinal_compl_components_eq_bounded_add_one hK]

end LatticeProb.Topology
