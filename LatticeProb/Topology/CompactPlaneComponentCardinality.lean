import LatticeProb.Topology.CompactPlaneUnboundedComponent
import Mathlib.SetTheory.Cardinal.Defs

/-!
# Complementary components of a compact plane set

The components of the complement consist of the bounded components and one unbounded component.
-/

open Set Bornology

namespace LatticeProb.Topology

/-- The connected components of the complement, represented as subsets of the plane. -/
def PlaneComplementComponent (K : Set ℂ) :=
  {U : Set ℂ // ∃ x ∈ Kᶜ, U = connectedComponentIn Kᶜ x}

/-- The bounded connected components of the complement. -/
def BoundedPlaneComplementComponent (K : Set ℂ) :=
  {U : PlaneComplementComponent K // IsBounded U.val}

/-- The components of the complement of a compact plane set consist of its bounded
components and exactly one further component, including for infinite component sets. -/
theorem cardinal_compl_components_eq_bounded_add_one {K : Set ℂ} (hK : IsCompact K) :
    Cardinal.mk (PlaneComplementComponent K) =
      Cardinal.mk (BoundedPlaneComplementComponent K) + 1 := by
  classical
  obtain ⟨p, hp, hu, hcharacter⟩ := exists_unbounded_compl_component hK
  let U : PlaneComplementComponent K := ⟨connectedComponentIn Kᶜ p, p, hp, rfl⟩
  have hiff (V : PlaneComplementComponent K) : IsBounded V.val ↔ V ≠ U := by
    obtain ⟨x, hx, hV⟩ := V.property
    constructor
    · intro hb heq
      have : V.val = U.val := congrArg Subtype.val heq
      have hbu : IsBounded U.val := this ▸ hb
      exact hu (by simpa [U] using hbu)
    · intro hne
      by_contra hb
      have hbx : ¬ IsBounded (connectedComponentIn Kᶜ x) := by simpa [hV] using hb
      have hmem : x ∈ connectedComponentIn Kᶜ p := (hcharacter x hx).2 hbx
      have heq : connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ p :=
        (connectedComponentIn_eq hmem).symm
      apply hne
      apply Subtype.ext
      exact hV.trans heq
  let e : BoundedPlaneComplementComponent K ≃ {V : PlaneComplementComponent K // V ≠ U} :=
    Equiv.subtypeEquivRight hiff
  have he : Option (BoundedPlaneComplementComponent K) ≃ PlaneComplementComponent K :=
    (Equiv.optionCongr e).trans (Equiv.optionSubtypeNe U)
  simpa only [Cardinal.mk_option] using he.cardinal_eq.symm

end LatticeProb.Topology
