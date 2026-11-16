import LatticeProb.Topology.CompactPlaneComponentCardinality

/-! # Three complementary components -/

open Set Bornology

namespace LatticeProb.Topology

/-- If a compact plane set has at most one bounded complementary component, any three
points of its complement have two belonging to the same component. -/
theorem two_of_three_compl_components_eq {K : Set ℂ} (hK : IsCompact K)
    [Subsingleton (BoundedPlaneComplementComponent K)]
    {x y z : ℂ} (hx : x ∈ Kᶜ) (hy : y ∈ Kᶜ) (hz : z ∈ Kᶜ) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y ∨
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ z ∨
    connectedComponentIn Kᶜ y = connectedComponentIn Kᶜ z := by
  have hunique (x : ℂ) (hx : x ∈ Kᶜ) (y : ℂ) (hy : y ∈ Kᶜ)
      (hbx : IsBounded (connectedComponentIn Kᶜ x))
      (hby : IsBounded (connectedComponentIn Kᶜ y)) :
      connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y := by
    let X : BoundedPlaneComplementComponent K := ⟨⟨_, x, hx, rfl⟩, hbx⟩
    let Y : BoundedPlaneComplementComponent K := ⟨⟨_, y, hy, rfl⟩, hby⟩
    exact congrArg (fun U : BoundedPlaneComplementComponent K => U.val.val)
      (Subsingleton.elim X Y)
  obtain ⟨p, hp, _, hpchar⟩ := exists_unbounded_compl_component hK
  by_cases hxp : x ∈ connectedComponentIn Kᶜ p
  · by_cases hyp : y ∈ connectedComponentIn Kᶜ p
    · left
      rw [← connectedComponentIn_eq hxp, ← connectedComponentIn_eq hyp]
    · by_cases hzp : z ∈ connectedComponentIn Kᶜ p
      · right; left
        rw [← connectedComponentIn_eq hxp, ← connectedComponentIn_eq hzp]
      · right; right
        exact hunique y hy z hz (not_not.mp fun hb => hyp ((hpchar y hy).2 hb))
          (not_not.mp fun hb => hzp ((hpchar z hz).2 hb))
  · by_cases hyp : y ∈ connectedComponentIn Kᶜ p
    · by_cases hzp : z ∈ connectedComponentIn Kᶜ p
      · right; right
        rw [← connectedComponentIn_eq hyp, ← connectedComponentIn_eq hzp]
      · right; left
        exact hunique x hx z hz (not_not.mp fun hb => hxp ((hpchar x hx).2 hb))
          (not_not.mp fun hb => hzp ((hpchar z hz).2 hb))
    · left
      exact hunique x hx y hy (not_not.mp fun hb => hxp ((hpchar x hx).2 hb))
        (not_not.mp fun hb => hyp ((hpchar y hy).2 hb))

end LatticeProb.Topology
