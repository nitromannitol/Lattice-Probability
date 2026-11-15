import LatticeProb.Bonanno.LQGMetric.Field.GreenFnSquare

/-! # Filled hulls and convex sets -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A planar set together with the bounded components of its complement. -/
def planarFilledHull (K : Set ℂ) : Set ℂ :=
  K ∪ {z | z ∈ Kᶜ ∧ Bornology.IsBounded (connectedComponentIn Kᶜ z)}

/-- Filling bounded complementary components preserves containment in a nonempty convex set. -/
theorem planarFilledHull_subset_convex {K C : Set ℂ} (hC : Convex ℝ C)
    (hCn : C.Nonempty) (hKC : K ⊆ C) : planarFilledHull K ⊆ C := by
  intro z hz
  rcases hz with hz | ⟨_, hb⟩
  · exact hKC hz
  · by_contra hzC
    obtain ⟨c, hc⟩ := hCn
    have hu := LQGMetric.not_isBounded_connectedComponentIn_compl_of_convex hC hc hzC
    exact hu (hb.subset (connectedComponentIn_mono z (compl_subset_compl.mpr hKC)))

end LatticeProb
