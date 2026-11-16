import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! # Bracketing intervals by gaps -/

set_option autoImplicit false

namespace LatticeProb

/-- A closed set avoiding a compact interval has a gap enclosing that interval,
provided it contains points on either side. -/
theorem exists_gap_bracketing_interval (K : Set ℝ) (hK : IsClosed K)
    {u v x y : ℝ} (hu : u ∈ K) (hv : v ∈ K)
    (hux : u < x) (hxy : x ≤ y) (hyv : y < v)
    (havoid : Disjoint K (Set.Icc x y)) :
    ∃ s ∈ K, ∃ t ∈ K, u ≤ s ∧ s < x ∧ y < t ∧ t ≤ v ∧
      ∀ w ∈ K, ¬ (s < w ∧ w < t) := by
  have hleft : IsCompact (K ∩ Set.Icc u x) :=
    isCompact_Icc.inter_left hK
  have hright : IsCompact (K ∩ Set.Icc y v) :=
    isCompact_Icc.inter_left hK
  obtain ⟨s, hs, hsmax⟩ := hleft.exists_isGreatest ⟨u, hu, le_rfl, hux.le⟩
  obtain ⟨t, ht, htmin⟩ := hright.exists_isLeast ⟨v, hv, hyv.le, le_rfl⟩
  have hsx : s < x := by
    have hne : s ∉ Set.Icc x y := fun h => (Set.disjoint_left.mp havoid) hs.1 h
    have hsle := hs.2.2
    by_contra h
    exact hne ⟨le_antisymm hsle (le_of_not_gt h) ▸ le_rfl, by linarith⟩
  have hyt : y < t := by
    have hne : t ∉ Set.Icc x y := fun h => (Set.disjoint_left.mp havoid) ht.1 h
    have hyle := ht.2.1
    by_contra h
    exact hne ⟨by linarith, by linarith⟩
  refine ⟨s, hs.1, t, ht.1, hs.2.1, hsx, hyt, ht.2.2, ?_⟩
  intro w hw ⟨hsw, hwt⟩
  by_cases hwx : w < x
  · have : w ≤ s := hsmax ⟨hw, le_trans hs.2.1 hsw.le, hwx.le⟩
    linarith
  · by_cases hyw : y < w
    · have : t ≤ w := htmin ⟨hw, hyw.le, le_trans hwt.le ht.2.2⟩
      linarith
    · exact (Set.disjoint_left.mp havoid) hw ⟨le_of_not_gt hwx, le_of_not_gt hyw⟩

end LatticeProb
