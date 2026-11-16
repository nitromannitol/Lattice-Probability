import LatticeProb.Topology.EqualGapCollapse
import LatticeProb.Topology.MinimalGapLoopFree

/-! # Interval fibres of equal-gap filling -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- The fibres of the filled map are intervals within a minimal equal-gap set's
parameter interval. -/
theorem equalGapCollapse_eq_of_between {Y : Type*} (f : ℝ → Y)
    {a b : ℝ} {K : Set ℝ} (hsub : K ⊆ Icc a b) (hclosed : IsClosed K)
    (ha : a ∈ K) (hb : b ∈ K)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v)
    (hmin : ∀ L : Set ℝ, L ⊆ K → IsClosed L → a ∈ L → b ∈ L →
      (∀ u ∈ L, ∀ v ∈ L, u < v →
        (∀ w ∈ L, ¬ (u < w ∧ w < v)) → f u = f v) → L = K)
    {x y z : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxz : x ≤ z) (hzy : z ≤ y)
    (heq : equalGapCollapse f hclosed ha hb hgap x =
      equalGapCollapse f hclosed ha hb hgap y) :
    equalGapCollapse f hclosed ha hb hgap z =
      equalGapCollapse f hclosed ha hb hgap x := by
  obtain ⟨u, hu, v, hv, hux, hxv, huv, huvfree⟩ :=
    exists_equal_gap_bracketing_point f hclosed ha hb hx hgap
  obtain ⟨p, hp, q, hq, hpy, hyq, hpq, hpqfree⟩ :=
    exists_equal_gap_bracketing_point f hclosed ha hb hy hgap
  have hxval : equalGapCollapse f hclosed ha hb hgap x = f u :=
    equalGapCollapse_eq_of_bracket f hclosed ha hb hgap hx hu hux hxv huv huvfree
  have hyval : equalGapCollapse f hclosed ha hb hgap y = f p :=
    equalGapCollapse_eq_of_bracket f hclosed ha hb hgap hy hp hpy hyq hpq hpqfree
  have huq : f u = f q := hxval.symm.trans (heq.trans (hyval.trans hpq))
  have hfree : ∀ w ∈ K, ¬ (u < w ∧ w < q) :=
    no_mem_between_of_minimal_equal_gap f hsub hclosed ha hb hgap hmin hu hq huq
  have hz : z ∈ Icc a b := ⟨le_trans hx.1 hxz, le_trans hzy hy.2⟩
  have hzval : equalGapCollapse f hclosed ha hb hgap z = f u :=
    equalGapCollapse_eq_of_bracket f hclosed ha hb hgap hz hu
      (le_trans hux hxz) (le_trans hzy hyq) huq hfree
  exact hzval.trans hxval.symm

end LatticeProb
