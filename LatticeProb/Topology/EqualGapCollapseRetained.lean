import LatticeProb.Topology.EqualGapCollapse

/-! # Continuity of gap filling at retained parameters -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Relative to a retained point, every filled value is attained by the original
map at a parameter between that point and the parameter being evaluated. -/
theorem equalGapCollapse_eq_between {Y : Type*} (f : ℝ → Y) {K : Set ℝ}
    (hK : IsClosed K) {a b x : ℝ} (ha : a ∈ K) (hb : b ∈ K)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v)
    (hxK : x ∈ K) (y : ℝ) :
    ∃ z ∈ Icc (min x y) (max x y), equalGapCollapse f hK ha hb hgap y = f z := by
  by_cases hy : y ∈ Icc a b
  · obtain ⟨u, hu, v, hv, huy, hyv, huv, hfree⟩ :=
      exists_equal_gap_bracketing_point f hK ha hb hy hgap
    have heq := equalGapCollapse_eq_of_bracket f hK ha hb hgap hy hu huy hyv huv hfree
    by_cases hxu : x ≤ u
    · have hxy : x ≤ y := le_trans hxu huy
      refine ⟨u, ?_, heq⟩
      simpa only [min_eq_left hxy, max_eq_right hxy, mem_Icc] using And.intro hxu huy
    · have hvx : v ≤ x := by
        by_contra h
        exact hfree x hxK ⟨lt_of_not_ge hxu, lt_of_not_ge h⟩
      have hyx : y ≤ x := le_trans hyv hvx
      refine ⟨v, ?_, heq.trans huv⟩
      simpa only [min_eq_right hyx, max_eq_left hyx, mem_Icc] using And.intro hyv hvx
  · refine ⟨y, ⟨min_le_right _ _, le_max_right _ _⟩, ?_⟩
    simp only [equalGapCollapse, dite_eq_right hy]

/-- Equal-image gap filling preserves continuity at every retained parameter. -/
theorem continuousAt_equalGapCollapse_of_mem {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) {K : Set ℝ} (hK : IsClosed K) {a b x : ℝ}
    (ha : a ∈ K) (hb : b ∈ K)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v)
    (hxK : x ∈ K) (hf : ContinuousAt f x) :
    ContinuousAt (equalGapCollapse f hK ha hb hgap) x := by
  have hx : equalGapCollapse f hK ha hb hgap x = f x := by
    by_cases h : x ∈ Icc a b
    · exact equalGapCollapse_eq_of_mem f hK ha hb hgap h hxK
    · simp only [equalGapCollapse, dite_eq_right h]
  rw [Metric.continuousAt_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  obtain ⟨z, hz, heq⟩ := equalGapCollapse_eq_between f hK ha hb hgap hxK y
  rw [heq, hx]
  apply hδf
  rw [Real.dist_eq, abs_lt] at hy ⊢
  rcases hz with ⟨hz₁, hz₂⟩
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy] at hz₁
    rw [max_eq_right hxy] at hz₂
    constructor <;> linarith
  · rw [min_eq_right hyx] at hz₁
    rw [max_eq_left hyx] at hz₂
    constructor <;> linarith

end LatticeProb
