import LatticeProb.Topology.EqualGapPointBracketing

/-! # Filling equal-image parameter gaps -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Two equal-image gaps containing the same point have the same endpoint image. -/
theorem eq_of_overlapping_equal_gaps {Y : Type*} (f : ℝ → Y) {K : Set ℝ}
    {s t u v x : ℝ} (hs : s ∈ K) (hu : u ∈ K)
    (hsx : s ≤ x) (hxt : x ≤ t) (hux : u ≤ x) (hxv : x ≤ v)
    (hst : f s = f t) (huv : f u = f v)
    (hstgap : ∀ w ∈ K, ¬ (s < w ∧ w < t))
    (huvgap : ∀ w ∈ K, ¬ (u < w ∧ w < v)) : f s = f u := by
  rcases le_total s u with hsu | hus
  · have hut : u ≤ t := le_trans hux hxt
    by_cases h : s = u
    · rw [h]
    · have hsu' : s < u := lt_of_le_of_ne hsu h
      have hut' : u = t := by
        by_contra hne
        exact hstgap u hu ⟨hsu', lt_of_le_of_ne hut hne⟩
      rw [hut', hst]
  · have hsv : s ≤ v := le_trans hsx hxv
    by_cases h : u = s
    · rw [h]
    · have hus' : u < s := lt_of_le_of_ne hus h
      have hsv' : s = v := by
        by_contra hne
        exact huvgap s hs ⟨hus', lt_of_le_of_ne hsv hne⟩
      rw [hsv', huv]

/-- Fill each gap in a closed parameter set with its common endpoint image. Outside
`[a,b]` the original function is retained. -/
noncomputable def equalGapCollapse {Y : Type*} (f : ℝ → Y) {K : Set ℝ}
    (hK : IsClosed K) {a b : ℝ} (ha : a ∈ K) (hb : b ∈ K)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v) (x : ℝ) : Y := by
  classical
  exact if hx : x ∈ Icc a b then
    f (Classical.choose (exists_equal_gap_bracketing_point f hK ha hb hx hgap))
  else f x

/-- The value of the filled map is the image of either endpoint of any gap
bracketing the point. -/
theorem equalGapCollapse_eq_of_bracket {Y : Type*} (f : ℝ → Y) {K : Set ℝ}
    (hK : IsClosed K) {a b x u v : ℝ} (ha : a ∈ K) (hb : b ∈ K)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v)
    (hx : x ∈ Icc a b) (hu : u ∈ K)
    (hux : u ≤ x) (hxv : x ≤ v) (huv : f u = f v)
    (huvgap : ∀ w ∈ K, ¬ (u < w ∧ w < v)) :
    equalGapCollapse f hK ha hb hgap x = f u := by
  classical
  let h := exists_equal_gap_bracketing_point f hK ha hb hx hgap
  let s := Classical.choose h
  have hs := Classical.choose_spec h
  let t := Classical.choose hs.2
  have ht := Classical.choose_spec hs.2
  rw [equalGapCollapse, dite_eq_left hx]
  exact eq_of_overlapping_equal_gaps f hs.1 hu ht.2.1 ht.2.2.1 hux hxv
    ht.2.2.2.1 huv ht.2.2.2.2 huvgap

/-- Gap filling preserves the original values at retained points. -/
theorem equalGapCollapse_eq_of_mem {Y : Type*} (f : ℝ → Y) {K : Set ℝ}
    (hK : IsClosed K) {a b x : ℝ} (ha : a ∈ K) (hb : b ∈ K)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v)
    (hx : x ∈ Icc a b) (hxK : x ∈ K) :
    equalGapCollapse f hK ha hb hgap x = f x := by
  exact equalGapCollapse_eq_of_bracket f hK ha hb hgap hx hxK le_rfl le_rfl rfl
    (fun _ _ h => lt_irrefl x (lt_trans h.1 h.2))

end LatticeProb
