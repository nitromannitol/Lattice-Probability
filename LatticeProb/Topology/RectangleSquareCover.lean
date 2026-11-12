import LatticeProb.Topology.PlaneTopology

/-!
# Covering closed rectangles by closed squares

A closed axis-parallel rectangle `[a₁, a₂] × [b₁, b₂]` with `a₁ < a₂` and `b₁ < b₂` is the union of finitely many
closed axis-parallel squares of side `min (a₂ - a₁) (b₂ - b₁)` contained in it. Hence a finite union of closed
rectangles is a finite union of closed squares, each contained in one of the rectangles.

* `exists_finset_Icc_cover`: for `0 < s ≤ b - a`, finitely many intervals `[x, x + s] ⊆ [a, b]` cover `[a, b]`.
* `IsClosedRectangle.exists_finset_closedSquare_cover`: the cover of one closed rectangle by closed squares.
* `exists_finset_closedSquare_cover_biUnion`: the cover of a finite union of closed rectangles by closed squares.
-/

namespace LatticeProb.Topology

open Set

/-- A closed axis-parallel square `[x, x + s] × [y, y + s] ⊆ ℂ` with side length `s > 0`. -/
def IsClosedSquare (Q : Set ℂ) : Prop :=
  ∃ x y s : ℝ, 0 < s ∧ Q = Icc x (x + s) ×ℂ Icc y (y + s)

/-- A closed square is a closed rectangle. -/
theorem IsClosedSquare.isClosedRectangle {Q : Set ℂ} (hQ : IsClosedSquare Q) : IsClosedRectangle Q := by
  obtain ⟨x, y, s, hs, rfl⟩ := hQ
  exact ⟨x, x + s, y, y + s, by linarith, by linarith, rfl⟩

/-- For `0 < s ≤ b - a`, finitely many intervals `[x, x + s]` contained in `[a, b]` cover `[a, b]`: the left endpoints
`min (a + i s) (b - s)` for `0 ≤ i ≤ ⌈(b - a) / s⌉`. -/
theorem exists_finset_Icc_cover {a b s : ℝ} (hs : 0 < s) (hsb : s ≤ b - a) :
    ∃ X : Finset ℝ, (∀ x ∈ X, a ≤ x ∧ x + s ≤ b) ∧ ∀ t ∈ Icc a b, ∃ x ∈ X, t ∈ Icc x (x + s) := by
  classical
  refine ⟨(Finset.range (⌈(b - a) / s⌉₊ + 1)).image fun i : ℕ => min (a + i * s) (b - s), ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    have hi : (0 : ℝ) ≤ i * s := mul_nonneg (Nat.cast_nonneg i) hs.le
    exact ⟨le_min (by linarith) (by linarith), by linarith [min_le_right (a + i * s) (b - s)]⟩
  · rintro t ⟨hat, htb⟩
    have hc : (b - a) / s ≤ ⌈(b - a) / s⌉₊ := Nat.le_ceil _
    by_cases hts : b - s ≤ t
    · have h2 : b - a ≤ ⌈(b - a) / s⌉₊ * s := by rwa [div_le_iff₀ hs] at hc
      refine ⟨b - s, Finset.mem_image.2 ⟨⌈(b - a) / s⌉₊, Finset.self_mem_range_succ _,
        min_eq_right (by linarith)⟩, hts, by linarith⟩
    · rw [not_le] at hts
      have hq : 0 ≤ (t - a) / s := div_nonneg (by linarith) hs.le
      obtain ⟨i, hi⟩ : ∃ i : ℕ, ⌊(t - a) / s⌋₊ = i := ⟨_, rfl⟩
      have h0 := Nat.floor_le hq
      have h1 := Nat.lt_floor_add_one ((t - a) / s)
      rw [hi] at h0 h1
      have h0' : (i : ℝ) * s ≤ t - a := by rwa [le_div_iff₀ hs] at h0
      have h1' : t - a < (i + 1) * s := by rwa [div_lt_iff₀ hs] at h1
      have hmin : min (a + i * s) (b - s) = a + i * s := min_eq_left (by linarith)
      have h3 : (i : ℝ) ≤ ⌈(b - a) / s⌉₊ :=
        h0.trans ((div_le_div_of_nonneg_right (by linarith) hs.le).trans hc)
      refine ⟨a + i * s, Finset.mem_image.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le ?_), hmin⟩,
        by linarith, by linarith⟩
      exact_mod_cast h3

/-- A closed rectangle `[a₁, a₂] × [b₁, b₂]` is the union of finitely many closed squares contained in it (of side
`min (a₂ - a₁) (b₂ - b₁)`). -/
theorem IsClosedRectangle.exists_finset_closedSquare_cover {R : Set ℂ} (hR : IsClosedRectangle R) :
    ∃ G : Finset (Set ℂ), (∀ Q ∈ G, IsClosedSquare Q ∧ Q ⊆ R) ∧ R = ⋃ Q ∈ G, Q := by
  classical
  obtain ⟨a₁, a₂, b₁, b₂, ha, hb, rfl⟩ := hR
  have hs : 0 < min (a₂ - a₁) (b₂ - b₁) := lt_min (by linarith) (by linarith)
  obtain ⟨X, hX, hXc⟩ := exists_finset_Icc_cover hs (min_le_left _ _)
  obtain ⟨Y, hY, hYc⟩ := exists_finset_Icc_cover hs (min_le_right _ _)
  set s := min (a₂ - a₁) (b₂ - b₁)
  have hsub : ∀ Q ∈ (X ×ˢ Y).image (fun p : ℝ × ℝ => Icc p.1 (p.1 + s) ×ℂ Icc p.2 (p.2 + s)),
      IsClosedSquare Q ∧ Q ⊆ Icc a₁ a₂ ×ℂ Icc b₁ b₂ := by
    intro Q hQ
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.1 hQ
    obtain ⟨hx, hy⟩ := Finset.mem_product.1 hxy
    refine ⟨⟨x, y, s, hs, rfl⟩, fun z hz => ?_⟩
    rw [Complex.mem_reProdIm, mem_Icc, mem_Icc] at hz ⊢
    have := hX x hx
    have := hY y hy
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  refine ⟨_, hsub, Subset.antisymm (fun z hz => ?_) (iUnion₂_subset fun Q hQ => (hsub Q hQ).2)⟩
  rw [Complex.mem_reProdIm] at hz
  obtain ⟨x, hx, hzx⟩ := hXc _ hz.1
  obtain ⟨y, hy, hzy⟩ := hYc _ hz.2
  exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩))
    (Complex.mem_reProdIm.2 ⟨hzx, hzy⟩)

/-- A finite union of closed rectangles is a finite union of closed squares, each contained in one of the
rectangles. -/
theorem exists_finset_closedSquare_cover_biUnion (F : Finset (Set ℂ)) (hF : ∀ R ∈ F, IsClosedRectangle R) :
    ∃ G : Finset (Set ℂ), (∀ Q ∈ G, IsClosedSquare Q ∧ ∃ R ∈ F, Q ⊆ R) ∧ ⋃ R ∈ F, R = ⋃ Q ∈ G, Q := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert R F _ ih =>
    obtain ⟨G₁, hG₁, hR⟩ := (hF R (Finset.mem_insert_self R F)).exists_finset_closedSquare_cover
    obtain ⟨G₂, hG₂, hFG⟩ := ih fun R' hR' => hF R' (Finset.mem_insert_of_mem hR')
    refine ⟨G₁ ∪ G₂, fun Q hQ => ?_, ?_⟩
    · rcases Finset.mem_union.1 hQ with hQ | hQ
      · exact ⟨(hG₁ Q hQ).1, R, Finset.mem_insert_self R F, (hG₁ Q hQ).2⟩
      · obtain ⟨hQs, R', hR', hQR'⟩ := hG₂ Q hQ
        exact ⟨hQs, R', Finset.mem_insert_of_mem hR', hQR'⟩
    · rw [Finset.set_biUnion_insert, Finset.set_biUnion_union, ← hR, ← hFG]

end LatticeProb.Topology
