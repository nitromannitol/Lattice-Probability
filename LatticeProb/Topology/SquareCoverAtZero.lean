import LatticeProb.Topology.RectangleSquareCover

/-!
# Covering a closed square through the origin by squares cornered at the origin

A closed square `[x, x + r] × [y, y + r]` containing the origin is the union of finitely many closed squares
`[a, a + s] × [b, b + s]` of one side `s > 0`, each of which either avoids the origin or has the origin as a corner,
that is `a, b ∈ {0, -s}`. The squares are the products of two one-dimensional covers of `[x, 0]` and `[0, x + r]`
(resp. `[y, 0]` and `[0, y + r]`) by intervals of length `s`, so an interval of the cover contains `0` only as an
endpoint.

* `exists_finset_Icc_cover_of_zero_mem`: the one-dimensional cover.
* `exists_finset_square_cover_of_zero_mem`: the cover of the square.
-/

namespace LatticeProb.Topology

open Set

/-- One-dimensional cover through the origin: if `x ≤ 0 ≤ x + r` with `0 < r`, and `0 < s` with `s ≤ -x` when
`x < 0` and `s ≤ x + r` when `0 < x + r`, then finitely many intervals `[c, c + s] ⊆ [x, x + r]` cover `[x, x + r]`,
and each of them that contains `0` has `0` as an endpoint (`c = 0` or `c = -s`). -/
theorem exists_finset_Icc_cover_of_zero_mem {x r s : ℝ} (hr : 0 < r) (hx : x ≤ 0) (hxr : 0 ≤ x + r)
    (hs : 0 < s) (hneg : x < 0 → s ≤ -x) (hpos : 0 < x + r → s ≤ x + r) :
    ∃ X : Finset ℝ, (∀ c ∈ X, x ≤ c ∧ c + s ≤ x + r ∧ ((0 : ℝ) ∈ Icc c (c + s) → c = 0 ∨ c = -s)) ∧
      ∀ t ∈ Icc x (x + r), ∃ c ∈ X, t ∈ Icc c (c + s) := by
  classical
  have hXn : ∃ X : Finset ℝ, (∀ c ∈ X, x ≤ c ∧ c + s ≤ 0) ∧
      (x < 0 → ∀ t ∈ Icc x 0, ∃ c ∈ X, t ∈ Icc c (c + s)) := by
    by_cases h : x < 0
    · obtain ⟨X, hX, hXc⟩ := exists_finset_Icc_cover hs (by linarith [hneg h] : s ≤ 0 - x)
      exact ⟨X, hX, fun _ => hXc⟩
    · exact ⟨∅, by simp, fun h' => absurd h' h⟩
  have hXp : ∃ X : Finset ℝ, (∀ c ∈ X, 0 ≤ c ∧ c + s ≤ x + r) ∧
      (0 < x + r → ∀ t ∈ Icc 0 (x + r), ∃ c ∈ X, t ∈ Icc c (c + s)) := by
    by_cases h : 0 < x + r
    · obtain ⟨X, hX, hXc⟩ := exists_finset_Icc_cover hs (by linarith [hpos h] : s ≤ x + r - 0)
      exact ⟨X, hX, fun _ => hXc⟩
    · exact ⟨∅, by simp, fun h' => absurd h' h⟩
  obtain ⟨Xn, hXn, hXnc⟩ := hXn
  obtain ⟨Xp, hXp, hXpc⟩ := hXp
  refine ⟨Xn ∪ Xp, fun c hc => ?_, fun t ht => ?_⟩
  · rcases Finset.mem_union.1 hc with hc | hc
    · obtain ⟨h1, h2⟩ := hXn c hc
      exact ⟨h1, by linarith, fun h0 => Or.inr (by linarith [h0.2])⟩
    · obtain ⟨h1, h2⟩ := hXp c hc
      exact ⟨by linarith, h2, fun h0 => Or.inl (by linarith [h0.1])⟩
  · rcases le_or_gt t 0 with htn | htp
    · rcases hx.lt_or_eq with hxn | hx0
      · obtain ⟨c, hc, htc⟩ := hXnc hxn t ⟨ht.1, htn⟩
        exact ⟨c, Finset.mem_union_left _ hc, htc⟩
      · obtain ⟨c, hc, htc⟩ := hXpc (by linarith) t ⟨by linarith [ht.1], ht.2⟩
        exact ⟨c, Finset.mem_union_right _ hc, htc⟩
    · obtain ⟨c, hc, htc⟩ := hXpc (by linarith [ht.2]) t ⟨htp.le, ht.2⟩
      exact ⟨c, Finset.mem_union_right _ hc, htc⟩

/-- A closed square `[x, x + r] × [y, y + r]` containing the origin is the union of finitely many closed squares
`[a, a + s] × [b, b + s]` (`(a, b) ∈ P`) of one side `s > 0`, each of which either avoids the origin or has the origin
as a corner: `a = 0` or `a = -s`, and `b = 0` or `b = -s`. -/
theorem exists_finset_square_cover_of_zero_mem {x y r : ℝ} (hr : 0 < r)
    (h0 : (0 : ℂ) ∈ Icc x (x + r) ×ℂ Icc y (y + r)) :
    ∃ (s : ℝ) (P : Finset (ℝ × ℝ)), 0 < s ∧
      (⋃ p ∈ P, Icc p.1 (p.1 + s) ×ℂ Icc p.2 (p.2 + s)) = Icc x (x + r) ×ℂ Icc y (y + r) ∧
      ∀ p ∈ P, (0 : ℂ) ∉ Icc p.1 (p.1 + s) ×ℂ Icc p.2 (p.2 + s) ∨
        ((p.1 = 0 ∨ p.1 = -s) ∧ (p.2 = 0 ∨ p.2 = -s)) := by
  classical
  rw [Complex.mem_reProdIm, Complex.zero_re, Complex.zero_im, mem_Icc, mem_Icc] at h0
  obtain ⟨⟨hx, hxr⟩, ⟨hy, hyr⟩⟩ := h0
  obtain ⟨s, hs, hx₁, hx₂, hy₁, hy₂⟩ : ∃ s : ℝ, 0 < s ∧ (x < 0 → s ≤ -x) ∧ (0 < x + r → s ≤ x + r) ∧
      (y < 0 → s ≤ -y) ∧ (0 < y + r → s ≤ y + r) := by
    refine ⟨min (min (if x < 0 then -x else r) (if 0 < x + r then x + r else r))
      (min (if y < 0 then -y else r) (if 0 < y + r then y + r else r)), ?_, fun h => ?_, fun h => ?_,
      fun h => ?_, fun h => ?_⟩
    · simp only [lt_min_iff]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> split_ifs <;> linarith
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (by simp [h]))
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (by simp [h]))
    · exact (min_le_right _ _).trans ((min_le_left _ _).trans (by simp [h]))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (by simp [h]))
  obtain ⟨X, hX, hXc⟩ := exists_finset_Icc_cover_of_zero_mem hr hx hxr hs hx₁ hx₂
  obtain ⟨Y, hY, hYc⟩ := exists_finset_Icc_cover_of_zero_mem hr hy hyr hs hy₁ hy₂
  refine ⟨s, X ×ˢ Y, hs, Subset.antisymm (iUnion₂_subset fun p hp => fun z hz => ?_) (fun z hz => ?_),
    fun p hp => ?_⟩
  · obtain ⟨hpx, hpy⟩ := Finset.mem_product.1 hp
    obtain ⟨h1, h2, -⟩ := hX p.1 hpx
    obtain ⟨h3, h4, -⟩ := hY p.2 hpy
    rw [Complex.mem_reProdIm, mem_Icc, mem_Icc] at hz ⊢
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rw [Complex.mem_reProdIm] at hz
    obtain ⟨c, hc, hzc⟩ := hXc _ hz.1
    obtain ⟨d, hd, hzd⟩ := hYc _ hz.2
    exact mem_biUnion (x := (c, d)) (Finset.mem_coe.2 (Finset.mem_product.2 ⟨hc, hd⟩))
      (Complex.mem_reProdIm.2 ⟨hzc, hzd⟩)
  · obtain ⟨hpx, hpy⟩ := Finset.mem_product.1 hp
    by_cases hp0 : (0 : ℂ) ∈ Icc p.1 (p.1 + s) ×ℂ Icc p.2 (p.2 + s)
    · rw [Complex.mem_reProdIm, Complex.zero_re, Complex.zero_im] at hp0
      exact Or.inr ⟨(hX p.1 hpx).2.2 hp0.1, (hY p.2 hpy).2.2 hp0.2⟩
    · exact Or.inl hp0

end LatticeProb.Topology
