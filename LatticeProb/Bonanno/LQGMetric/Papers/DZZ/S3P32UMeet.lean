/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UMeet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UGeo

/-!
# DZZ P3.2 upper bound, ball crossing: touching rings have meeting boundaries (P2-DZZ32U)

In the crossing argument of DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1071–1077) two
enclosures `ℂ_{i_r}`, `ℂ_{i_{r+1}}` "intersect". On the level-`N` grid (decision D84) the proved
recursion `l35_recursion` gives touching rings of boundary squares (`Tch`); for balls we need the
boundaries `∂B`, `∂B'` of the two ring boxes to meet:

* **`frontier_inter_of_bdry`**: if `x` is a boundary square of `B`, `y` one of `B'` (levels
  `< N`), and `x = y` or `x, y` are 4-adjacent, then `∂B ∩ ∂B' ≠ ∅`.

Own elementary argument (integer coordinates, dyadic nesting).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- Dyadic intervals `[j 2^p, (j+1) 2^p]`, `[j' 2^{p'}, (j'+1) 2^{p'}]` with `p ≤ p'` are disjoint
(up to an endpoint) or nested on the grid of mesh `2^p`. -/
lemma dy_coord (j j' p p' : ℕ) (hp : p ≤ p') :
    j * 2 ^ p + 2 ^ p ≤ j' * 2 ^ p' ∨ j' * 2 ^ p' + 2 ^ p' ≤ j * 2 ^ p ∨
      ((j * 2 ^ p = j' * 2 ^ p' ∨ j' * 2 ^ p' + 2 ^ p ≤ j * 2 ^ p) ∧
        (j * 2 ^ p + 2 ^ p = j' * 2 ^ p' + 2 ^ p' ∨
          j * 2 ^ p + 2 ^ p + 2 ^ p ≤ j' * 2 ^ p' + 2 ^ p')) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [pow_add]
  set M := 2 ^ p
  set L := 2 ^ e
  rcases lt_or_ge j (j' * L) with h | h
  · left
    calc j * M + M = (j + 1) * M := by ring
      _ ≤ (j' * L) * M := Nat.mul_le_mul_right _ h
      _ = j' * (M * L) := by ring
  · rcases le_or_gt ((j' + 1) * L) j with h' | h'
    · right; left
      calc j' * (M * L) + M * L = ((j' + 1) * L) * M := by ring
        _ ≤ j * M := Nat.mul_le_mul_right _ h'
    · right; right
      refine ⟨?_, ?_⟩
      · rcases Nat.eq_or_lt_of_le h with e1 | e1
        · left; rw [← e1]; ring
        · right
          calc j' * (M * L) + M = (j' * L + 1) * M := by ring
            _ ≤ j * M := Nat.mul_le_mul_right _ e1
      · have : j + 1 = (j' + 1) * L ∨ j + 2 ≤ (j' + 1) * L := by omega
        rcases this with e1 | e1
        · left
          calc j * M + M = (j + 1) * M := by ring
            _ = ((j' + 1) * L) * M := by rw [e1]
            _ = j' * (M * L) + M * L := by ring
        · right
          calc j * M + M + M = (j + 2) * M := by ring
            _ ≤ ((j' + 1) * L) * M := Nat.mul_le_mul_right _ e1
            _ = j' * (M * L) + M * L := by ring

/-- An integer point on the boundary of `B` (scaled by `2^N`) lies on `∂B`. -/
lemma mem_frontier_of_int {B : DyBox} {N : ℕ} (hB : B.n ≤ N) {u v : ℕ}
    (h : B.j * 2 ^ (N - B.n) ≤ u ∧ u ≤ B.j * 2 ^ (N - B.n) + 2 ^ (N - B.n) ∧
      B.k * 2 ^ (N - B.n) ≤ v ∧ v ≤ B.k * 2 ^ (N - B.n) + 2 ^ (N - B.n) ∧
      (u = B.j * 2 ^ (N - B.n) ∨ u = B.j * 2 ^ (N - B.n) + 2 ^ (N - B.n) ∨
        v = B.k * 2 ^ (N - B.n) ∨ v = B.k * 2 ^ (N - B.n) + 2 ^ (N - B.n))) :
    (⟨(u : ℝ) / 2 ^ N, (v : ℝ) / 2 ^ N⟩ : ℂ) ∈ frontier B.closedBox := by
  rw [frontier_closedBox_eq]
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  have e := bx_side_mul hB
  have es : B.side = (2 : ℝ) ^ (N - B.n) / 2 ^ N := by rw [eq_div_iff hp.ne', e]
  have d : ∀ a : ℕ, ((a : ℝ) + 1) * B.side =
      ((a * 2 ^ (N - B.n) + 2 ^ (N - B.n) : ℕ) : ℝ) / 2 ^ N := by
    intro a; rw [es]; push_cast; ring
  have c' : ∀ a : ℕ, (a : ℝ) * B.side = ((a * 2 ^ (N - B.n) : ℕ) : ℝ) / 2 ^ N := by
    intro a; rw [es]; push_cast; ring
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have le : ∀ a b : ℕ, a ≤ b → (a : ℝ) / 2 ^ N ≤ (b : ℝ) / 2 ^ N := fun a b hab =>
    div_le_div_of_nonneg_right (by exact_mod_cast hab) hp.le
  simp only [rectBd, mem_ofPred_eq, c', d]
  refine ⟨le _ _ h1, le _ _ h2, le _ _ h3, le _ _ h4, ?_⟩
  rcases h5 with e5 | e5 | e5 | e5 <;> rw [e5]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

end DZZ
end LQGMetric
