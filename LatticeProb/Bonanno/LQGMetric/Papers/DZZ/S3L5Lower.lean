/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5Lower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinRow

/-!
# DZZ (Eq.lowerboundforDprime): `D'_δ(A, B) ≥ ξ / (2 δ^{C_Mc})` (P2-DZZ3G)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1080–1083, proof of Lemma 3.5):
"on `𝓔_{δ,α}`, `min_{x ∈ A_δ, y ∈ B_δ} D'_{γ,δ}(x, y) ≥ ξ / (2 δ^{C_Mc})`". DZZ give no
argument; own elementary proof: consecutive cells of a chain have intersecting closures and
each closed cell of side `≤ s` has diameter `≤ 2 s`, so a chain of `n + 1` cells joins points
at distance `≤ 2 s (n + 1)`.

* `dist_le_of_walk`: points of the end cells of a walk of length `ℓ` are `≤ 2 s (ℓ + 1)` apart.
* `approxDist_ge_of_dist`, `approxDistSet_ge_of_dist`: the lower bounds for `D'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ s : ℝ}

lemma dist_le_of_mem_closedBox {b : DyBox} {z w : ℂ} (hz : z ∈ b.closedBox)
    (hw : w ∈ b.closedBox) : dist z w ≤ 2 * b.side := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  obtain ⟨w1, w2, w3, w4⟩ := hw
  rw [Complex.dist_eq]
  have a1 : |(z - w).re| ≤ b.side := by
    rw [Complex.sub_re, abs_le]; constructor <;> linarith
  have a2 : |(z - w).im| ≤ b.side := by
    rw [Complex.sub_im, abs_le]; constructor <;> linarith
  linarith [Complex.norm_le_abs_re_add_abs_im (z - w)]

/-- Along a walk of cells of side `≤ s`, the end cells are `≤ 2 s (ℓ + 1)` apart. -/
lemma dist_le_of_walk (hs : ∀ b, IsCell m δ b → b.side ≤ s) {b b' : DyBox}
    (p : (cellGraph m δ).Walk b b') (hb : IsCell m δ b) {z w : ℂ} (hz : z ∈ b.closedBox)
    (hw : w ∈ b'.closedBox) : dist z w ≤ 2 * s * (p.length + 1) := by
  induction p generalizing z with
  | nil =>
    simp only [SimpleGraph.Walk.length_nil, CharP.cast_eq_zero, zero_add, mul_one]
    exact (dist_le_of_mem_closedBox hz hw).trans (by linarith [hs _ hb])
  | @cons x c y hadj p ih =>
    obtain ⟨y0, hy0⟩ := (Set.not_subsingleton_iff.1 hadj.2.2.2).nonempty
    have h1 : dist z y0 ≤ 2 * s :=
      (dist_le_of_mem_closedBox hz hy0.1).trans (by linarith [hs _ hadj.1])
    have h2 := ih hadj.2.1 hy0.2 hw
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    calc dist z w ≤ dist z y0 + dist y0 w := dist_triangle _ _ _
      _ ≤ 2 * s + 2 * s * (p.length + 1) := add_le_add h1 h2
      _ = 2 * s * (p.length + 1 + 1) := by ring

lemma mem_closedBox_of_mem {b : DyBox} {u : ℂ} (hu : b.Mem u) : u ∈ b.closedBox := by
  have := mem_closedBox_boxAt (L := b.n) hu.1
  rwa [hu.2] at this

/-- `D'_δ(u, v) ≥ n + 1` when `2 s n < |u − v|` and all cells have side `≤ s`. -/
lemma approxDist_ge_of_dist (hs : ∀ b, IsCell m δ b → b.side ≤ s) {u v : ℂ} {n : ℕ}
    (h : 2 * s * n < dist u v) : ((n : ℕ∞) + 1) ≤ approxDist m δ u v := by
  unfold approxDist
  refine le_iInf fun b => le_iInf fun b' => le_iInf fun hb => le_iInf fun hb' => ?_
  gcongr
  by_contra hlt
  push Not at hlt
  have hne : (cellGraph m δ).edist b b' ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  rw [← hp] at hlt
  have hlen : p.length + 1 ≤ n := by exact_mod_cast Order.add_one_le_of_lt hlt
  have hd := dist_le_of_walk hs p hb.1 (mem_closedBox_of_mem hb.2) (mem_closedBox_of_mem hb'.2)
  have hs0 : 0 ≤ s := (side_pos' b).le.trans (hs b hb.1)
  have : 2 * s * ((p.length : ℝ) + 1) ≤ 2 * s * n :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) (by positivity)
  linarith

/-- The set version: `min_{A × B} D'_δ ≥ n + 1` when all pairs are `> 2 s n` apart. -/
lemma approxDistSet_ge_of_dist (hs : ∀ b, IsCell m δ b → b.side ≤ s) {A B : Set ℂ} {n : ℕ}
    (h : ∀ x ∈ A, ∀ y ∈ B, 2 * s * n < dist x y) :
    ((n : ℕ∞) + 1) ≤ approxDistSet m δ A B :=
  le_iInf₂ fun x hx => le_iInf₂ fun y hy => approxDist_ge_of_dist hs (h x hx y hy)

end DZZ
end LQGMetric
