/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7FinRow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Mono
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinPath

/-!
# DZZ Lemma 3.7, (eq-B-good-Phi): the deterministic part (P2-DZZ3G)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1017–1035): if all boxes
`B̃_i ∈ 𝓑(B, t)` meeting the horizontal line through `x` have mass `≤ δ'²`, then
`D'_{γ,δ'}(x, ∂B_large) ≤ 4/t`. DZZ give this as an implication; own elementary proof: a row
of boxes of mass `< δ'²` maps (via the `δ'`-cell containing each box, `cellAnc`, S3L5Mono) to a
walk of `δ'`-cells which is not longer.

* `exists_walk_cellAnc_chain`, `approxDist_le_chain`: a `Neighbour`-chain of small boxes.
* `rowBox`, `approxDist_row_le`: the row of level-`N` boxes between `u` and `v` (`u.im = v.im`).
* `approxDist_comm`; `exists_frontier_row`: a point of `∂B_large ∩ 𝕍` on the horizontal line
  through `x ∈ B_large ∩ 𝕍`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- A `Neighbour`-chain of boxes of mass `< δ²` gives a walk of their `δ`-cells. -/
lemma exists_walk_cellAnc_chain (g : ℕ → DyBox) (d : ℕ) (hm : ∀ i ≤ d, m (g i) < δ ^ 2)
    (hn : ∀ i < d, Neighbour (g i) (g (i + 1))) :
    ∃ q : (cellGraph m δ).Walk (cellAnc m δ (g 0)) (cellAnc m δ (g d)), q.length ≤ d := by
  induction d with
  | zero => exact ⟨.nil, by simp⟩
  | succ d ih =>
    obtain ⟨q, hq⟩ := ih (fun i hi => hm i (by omega)) (fun i hi => hn i (by omega))
    have m1 := hm d (by omega)
    have m2 := hm (d + 1) le_rfl
    obtain ⟨-, -, -, c1⟩ := cellAnc_spec (m := m) (δ := δ) m1
    obtain ⟨-, -, -, c2⟩ := cellAnc_spec (m := m) (δ := δ) m2
    rcases eq_or_neighbour_of_sub (hn d (by omega)) (closedBox_sub_cellAnc m1)
      (closedBox_sub_cellAnc m2) with he | hN
    · exact ⟨q.copy rfl he, by rw [SimpleGraph.Walk.length_copy]; omega⟩
    · refine ⟨q.concat (show (cellGraph m δ).Adj _ _ from ⟨c1, c2, hN⟩), ?_⟩
      rw [SimpleGraph.Walk.length_concat]; omega

/-- `D'_δ(u, v) ≤ d + 1` along a chain `g 0, …, g d` of boxes of mass `< δ²`, `u ∈ g 0`,
`v ∈ g d`. -/
lemma approxDist_le_chain (g : ℕ → DyBox) (d : ℕ) (hm : ∀ i ≤ d, m (g i) < δ ^ 2)
    (hn : ∀ i < d, Neighbour (g i) (g (i + 1))) {u v : ℂ} (hu : (g 0).Mem u)
    (hv : (g d).Mem v) : approxDist m δ u v ≤ d + 1 := by
  obtain ⟨q, hq⟩ := exists_walk_cellAnc_chain g d hm hn
  obtain ⟨i, hi, he, hc⟩ := cellAnc_spec (m := m) (δ := δ) (hm 0 (Nat.zero_le _))
  obtain ⟨i', hi', he', hc'⟩ := cellAnc_spec (m := m) (δ := δ) (hm d le_rfl)
  have hu' : (cellAnc m δ (g 0)).Mem u := by rw [he]; exact mem_anc hu hi
  have hv' : (cellAnc m δ (g d)).Mem v := by rw [he']; exact mem_anc hv hi'
  unfold approxDist
  refine (iInf_le_of_le (cellAnc m δ (g 0)) (iInf_le_of_le (cellAnc m δ (g d))
    (iInf_le_of_le (show IsCell m δ _ ∧ _ from ⟨hc, hu'⟩)
      (iInf_le_of_le (show IsCell m δ _ ∧ _ from ⟨hc', hv'⟩) le_rfl)))).trans ?_
  gcongr
  exact (SimpleGraph.edist_le q).trans (by exact_mod_cast hq)

lemma approxDist_le_comm (u v : ℂ) : approxDist m δ u v ≤ approxDist m δ v u := by
  unfold approxDist
  refine le_iInf fun b => le_iInf fun b' => le_iInf fun hb => le_iInf fun hb' => ?_
  refine iInf_le_of_le b' (iInf_le_of_le b (iInf_le_of_le hb' (iInf_le_of_le hb ?_)))
  rw [SimpleGraph.edist_comm]

lemma approxDist_comm (u v : ℂ) : approxDist m δ u v = approxDist m δ v u :=
  le_antisymm (approxDist_le_comm u v) (approxDist_le_comm v u)

lemma two_pow_sub_one_lt (N : ℕ) : 2 ^ N - 1 < 2 ^ N := Nat.sub_lt (by positivity) one_pos

/-- The level-`N` box of row `k` and column `min i (2^N - 1)`. -/
def rowBox (N k : ℕ) (hk : k < 2 ^ N) (i : ℕ) : DyBox :=
  ⟨N, min i (2 ^ N - 1), k, lt_of_le_of_lt (min_le_right _ _) (two_pow_sub_one_lt N), hk⟩

lemma idx_mono (N : ℕ) {x y : ℝ} (h : x ≤ y) : idx N x ≤ idx N y :=
  min_le_min (Nat.floor_mono (mul_le_mul_of_nonneg_right h (by positivity))) le_rfl

/-- The row of level-`N` boxes from `u` to `v` (`u.re ≤ v.re`, `u.im = v.im`): if all have mass
`< δ²` then `D'_δ(u, v) ≤ (idx v.re − idx u.re) + 1`. -/
lemma approxDist_row_le {N : ℕ} {u v : ℂ} (hu : u ∈ dzzV) (hv : v ∈ dzzV) (hre : u.re ≤ v.re)
    (him : u.im = v.im)
    (hm : ∀ i, idx N u.re ≤ i → i ≤ idx N v.re → m (rowBox N (idx N u.im) (idx_lt _ _) i) < δ ^ 2) :
    approxDist m δ u v ≤ ((idx N v.re - idx N u.re : ℕ) : ℕ∞) + 1 := by
  have hmono := idx_mono N hre
  have hlt := idx_lt N v.re
  set g : ℕ → DyBox := fun i => rowBox N (idx N u.im) (idx_lt _ _) (idx N u.re + i)
  refine approxDist_le_chain g (idx N v.re - idx N u.re) (fun i hi => hm _ (by omega) (by omega))
    (fun i hi => neighbour_of_j_succ rfl rfl ?_) ⟨hu, ?_⟩ ⟨hv, ?_⟩
  · simp only [g, rowBox]; omega
  · refine DyBox.ext rfl ?_ rfl
    simp only [g, rowBox, boxAt]; omega
  · refine DyBox.ext rfl ?_ ?_
    · simp only [g, rowBox, boxAt]; omega
    · simp only [g, rowBox, boxAt, him]

lemma side_le_half (B : DyBox) (hB : 1 ≤ B.n) : B.side ≤ 1 / 2 := by
  unfold DyBox.side
  calc (2 : ℝ)⁻¹ ^ B.n ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hB
    _ = 1 / 2 := by norm_num

lemma succ_mul_side_le_one (B : DyBox) : ((B.j : ℝ) + 1) * B.side ≤ 1 := by
  have h1 : ((B.j + 1 : ℕ) : ℝ) ≤ ((2 ^ B.n : ℕ) : ℝ) := by exact_mod_cast B.hj
  push_cast at h1
  have := pow_inv_mul_pow B.n
  unfold DyBox.side
  nlinarith [show (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ B.n by positivity]

/-- A point of `∂B_large ∩ 𝕍` on the horizontal line through `x ∈ B_large ∩ 𝕍`. -/
lemma exists_frontier_row (B : DyBox) (hB : 1 ≤ B.n) {x : ℂ} (hx : x ∈ B.largeBox ∩ dzzV) :
    ∃ v : ℂ, v ∈ frontier B.largeBox ∩ dzzV ∧ v.im = x.im := by
  obtain ⟨⟨hxr, hxi⟩, hx0, hx1, hx2, hx3⟩ := hx
  have hs := side_le_half B hB
  have hs0 := side_pos' B
  have hj1 := succ_mul_side_le_one B
  have hc : B.center.re = (B.j + 1 / 2) * B.side := rfl
  have hj0 : (0 : ℝ) ≤ B.j := by positivity
  -- `σ = ±1`: the side of `B_large` met inside `𝕍`
  obtain ⟨σ, hσ, hv0, hv1⟩ : ∃ σ : ℝ, |σ| = 1 ∧ 0 ≤ B.center.re + σ * B.side ∧
      B.center.re + σ * B.side ≤ 1 := by
    by_cases h : B.center.re + B.side ≤ 1
    · exact ⟨1, by norm_num, by rw [hc]; nlinarith, by linarith⟩
    · refine ⟨-1, by norm_num, ?_, by rw [hc]; nlinarith⟩
      rcases Nat.eq_zero_or_pos B.j with h0 | h0
      · exfalso; apply h; rw [hc, h0]; push_cast; nlinarith
      · have : (1 : ℝ) ≤ B.j := by exact_mod_cast h0
        rw [hc]; nlinarith
  set v : ℂ := ⟨B.center.re + σ * B.side, x.im⟩ with hvdef
  have hvL : v ∈ B.largeBox := by
    refine ⟨?_, hxi⟩
    show |B.center.re + σ * B.side - B.center.re| ≤ B.side
    rw [add_sub_cancel_left, abs_mul, hσ, one_mul, abs_of_pos hs0]
  refine ⟨v, ⟨⟨subset_closure hvL, fun hint => ?_⟩, ⟨hv0, hv1, hx2, hx3⟩⟩, rfl⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ hint
    let w : ℂ := ⟨B.center.re + σ * (B.side + ε / 2), x.im⟩
    have hw : w ∈ Metric.ball v ε := by
      rw [Metric.mem_ball, Complex.dist_eq]
      have : w - v = ((σ * (ε / 2) : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [w, v] <;> ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, hσ, one_mul,
        abs_of_pos (by positivity)]
      linarith
    have := (interior_subset (hball hw)).1
    simp only [w, add_sub_cancel_left, abs_mul, hσ, one_mul] at this
    rw [abs_of_pos (by positivity)] at this
    linarith

end DZZ
end LQGMetric
