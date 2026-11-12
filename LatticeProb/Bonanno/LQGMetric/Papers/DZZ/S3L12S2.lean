/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12S2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12S1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinRow

/-!
# DZZ Lemma 3.12: the initial sequence `𝒞_0` (P2-DZZ316)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1436: "Let `𝒞_0 = (𝖢_1, …, 𝖢_{d_0})`
be the geodesic in `D'_{γ,δ}` joining `u` and `v`".

* `approxDist_ne_top`: when the cells cover `𝕍` and have level `≤ M`, `D'(u, v) < ∞` (the cell
  graph is connected: walk through the level-`M` grid; own elementary argument, DZZ take it for
  granted).
* `exists_geodesic_chain`: a loop-free `Neighbour`-chain of cells joining `u` and `v` with
  `d_0 ≤ D'(u, v)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma closedBox_not_subsingleton (b : DyBox) : ¬ b.closedBox.Subsingleton := by
  intro hs
  have s0 := side_pos' b
  have h := hs (show (⟨b.j * b.side, b.k * b.side⟩ : ℂ) ∈ b.closedBox from
    ⟨le_rfl, by simp only; nlinarith, le_rfl, by simp only; nlinarith⟩)
    (show (⟨(b.j + 1) * b.side, b.k * b.side⟩ : ℂ) ∈ b.closedBox from
    ⟨by simp only; nlinarith, le_rfl, le_rfl, by simp only; nlinarith⟩)
  have := congrArg Complex.re h
  simp only at this; nlinarith

lemma cells_adj_of_boxes {c c' b b' : DyBox} (h : b = b' ∨ Neighbour b b')
    (hb : b.closedBox ⊆ c.closedBox) (hb' : b'.closedBox ⊆ c'.closedBox) :
    c = c' ∨ Neighbour c c' := by
  rcases h with rfl | h
  · by_cases he : c = c'
    · exact Or.inl he
    · exact Or.inr ⟨he, fun hs => closedBox_not_subsingleton b (hs.anti (subset_inter hb hb'))⟩
  · exact eq_or_neighbour_of_sub h hb hb'

lemma boxAt_sub_cell {c : DyBox} {M : ℕ} {x : ℂ} (hc : c.Mem x) (hM : c.n ≤ M) :
    (boxAt M x).closedBox ⊆ c.closedBox := by
  have e : (boxAt M x).anc c.n = c := by rw [anc_boxAt hM, hc.2]
  rw [← e]; exact closedBox_sub_anc _ _

/-- The lower-left corner of the level-`M` box `(j, k)`. -/
def l312GridPt (M j k : ℕ) : ℂ := ⟨j * (2 : ℝ)⁻¹ ^ M, k * (2 : ℝ)⁻¹ ^ M⟩

lemma idx_l312GridPt {M j : ℕ} (hj : j < 2 ^ M) : idx M (j * (2 : ℝ)⁻¹ ^ M) = j := by
  unfold idx
  rw [mul_assoc, pow_inv_mul_pow, mul_one, Nat.floor_natCast]; omega

lemma gridPt_mem {M j k : ℕ} (hj : j < 2 ^ M) (hk : k < 2 ^ M) : l312GridPt M j k ∈ dzzV := by
  have h1 : (j : ℝ) ≤ 2 ^ M := by exact_mod_cast hj.le
  have h2 : (k : ℝ) ≤ 2 ^ M := by exact_mod_cast hk.le
  have e := pow_inv_mul_pow M
  have p : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ M := by positivity
  refine ⟨by simp only [l312GridPt]; positivity, ?_, by simp only [l312GridPt]; positivity, ?_⟩ <;>
    simp only [l312GridPt] <;> nlinarith

lemma boxAt_gridPt {M j k : ℕ} (hj : j < 2 ^ M) (hk : k < 2 ^ M) :
    (boxAt M (l312GridPt M j k)).j = j ∧ (boxAt M (l312GridPt M j k)).k = k := by
  simp only [boxAt, l312GridPt]; exact ⟨idx_l312GridPt hj, idx_l312GridPt hk⟩

/-- Cells containing points in equal or neighbouring level-`M` boxes are reachable. -/
lemma reachable_of_boxes {M : ℕ} (hlev : ∀ c, IsCell m δ c → c.n ≤ M) {x y : ℂ} {c c' : DyBox}
    (hc : IsCell m δ c ∧ c.Mem x) (hc' : IsCell m δ c' ∧ c'.Mem y)
    (h : boxAt M x = boxAt M y ∨ Neighbour (boxAt M x) (boxAt M y)) :
    (cellGraph m δ).Reachable c c' := by
  rcases cells_adj_of_boxes h (boxAt_sub_cell hc.2 (hlev c hc.1))
    (boxAt_sub_cell hc'.2 (hlev c' hc'.1)) with he | hN
  · rw [he]
  · exact SimpleGraph.Adj.reachable ⟨hc.1, hc'.1, hN⟩

/-- **The cell graph is connected**: cells containing two points of `𝕍` are reachable. -/
theorem cellGraph_reachable {M : ℕ} (hcov : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v)
    (hlev : ∀ c, IsCell m δ c → c.n ≤ M) {x y : ℂ} {c c' : DyBox}
    (hc : IsCell m δ c ∧ c.Mem x) (hc' : IsCell m δ c' ∧ c'.Mem y) :
    (cellGraph m δ).Reachable c c' := by
  classical
  -- a chosen cell at each grid point
  have hcp : ∀ j k, ∃ c, j < 2 ^ M → k < 2 ^ M → IsCell m δ c ∧ c.Mem (l312GridPt M j k) := by
    intro j k
    by_cases h : j < 2 ^ M ∧ k < 2 ^ M
    · obtain ⟨c, hc⟩ := hcov _ (gridPt_mem h.1 h.2); exact ⟨c, fun _ _ => hc⟩
    · exact ⟨c, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose cp hcp using hcp
  -- every point reaches the cell of the grid point of its box
  have hto : ∀ {z : ℂ} {d : DyBox}, IsCell m δ d ∧ d.Mem z →
      (cellGraph m δ).Reachable d (cp (boxAt M z).j (boxAt M z).k) := by
    intro z d hd
    have hj := (boxAt M z).hj; have hk := (boxAt M z).hk
    simp only [boxAt] at hj hk
    refine reachable_of_boxes hlev hd (hcp _ _ hj hk) (Or.inl ?_)
    obtain ⟨e1, e2⟩ := boxAt_gridPt hj hk
    exact DyBox.ext rfl e1.symm e2.symm
  -- the grid is connected
  have hrow : ∀ j k, j < 2 ^ M → k < 2 ^ M → (cellGraph m δ).Reachable (cp 0 0) (cp j k) := by
    have h0 : (0 : ℕ) < 2 ^ M := Nat.two_pow_pos M
    have hstep : ∀ j k, j + 1 < 2 ^ M → k < 2 ^ M →
        (cellGraph m δ).Reachable (cp j k) (cp (j + 1) k) := fun j k hj hk => by
      obtain ⟨a1, a2⟩ := boxAt_gridPt (M := M) (by omega : j < 2 ^ M) hk
      obtain ⟨b1, b2⟩ := boxAt_gridPt (M := M) hj hk
      exact reachable_of_boxes hlev (hcp j k (by omega) hk) (hcp (j + 1) k hj hk)
        (Or.inr (neighbour_of_j_succ rfl (by rw [a2, b2]) (by rw [a1, b1])))
    have hstep' : ∀ j k, j < 2 ^ M → k + 1 < 2 ^ M →
        (cellGraph m δ).Reachable (cp j k) (cp j (k + 1)) := fun j k hj hk => by
      obtain ⟨a1, a2⟩ := boxAt_gridPt (M := M) hj (by omega : k < 2 ^ M)
      obtain ⟨b1, b2⟩ := boxAt_gridPt (M := M) hj hk
      exact reachable_of_boxes hlev (hcp j k hj (by omega)) (hcp j (k + 1) hj hk)
        (Or.inr (neighbour_of_k_succ rfl (by rw [a1, b1]) (by rw [a2, b2])))
    have hr : ∀ j, j < 2 ^ M → (cellGraph m δ).Reachable (cp 0 0) (cp j 0) := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih => intro hj; exact (ih (by omega)).trans (hstep j 0 hj h0)
    intro j k hj
    induction k with
    | zero => intro _; exact hr j hj
    | succ k ih => intro hk; exact (ih (by omega)).trans (hstep' j k hj hk)
  have hx := hto hc; have hy := hto hc'
  have a := hrow _ _ (boxAt M x).hj (boxAt M x).hk
  have b := hrow _ _ (boxAt M y).hj (boxAt M y).hk
  exact (hx.trans a.symm).trans (b.trans hy.symm)

lemma isCell_of_mem_support {c c' : DyBox} (hc : IsCell m δ c) :
    ∀ (p : (cellGraph m δ).Walk c c'), ∀ x ∈ p.support, IsCell m δ x
  | .nil, x, hx => by simp at hx; rw [hx]; exact hc
  | .cons h p, x, hx => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact isCell_of_mem_support h.2.1 p x hx

/-- **`𝒞_0`**: a `Neighbour`-chain of cells joining `u` and `v` with at most `D'(u, v)` cells. -/
theorem exists_geodesic_chain {M : ℕ} (hcov : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v)
    (hlev : ∀ c, IsCell m δ c → c.n ≤ M) {u v : ℂ} (hu : u ∈ dzzV) (hv : v ∈ dzzV) :
    ∃ l : List DyBox, JoinsCells m δ u v l ∧ l.IsChain Neighbour ∧ l.Nodup ∧
      (l.length : ℕ∞) ≤ approxDist m δ u v := by
  obtain ⟨cu, hcu⟩ := hcov u hu
  obtain ⟨cv, hcv⟩ := hcov v hv
  have hfin : approxDist m δ u v ≠ ⊤ := by
    have hr := cellGraph_reachable hcov hlev hcu hcv
    refine ne_top_of_le_ne_top ?_ (iInf_le_of_le cu (iInf_le_of_le cv
      (iInf_le_of_le hcu (iInf_le_of_le hcv le_rfl))))
    have h1 := SimpleGraph.edist_ne_top_iff_reachable.2 hr
    generalize (cellGraph m δ).edist cu cv = e at h1 ⊢
    induction e using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe n => exact_mod_cast ENat.coe_ne_top (n + 1)
  have hlt : approxDist m δ u v < approxDist m δ u v + 1 := ENat.lt_add_one_iff hfin |>.2 le_rfl
  conv_lhs at hlt => unfold approxDist
  simp only [iInf_lt_iff] at hlt
  obtain ⟨b, b', hb, hb', hlt⟩ := hlt
  have hle := (ENat.lt_add_one_iff hfin).1 hlt
  have hne : (cellGraph m δ).edist b b' ≠ ⊤ := by
    intro h; rw [h] at hle; simp at hle; exact hfin hle
  obtain ⟨p₀, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  set p := p₀.bypass
  have hpl : p.length ≤ p₀.length := SimpleGraph.Walk.length_bypass_le_length p₀
  refine ⟨p.support, ⟨by simp, isCell_of_mem_support hb.1 p, ?_, ?_⟩,
    (SimpleGraph.Walk.isChain_adj_support p).imp fun a b h => h.2.2,
    (SimpleGraph.Walk.bypass_isPath p₀).support_nodup, ?_⟩
  · rw [SimpleGraph.Walk.head_support]; exact hb.2
  · rw [SimpleGraph.Walk.getLast_support]; exact hb'.2
  · rw [SimpleGraph.Walk.length_support]
    refine le_trans ?_ hle
    rw [← hp]; push_cast; gcongr

end DZZ
end LQGMetric
