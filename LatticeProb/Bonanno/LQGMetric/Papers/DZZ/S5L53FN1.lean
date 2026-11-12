/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53FN1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53HB2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53UF2

/-!
# DZZ Lemma 5.3 part 1, final assembly 1: node 4 at the selected chain (P2-DZZ53FIN)

Ding–Zeitouni–Zhang, arXiv:1807.00422 (`LBM_LGDarXiv.tex`), proof of Lemma 5.3, l. 2516–2522
(`u`, `v` desirable), on the selected chain `𝒞 = l53Chain … ω` of `𝓔*` (S5L53L5), following
AUDIT-2026-10-03-N rows N6 (ii), N7 and N12: M4's argument (`l53_uv_bound`) in the cut-off form of
P2-DZZ53UF (`l53uf_uv_bound`, S5L53UF2) with `Adm ω c := c = 𝒞(ω)`, `E := l53E4 ∩ cellSizeEvent`,
`G := univ`, and `ε := ε*²` from the side ratio of consecutive chain boxes (G-A1, N12).

* `l53fn_n_eq`, `l53fn_safe`: the `L313Q` box condition `s_b = s_𝖢 ε*²` in the level form
  `n_b = n_𝖢 + 2 n_{ε*}` used by S5L53L2/M5.
* `l53fn_wdata`: the end-box data `L53WData` from the side ratio (copy of `l53_wdata_box`, S5L53M5,
  with the side ratio `ε*² s_b ≤ s_{b'}` in place of the good point `w`).
* `l53fn_real_closedBox`, `l53fn_uv_nil`: an empty chain satisfies the `u`/`v` clauses trivially
  (`μH¹` of a square is `∞`, so its real part is `0`).
* **`l53fn_node4`**: `P(E ∩ ¬(u, v clauses of 𝒞)) ≤ 2 (N + 1) B`, from the bound `B` on the bad
  events (`l53WBadQ` at threshold `0.01 ε*² s_b`), the domination of `dzzMuIn` by `M b` on `E` at
  the end boxes, and the side ratio (as hypothesis `hrat`, the exact conclusion of G-A1
  `l53_side_ratio`, S5L53GA1).

Own elementary bookkeeping (copies of S5L53M5 `l53_wdata_box` and `l53uf_UVBadBox_le`, S5L53UF2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `s_b = s_𝖢 ε*²` gives `n_b = n_𝖢 + 2 n_{ε*}`. -/
lemma l53fn_n_eq {b C : DyBox} {αs δ : ℝ} (h : b.side = C.side * epsStar αs δ ^ 2) :
    b.n = C.n + 2 * epsStarN αs δ := by
  have e : (2 : ℝ)⁻¹ ^ b.n = (2 : ℝ)⁻¹ ^ (C.n + 2 * epsStarN αs δ) := by
    rw [pow_add, pow_mul']
    exact h
  exact pow_right_injective₀ (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num) e

/-- The boxes of an `L313Q` sequence at `ε*` in the level form of S5L53L2. -/
lemma l53fn_safe {m : DyBox → ℝ} {δ αs : ℝ} {u v : ℂ} {l : List DyBox}
    (hQ : L313Q (epsStar αs δ) u v (fun b => IsCell m δ b) l) :
    ∀ b ∈ l, ∃ C : DyBox, IsCell m δ C ∧ b.closedBox ⊆ C.closedBox ∧
      b.n = C.n + 2 * epsStarN αs δ := fun b hb => by
  obtain ⟨C, hC, hs, he⟩ := hQ.2.1 b hb
  exact ⟨C, hC, hs, l53fn_n_eq he⟩

omit [MeasurableSpace Ω] in
/-- **The data of node 4 at one end of the chain** (copy of `l53_wdata_box`, S5L53M5, with the
side ratio `ε*² s_b ≤ s_{b'}` (G-A1) in place of the good point). -/
lemma l53fn_wdata {γ αs : ℝ} {W : WNSpace → Ω → ℝ} {μ0 : Ω → Measure ℂ}
    {M : DyBox → Ω → ℚ × ℚ → ℚ → ℝ≥0∞} {u v w : ℂ} {k N : ℕ} {ω : Ω}
    (hsize : ω ∈ cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k))
    (hN : ∀ C : DyBox, ((2 : ℝ)⁻¹ ^ k) ^ dzzCmc γ ≤ C.side →
      C.n + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) ≤ N)
    (hs : 12 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ ≤ ‖v - u‖) {b b' : DyBox}
    (hb : ∃ C : DyBox, IsCell (approxLQG γ W ω) ((2 : ℝ)⁻¹ ^ k) C ∧
      b.closedBox ⊆ C.closedBox ∧ b.n = C.n + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k))
    (hb' : ∃ C : DyBox, IsCell (approxLQG γ W ω) ((2 : ℝ)⁻¹ ^ k) C ∧
      b'.closedBox ⊆ C.closedBox ∧ b'.n = C.n + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k))
    (hNb : Neighbour b b') (hwm : b.Mem w)
    (hrat : epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 * b.side ≤ b'.side)
    (hdom : ∀ (c : ℚ × ℚ) (r : ℚ), Metric.ball (ratPt c) r ⊆ sqBox b.center (5 * b.side) →
      μ0 ω (Metric.ball (ratPt c) r) ≤ M b ω c r) :
    L53WData μ0 M u v (epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2) N ω b (b.closedBox ∩ b'.closedBox) w := by
  obtain ⟨C, hC, hbC, hbn⟩ := hb
  have hsz := hsize.2 C hC
  obtain ⟨a1, a2, -, -⟩ := corners_of_subset hbC
  have hb0 : (0 : ℝ) < b.side := DyBox.side_pos' b
  have hsb : b.side ≤ C.side := by nlinarith
  have hn1 := eq_of_safe_subset ⟨C, hC, hbC, hbn⟩ hb'
  have hn2 := eq_of_safe_subset hb' ⟨C, hC, hbC, hbn⟩
  have hfin := l53_iface_ne_top_of_nest hNb.1 hn1 hn2
  have hε0 := epsStar_pos' αs ((2 : ℝ)⁻¹ ^ k)
  have hε1 : epsStar αs ((2 : ℝ)⁻¹ ^ k) ≤ 1 := by
    unfold epsStar; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hε2 : epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
  refine ⟨by have := hN C hsz.1; omega, hwm.2, mem_closedBox_of_mem hwm, by nlinarith [hsz.2],
    ((isClosed_closedBox _).inter (isClosed_closedBox _)).measurableSet,
    l53_iface_sub_frontier_of_nest hNb.1 hn1 hn2, hfin,
    le_trans (le_min (by nlinarith) hrat) (l53_iface_ge_min_of_nest hn1 hn2 hNb hfin), hdom⟩

/-- `μH¹` of a dyadic square is infinite, so its real part vanishes. -/
lemma l53fn_real_closedBox (b : DyBox) : (μH[1] : Measure ℂ).real b.closedBox = 0 := by
  have hd : ((1 : NNReal) : ENNReal) < dimH b.closedBox := by
    rw [Real.dimH_of_nonempty_interior ⟨_, center_mem_interior_closedBox b⟩,
      Complex.finrank_real_complex]
    norm_num
  have h := hausdorffMeasure_of_lt_dimH hd
  rw [NNReal.coe_one] at h
  rw [measureReal_def, h, ENNReal.toReal_top]

/-- **The empty chain satisfies the `u`/`v` clauses** (its interfaces are the root square). -/
lemma l53fn_uv_nil (ν : Measure ℂ) (u v : ℂ) (δ T : ℝ) :
    l53UClause ν u δ T [] ∧ l53VClause ν v δ T [] := by
  have e1 : l53Iface [] 1 = DyBox.root.closedBox := by simp [l53Iface]
  have e0 : l53Iface [] ([] : List DyBox).length = DyBox.root.closedBox := by simp [l53Iface]
  refine ⟨⟨∅, empty_subset _, MeasurableSet.empty, ?_, by simp⟩,
    ⟨∅, empty_subset _, ?_, by simp⟩⟩
  · rw [e1, l53fn_real_closedBox]; simp
  · simp only [List.length_nil, Nat.zero_sub]
    rw [show l53Iface [] 0 = DyBox.root.closedBox by simp [l53Iface], l53fn_real_closedBox]
    simp

/-- **Node 4 at the selected chain** (DZZ l. 2516–2522; AUDIT-N N6 (ii), N7, N12): on
`E = l53E4 ∩ cellSizeEvent`, the `u`/`v` clauses of `𝒞(ω)` fail with probability `≤ 2(N+1) B`. -/
theorem l53fn_node4 {P : Measure Ω} [IsProbabilityMeasure P] {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ αs : ℝ} {u v : ℂ} {k l N : ℕ} {R : Set ℂ} {T₁ T : ℝ}
    (M : DyBox → Ω → ℚ × ℚ → ℚ → ℝ≥0∞)
    (hM : ∀ (b : DyBox) (c : ℚ × ℚ) (r : ℚ), Measurable fun ω => M b ω c r)
    (hN : ∀ C : DyBox, ((2 : ℝ)⁻¹ ^ k) ^ dzzCmc γ ≤ C.side →
      C.n + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) ≤ N)
    (hs : 12 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ ≤ ‖v - u‖) {B : ℝ≥0∞}
    (hbad : ∀ n ≤ N, ∀ w : ℂ, (w = u ∨ w = v) → 12 * (boxAt n w).side ≤ ‖v - u‖ →
      P (l53WBadQ (M (boxAt n w)) ((2 : ℝ)⁻¹ ^ (k + l)) T w (frontier (boxAt n w).closedBox)
        (ENNReal.ofReal (0.01 * epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 * (boxAt n w).side))) ≤ B)
    (hrat : ∀ ω : Ω, ∀ c : List DyBox,
      L313Q (epsStar αs ((2 : ℝ)⁻¹ ^ k)) u v
        (fun b => IsCell (approxLQG γ W ω) ((2 : ℝ)⁻¹ ^ k) b) c →
      ∀ i, i + 1 < c.length →
        epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 * (c.getD i root).side ≤ (c.getD (i + 1) root).side ∧
        epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 * (c.getD (i + 1) root).side ≤ (c.getD i root).side)
    (hdom : ∀ ω ∈ l53E4 hW γ ((2 : ℝ)⁻¹ ^ k) ∩ cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k),
      ∀ b ∈ l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω, (b.Mem u ∨ b.Mem v) →
      ∀ (c : ℚ × ℚ) (r : ℚ), Metric.ball (ratPt c) r ⊆ sqBox b.center (5 * b.side) →
        dzzMuIn γ W ω (Metric.ball (ratPt c) r) ≤ M b ω c r) :
    P (l53E4 hW γ ((2 : ℝ)⁻¹ ^ k) ∩ cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k) ∩
      {ω | ¬ (l53UClause (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u ((2 : ℝ)⁻¹ ^ (k + l)) T
          (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω) ∧
        l53VClause (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) v ((2 : ℝ)⁻¹ ^ (k + l)) T
          (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω))}) ≤
      2 * ((N + 1 : ℕ) : ℝ≥0∞) * B := by
  set E := l53E4 hW γ ((2 : ℝ)⁻¹ ^ k) ∩ cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k) with hE
  have hpos : 0 < ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ := by positivity
  have h := l53uf_uv_bound P (μ0 := dzzMuIn γ W) M (pow_pos (epsStar_pos' αs ((2 : ℝ)⁻¹ ^ k)) 2)
    (E := E ∩ {ω | l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω ≠ []}) (G := univ) (q := 0)
    (Adm := fun ω c => c = l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω)
    (δ := (2 : ℝ)⁻¹ ^ (k + l)) (T := T) hM hbad (by rw [compl_univ, measure_empty])
    ?_ ?_
  · rw [zero_add] at h
    refine le_trans (measure_mono ?_) h
    rintro ω ⟨hωE, hn⟩
    by_cases h0 : l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω = []
    · rw [mem_setOf_eq, h0] at hn
      exact absurd (l53fn_uv_nil (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v
        ((2 : ℝ)⁻¹ ^ (k + l)) T) hn
    · exact ⟨⟨hωE, h0⟩, _, rfl, hn⟩
  · rintro ω ⟨⟨hωE, hne0⟩, -⟩ c rfl
    have hQ := (l53Chain_spec hne0).1
    have hdω := hdom ω hωE
    generalize l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω = c at hQ hdω ⊢
    have hin := l53fn_safe hQ
    have hsize := hωE.2
    have h2 : 2 ≤ c.length := l53_two_le_length_box hsize hQ.1.1 hin
      (by rw [norm_sub_rev]; linarith)
    have hr := (hrat ω _ hQ 0 (by omega)).1
    obtain ⟨⟨hne, hu, -⟩, hchn⟩ := hQ.1
    have hNb := List.isChain_iff_getElem.1 hchn 0 (by omega)
    have e : l53Iface c 1 = c[0].closedBox ∩ c[0 + 1].closedBox := by
      unfold l53Iface; rw [l53_getD_eq _ (by omega), l53_getD_eq _ (by omega)]
    rw [l53_getD_eq _ (by omega), l53_getD_eq _ (by omega)] at hr
    rw [e, l53_getD_eq _ (by omega)]
    have hh : c.head hne = c[0] := List.head_eq_getElem hne
    exact l53fn_wdata hsize hN hs (hin _ (List.getElem_mem _)) (hin _ (List.getElem_mem _))
      hNb (hh ▸ hu) hr (hdω _ (List.getElem_mem _) (Or.inl (hh ▸ hu)))
  · rintro ω ⟨⟨hωE, hne0⟩, -⟩ c rfl
    have hQ := (l53Chain_spec hne0).1
    have hdω := hdom ω hωE
    generalize l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω = c at hQ hdω ⊢
    have hin := l53fn_safe hQ
    have hsize := hωE.2
    have h2 : 2 ≤ c.length := l53_two_le_length_box hsize hQ.1.1 hin
      (by rw [norm_sub_rev]; linarith)
    have hr := (hrat ω _ hQ (c.length - 2) (by omega)).2
    obtain ⟨⟨hne, -, hv⟩, hchn⟩ := hQ.1
    have hN0 := List.isChain_iff_getElem.1 hchn (c.length - 2) (by omega)
    have e1 : c.length - 2 + 1 = c.length - 1 := by omega
    have hNb : Neighbour c[c.length - 1] c[c.length - 2] := by
      simp only [e1] at hN0; exact hN0.symm
    have e : l53Iface c (c.length - 1) =
        c[c.length - 1].closedBox ∩ c[c.length - 2].closedBox := by
      unfold l53Iface
      rw [l53_getD_eq _ (by omega), l53_getD_eq _ (by omega), inter_comm]
      congr 3
    simp only [e1] at hr
    rw [l53_getD_eq _ (by omega), l53_getD_eq _ (by omega)] at hr
    rw [e, l53_getD_eq _ (by omega)]
    have hl : c.getLast hne = c[c.length - 1] := List.getLast_eq_getElem hne
    exact l53fn_wdata hsize hN hs (hin _ (List.getElem_mem _)) (hin _ (List.getElem_mem _))
      hNb (hl ▸ hv) hr (hdω _ (List.getElem_mem _) (Or.inr (hl ▸ hv)))

end DZZ
end LQGMetric
