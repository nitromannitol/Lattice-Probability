/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53GB4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53GB1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53GB3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J10
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J12

/-!
# DZZ Lemma 5.3, node 3: desirability of one chain box, dyadic grid (P2-DZZ53GB, G-J3)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2425–2514 ("partition `𝖢_i` into `K²` many dyadic
squares with side length `s_i/K`" … "each cell `𝖢_i` is desirable with probability
`1 - e^{-Ω(2^{√log δ⁻¹})}`"); DEC-131 §4; DEC-131-IF §3 G-J3.

**`l53_box_desirable_prob`**: `l53_cell_desirable_prob_on` (S5L53GB1) instantiated at a chain
box `𝖢` with
* the `K × K` sub-box grid `l53Sub 𝖢 κ N` (S5L53J9; `2^κ = 2N + 2`), sites `l53EvenBox N`,
  depths `l53EvenTb` (S5L53J7);
* `Bd z = ∂𝖡̄_z`, `I x y = 𝖡̄_x ∩ 𝖡̄_y` (`l53_sub_hI`, `l53_sub_hIc`, `l53_sub_hBdc`),
  `seg p = 𝖡̄_{site p} ∩ ∂𝖢̄` (`l53CellSeg`, S5L53J12; `l53_seg_subset_frontier`,
  `l53_sub_seg_le`, S5L53J10);
* the measure `P[· | A₀]`, the bad events `l53ZBadQ (M z) … (K̃⁻¹ μH¹(∂𝖡̄_z))` of the mass maps
  `M z` local to `(0, s²) × 𝕍_{c_z, 7t}`, range `r = 7` (`l53_sub_region_disjoint`,
  `l53_cond_biInter`, S5L53G3), openness on `E` from the domination (`l53_hopen_of_not_badQ`,
  S5L53Q1, `l53_hopen_uniform`, S5L53J10) with uniform thresholds `a = b = K̃⁻¹ · 4t`.
Left as hypotheses: the per-site bound `hε` (from `l53_bad_cond_proxy`, S5L53Y4), the
domination `hdom` on `E` (from `l53_domination`, S5L53Z3), and the interface data
`Prev`, `Next`, `Λprev`, `Λnext` with the covering inequalities (the coverage of `l53Iface`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The boundary segment of `∂𝖢̄` carried by the boundary site of `p`: `l53CellSeg` (S5L53J12)
on the grid, empty off it (the hypothesis `hseg` of `l53_cell_desirable_prob` quantifies over
all `p`; `l53SubSeg_eq_cellSeg` is the bridge). -/
def l53SubSeg (C : DyBox) (κ N n : ℕ) (p : PercDir × ℤ) : Set ℂ :=
  if l53Col n N p.1 p.2 (l53EvenTb n N p.1) ∈ l53EvenBox N then
    (l53Sub C κ N (l53Col n N p.1 p.2 (l53EvenTb n N p.1))).closedBox ∩ frontier C.closedBox
  else ∅

lemma l53SubSeg_eq_cellSeg (C : DyBox) {κ N n : ℕ} (hnN : n ≤ N) {p : PercDir × ℤ}
    (h1 : (N : ℤ) - n < p.2) (h2 : p.2 < N + n) : l53SubSeg C κ N n p = l53CellSeg C κ n N p := by
  have hmem : l53Col n N p.1 p.2 (l53EvenTb n N p.1) ∈ l53EvenBox N :=
    l53_even_hcolB n N hnN p.1 p.2 h1 h2 _ (by have := (l53_even_htb n N p.1).1; omega) le_rfl
  simp only [l53SubSeg, hmem, ite_true, l53CellSeg]

lemma l53_biUnion_subSeg (C : DyBox) {κ N n : ℕ} (hnN : n ≤ N) (F : Finset (PercDir × ℤ))
    (hF : ∀ p ∈ F, (N : ℤ) - n < p.2 ∧ p.2 < N + n) :
    (⋃ p ∈ F, l53SubSeg C κ N n p) = ⋃ p ∈ F, l53CellSeg C κ n N p :=
  iUnion₂_congr fun p hp => l53SubSeg_eq_cellSeg C hnN (hF p hp).1 (hF p hp).2

/-- **G-J3: one chain box is desirable with high probability, on `E`, under `P[· | A₀]`**
(DZZ l. 2425–2514). -/
theorem l53_box_desirable_prob (hW : IsWhiteNoise P W) (C : DyBox) {κ N n : ℕ}
    (hK : 2 ^ κ = 2 * N + 2) (hn : 1 ≤ n) (hnN : n ≤ N)
    (M : ℤ × ℤ → Ω → ℚ × ℚ → ℚ → ℝ≥0∞) (s : ℝ)
    (hloc : ∀ z ∈ l53EvenBox N, ∀ (c : ℚ × ℚ) (q : ℚ), Measurable[wnSigma W
      (Ioo 0 (s ^ 2) ×ˢ sqBox (l53Sub C κ N z).center (7 * (l53Sub C κ N z).side))]
        fun ω => M z ω c q)
    {R₀ : Set (ℝ × ℂ)} {A₀ : Set Ω} (hA₀ : MeasurableSet[wnSigma W R₀] A₀) (h0 : P A₀ ≠ 0)
    (hR₀ : ∀ z ∈ l53EvenBox N, Disjoint R₀
      (Ioo 0 (s ^ 2) ×ˢ sqBox (l53Sub C κ N z).center (7 * (l53Sub C κ N z).side)))
    (δ T : ℝ) {Kt : ℝ≥0∞} (hK8 : 8 ≤ Kt)
    {ε θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹) (hεθ : ε ≤ θ ^ ((7 + 1) ^ 2))
    (hε : ∀ z ∈ l53EvenBox N, P[l53ZBadQ (M z) δ T (frontier (l53Sub C κ N z).closedBox)
      (Kt⁻¹ * μH[1] (frontier (l53Sub C κ N z).closedBox))
      (Kt⁻¹ * μH[1] (frontier (l53Sub C κ N z).closedBox)) | A₀] ≤ ε)
    (j : ℕ) (E : Set Ω) (ν : Ω → Measure ℂ) (Kw : Set ℂ)
    (hKw : ∀ z ∈ l53EvenBox N,
      sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side) ⊆ Kw)
    (hdom : ∀ ω ∈ E, ∀ z ∈ l53EvenBox N, ∀ (c : ℚ × ℚ) (q : ℚ),
      Metric.ball (ratPt c) q ⊆ sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side) →
        ν ω (Metric.ball (ratPt c) q) ≤ M z ω c q)
    (Prev Next : Finset (PercDir × ℤ))
    (hrange : ∀ p, (p ∈ Prev ∨ p ∈ Next) → (N : ℤ) - n < p.2 ∧ p.2 < N + n)
    {Λprev Λnext : Set ℂ} (hΛp : μH[1] Λprev ≠ ⊤) (hΛn : μH[1] Λnext ≠ ⊤)
    (hPrev : ∀ p ∈ Prev, l53CellSeg C κ n N p ⊆ Λprev)
    (hNext : ∀ p ∈ Next, l53CellSeg C κ n N p ⊆ Λnext)
    (hcovP : 0.2 * (μH[1] : Measure ℂ).real Λprev + 4 * (7 + 1) * j * (4 * (2 : ℝ)⁻¹ ^ (C.n + κ))
      ≤ (μH[1] : Measure ℂ).real (⋃ p ∈ Prev, l53CellSeg C κ n N p))
    (hcardP : (Prev.card : ℝ) * (Kt⁻¹ * (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + κ)))).toReal ≤
      0.1 * (μH[1] : Measure ℂ).real Λprev)
    (hcovN : (μH[1] : Measure ℂ).real (Λnext \ ⋃ p ∈ Next, l53CellSeg C κ n N p) +
      Next.card * (Kt⁻¹ * (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + κ)))).toReal +
        4 * (7 + 1) * j * (4 * (2 : ℝ)⁻¹ ^ (C.n + κ)) < 0.1 * (μH[1] : Measure ℂ).real Λnext) :
    P[E ∩ {ω | ¬ L53DesClause (μH[1] : Measure ℂ) (dzzWall Kw (ν ω)) δ
        (T + Real.log ((((2 * N + 2) ^ 2 : ℕ) : ℝ) + 1)) Λprev Λnext} | A₀] ≤
      4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) +
        4 * (7 + 1) * (((2 * N + 1).choose j : ℝ≥0∞) * (((N - n + 2 : ℕ) : ℝ≥0∞) * ε) ^ j) := by
  classical
  have := hW.isProbabilityMeasure
  set t : ℝ := (2 : ℝ)⁻¹ ^ (C.n + κ) with ht
  have ht0 : 0 < t := by positivity
  have hK0 : Kt ≠ 0 := (lt_of_lt_of_le (by norm_num) hK8).ne'
  set Sub := l53Sub C κ N with hSub
  set Bd : ℤ × ℤ → Set ℂ := fun z => frontier (Sub z).closedBox with hBd
  set Bad : ℤ × ℤ → Set Ω := fun z => l53ZBadQ (M z) δ T (Bd z) (Kt⁻¹ * μH[1] (Bd z))
    (Kt⁻¹ * μH[1] (Bd z)) with hBad
  set R : ℤ × ℤ → Set (ℝ × ℂ) :=
    fun z => Ioo 0 (s ^ 2) ×ˢ sqBox (Sub z).center (7 * (Sub z).side) with hR
  set a : ℝ≥0∞ := Kt⁻¹ * (4 * ENNReal.ofReal t) with ha
  have ha_top : a ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hK0) (ENNReal.mul_ne_top (by norm_num)
      ENNReal.ofReal_ne_top)
  have hac : a + a ≤ ENNReal.ofReal t := by
    have h1 : Kt⁻¹ ≤ 8⁻¹ := ENNReal.inv_le_inv.2 hK8
    have h2 : a + a = (8 * Kt⁻¹) * ENNReal.ofReal t := by rw [ha]; ring
    rw [h2]
    calc 8 * Kt⁻¹ * ENNReal.ofReal t ≤ 8 * 8⁻¹ * ENNReal.ofReal t := by gcongr
      _ = ENNReal.ofReal t := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hmeas : ∀ z ∈ l53EvenBox N, MeasurableSet[wnSigma W (R z)] (Bad z) := fun z hz =>
    @measurableSet_l53ZBadQ Ω (wnSigma W (R z)) (M z) (hloc z hz) δ T (Bd z)
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        (l53_frontier_closedBox_le _)) _ _
  have hind := l53_hind_of_prod (P[|A₀]) (l53EvenBox N) Bad 7 R hR₀
    (fun x hx y hy hxy => l53_sub_region_disjoint C hK hx hy hxy s)
    (fun F hF hRF hR₀F => l53_cond_biInter hW F hRF hR₀F hA₀ h0 fun i hi => hmeas i (hF i hi))
  have hopen : ∀ ω ∈ E, ∀ x ∈ l53EvenBox N, ω ∉ Bad x → ∀ Λ ⊆ Bd x, a ≤ μH[1] Λ →
      ∃ z ∈ Λ, μH[1] {z' ∈ Bd x | ¬ lgdLeExp (dzzWall Kw (ν ω)) δ T z z'} ≤ a := by
    intro ω hω x hx hbad
    have hBs : ∀ z ∈ Bd x, ∀ z' ∈ Bd x, z ≠ z' →
        tildeBox z z' ⊆ sqBox (Sub x).center (5 * (Sub x).side) := by
      intro z hz z' hz' hne
      have h1 := (isClosed_closedBox (Sub x)).frontier_subset hz
      have h2 := (isClosed_closedBox (Sub x)).frontier_subset hz'
      rw [closedBox_eq_sqBox] at h1 h2
      exact tildeBox_subset_sqBox_five h1 h2 hne
    have h := l53_hopen_of_not_badQ (ν := ν) (K := Kw) isClosed_frontier.measurableSet hbad
      (hdom ω hω x hx) hBs (fun z hz z' hz' hne => (hBs z hz z' hz' hne).trans (hKw x hx))
    exact l53_hopen_uniform (l53_sub_frontier_le C κ N x) h
  have hseg : ∀ p, l53SubSeg C κ N n p ⊆ Bd (l53Col n N p.1 p.2 (l53EvenTb n N p.1)) := by
    intro p
    unfold l53SubSeg
    split_ifs with hp
    · exact l53_seg_subset_frontier (l53_sub_subset C hK hp)
    · exact empty_subset _
  have hσ : ∀ p, (μH[1] : Measure ℂ).real (l53SubSeg C κ N n p) ≤ 4 * t := by
    intro p
    unfold l53SubSeg
    split_ifs with hp
    · exact l53_sub_seg_le C hK hp
    · simp only [measureReal_empty]; positivity
  have hP' : ∀ p ∈ Prev, (N : ℤ) - n < p.2 ∧ p.2 < N + n := fun p hp => hrange p (Or.inl hp)
  have hN' : ∀ p ∈ Next, (N : ℤ) - n < p.2 ∧ p.2 < N + n := fun p hp => hrange p (Or.inr hp)
  rw [← l53_biUnion_subSeg C hnN Prev hP'] at hcovP
  rw [← l53_biUnion_subSeg C hnN Next hN'] at hcovN
  have hPrev' : ∀ p ∈ Prev, l53SubSeg C κ N n p ⊆ Λprev := fun p hp => by
    rw [l53SubSeg_eq_cellSeg C hnN (hP' p hp).1 (hP' p hp).2]; exact hPrev p hp
  have hNext' : ∀ p ∈ Next, l53SubSeg C κ N n p ⊆ Λnext := fun p hp => by
    rw [l53SubSeg_eq_cellSeg C hnN (hN' p hp).1 (hN' p hp).2]; exact hNext p hp
  have hmain := l53_cell_desirable_prob_on (P[|A₀]) n N hn hnN (l53EvenBox N) (l53_even_hBox N)
    (l53EvenTb n N) (l53_even_htb n N) (l53_even_hcolB n N hnN) Bad 7 hθ hεθ hε hind j E
    (μH[1] : Measure ℂ) (fun ω => dzzWall Kw (ν ω)) (δ := δ) (T := T) Bd
    (fun x y => (Sub x).closedBox ∩ (Sub y).closedBox) ha_top ha_top hac
    (l53_sub_hI C hK) (l53_sub_hIc C hK) (fun x _ => l53_sub_hBdc C κ N x) hopen
    (l53SubSeg C κ N n) hseg Prev Next hrange hΛp hΛn hPrev' hNext' (by positivity) hσ hcovP
    hcardP hcovN
  rwa [card_l53EvenBox] at hmain

end DZZ
end LQGMetric
