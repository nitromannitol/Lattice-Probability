/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13Cov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Main
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Good
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XCell
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XBridge

/-!
# DZZ Lemma 3.13: the white-noise disjointness from cell sizes near the boxes (P2-DZZ313)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1334–1340: DZZ derive
(Eq.fine-field-independent) from `s_B log(1/s_B) < ε* s_𝖢 / 10` and the goodness of the cell sequence,
i.e. from the fact that all cells near `B` are not smaller than `B`. This file proves that implication
(`disjoint_boxReg_fineReg_of_cov`, own elementary proof): if every point of `𝕍` within distance
`ρ(s_B) = (s_B log s_B⁻² + 2 s_B)/2` (twice the range `r(·)` of the fine field) of `B_large` lies in a
cell of side `≥ s_B`, then no box explored by the partition reads the white noise of the fine field of
`B` (a smaller explored box near `B` would contain the centre of a cell smaller than `B`; a box at
least as large as `B` reads only times `> s_B²`).

`L313GeomC` is the remaining (purely cell-geometric) node: the construction of the box sequence,
DZZ l. 1327–1334; `dzz_lemma313_of_geomC : L313GeomC → DZZLemma313`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- `ρ(s) = (s log s⁻² + 2 s)/2`, twice the bound of the radius `r(t)`, `t < s²`. -/
def l313Rho (s : ℝ) : ℝ := (s * Real.log (s ^ 2)⁻¹ + 2 * s) / 2

lemma two_etaRad_le_rho (b : DyBox) {t : ℝ} (ht : t ∈ Ioo 0 (b.side ^ 2)) :
    2 * etaRad t ≤ l313Rho b.side := by
  have hs := side_pos' b
  have hs1 : b.side ≤ 1 := by unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)
  have h := etaRad_le_of_le ht.1 ht.2.le (pow_le_one₀ hs.le hs1)
  rw [Real.sqrt_sq hs.le] at h
  unfold l313Rho; linarith

/-- **Disjointness from the cell sizes near the boxes.** -/
theorem disjoint_boxReg_fineReg_of_cov (m : DyBox → ℝ) (δ : ℝ) (l : List DyBox)
    (hcov : ∀ b ∈ l, ∀ x ∈ b.largeBox, ∀ z ∈ dzzV, dist z x < l313Rho b.side →
      b.side ≤ cellSide m δ z)
    (b' : DyBox) (hb' : Explored (IsCell m δ) b') : Disjoint (boxReg b') (fineReg l) := by
  rw [Set.disjoint_left]
  rintro q ⟨hq1, hq2⟩ ⟨b, hb, x, hx, hqt, hqx⟩
  have hsb' := side_pos' b'
  have hsb := side_pos' b
  have hlt : b'.side < b.side :=
    (pow_lt_pow_iff_left₀ hsb'.le hsb.le two_ne_zero).1 ((mem_Ioi.1 hq1).trans hqt.2)
  have hd : dist b'.center x < l313Rho b.side := by
    rw [Metric.mem_ball] at hq2 hqx
    calc dist b'.center x ≤ dist q.2 b'.center + dist q.2 x := dist_triangle_left _ _ _
      _ < etaRad q.1 + etaRad q.1 := add_lt_add hq2 hqx
      _ = 2 * etaRad q.1 := by ring
      _ ≤ _ := two_etaRad_le_rho b hqt
  have hz : b'.center ∈ dzzV := closedBox_sub_dzzV' b' (center_mem_closedBox' b')
  have hcs := hcov b hb x hx _ hz hd
  by_cases hex : ∃ C, IsCell m δ C ∧ C.Mem b'.center
  · obtain ⟨C, hC, hCz⟩ := hex
    rw [cellSide_eq_of_isCell hC hCz] at hcs
    by_cases hn : C.n < b'.n
    · have e : b'.anc C.n = C := by
        rw [← boxAt_center (s := b') rfl, anc_boxAt hn.le, hCz.2]
      exact hb' C.n hn (by rw [e]; exact hC)
    · have : C.side ≤ b'.side := by
        unfold DyBox.side
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (not_lt.1 hn)
      linarith
  · unfold cellSide at hcs
    simp only [hex, ↓reduceDIte] at hcs
    linarith

end DZZ
end LQGMetric
