/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53L7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53P2

/-!
# DZZ Lemma 5.3, part 1: P-131A remainder — `L53RefineB` (P2-DZZ53LR)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2366–2379, l. 1327–1336.
**`l53RefineB_of_pos`**: the refinement hypothesis `L53RefineB` of P2-DZZ53P's adapter
(S5L53P2) holds for every `α* > 0`: `l53D1EventR_subset_l53D1EventB_gen` (S5L53L6) with
`R' = cthickening (2 δ^{C_Mc}) R` and `4^{2 n_{ε*}} ≤ e^{(log δ⁻¹)^{0.6}}` (`l313_len_asym`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **`L53RefineB` holds** (DEC-131 §2, P-131A, in the form of S5L53P2). -/
theorem l53RefineB_of_pos {Ω : Type*} [MeasurableSpace Ω] {W : WNSpace → Ω → ℝ} {αs : ℝ}
    (hαs : 0 < αs) (γ : ℝ) : L53RefineB γ W αs := by
  obtain ⟨δ₁, hδ₁, h⟩ := l53D1EventR_subset_l53D1EventB_gen (W := W) hαs γ
  obtain ⟨δ₂, hδ₂, hA⟩ := l313_len_asym hαs
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ u v R T => ?_⟩
  have hδ1 : δ ∈ Ioo 0 δ₁ := ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩
  have hδ2 : δ ∈ Ioo 0 δ₂ := ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩
  refine h δ hδ1 u v R _ T _ subset_rfl ?_
  rw [Real.exp_add]
  exact mul_le_mul_of_nonneg_left (hA δ hδ2).2 (Real.exp_pos _).le

end DZZ
end LQGMetric
