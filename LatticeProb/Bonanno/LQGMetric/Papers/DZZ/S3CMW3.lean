/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CMW3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CMW1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CMW2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM8

/-!
# Walled DZZ crude moments `DZZCrudeMomentsEvOn` at `dzzWall K μIn` (P2-DZZMOMW)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-very-crude-prime), (eq-very-crude), l. 849–857,
for the walled LGD (Remark 5.2, l. 2281–2284) and the walled approximate distance
`approxLGDSetOn S`, for `ξ`-admissible pairs inside `K^ξ` (DZZ l. 1521: "the general case follows
by the same proof"). Decisions D117/D123, packet P-317K-MOM. The proof is a copy of
`dzzCrudeMomentsEv_dzzMuIn` (P2-DZZCM, S3CM8) with the walled second moments
`lintegral_sq_logMin_dzzWall_le` (S3CMW2) and `lintegral_sq_logApproxLGDOn_le` (S3CMW1).

* **`dzzCrudeMomentsEvOn_dzzMuIn`**: for every convex `K` and every cell family `S`;
* **`dzzCrudeMomentsEvOn_inside`**: the dyadic wall `K = B̄`, `S = cellsInside B` (D123);
* **`dzzCrudeMomentsEvOn_meeting`**: convex `K`, `S = cellsMeeting K` (D117).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **Walled DZZ (eq-very-crude), (eq-very-crude-prime) at `dzzWall K μIn`** for a convex wall
`K`, any cell family `S`, `ξ`-admissible pairs inside `K^ξ`, small `δ` (copy of
`dzzCrudeMomentsEv_dzzMuIn`). -/
theorem dzzCrudeMomentsEvOn_dzzMuIn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {K : Set ℂ} (hK : Convex ℝ K) (S : Set DyBox) {ξ : ℝ} (hξ : 0 < ξ) :
    DZZCrudeMomentsEvOn P γ W K S (fun ω => dzzWall K (dzzMuIn γ W ω)) ξ := by
  obtain ⟨a₁, b₁, ha₁, hb₁, h1⟩ := lintegral_sq_logMin_dzzWall_le (P := P) hW hγ hγ2 hξ
  obtain ⟨a₂, b₂, ha₂, hb₂, h2⟩ := lintegral_sq_logApproxLGDOn_le (P := P) hW hγ hγ2
  have hμm : ∀ (c : ℂ) (r : ℝ),
      AEMeasurable (fun ω => dzzWall K (dzzMuIn γ W ω) (ball c r)) P := fun c r => by
    simp only [dzzWall, dzzMuIn, Measure.add_apply, Measure.smul_apply]
    exact ((aemeasurable_wickQArea_ball hW hγ hγ2 c r).add aemeasurable_const).add
      aemeasurable_const
  intro A B hAB hKin
  have he : Real.exp (-1) < 1 / 2 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  refine ⟨a₁ + b₁ + (a₂ + b₂), Real.exp (-1), Real.exp_pos _, fun δ hδ => ?_⟩
  have hδ1 : δ < 1 := hδ.2.trans (he.trans (by norm_num))
  have hL := cm_one_le_log_inv hδ.1 hδ.2
  set L := Real.log δ⁻¹ with hLdef
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hfin : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b * L ^ 2 ≤ (a + b) * L ^ 2 := fun a b ha hb => by
    nlinarith
  have hδI : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, hδ1⟩
  obtain ⟨u, hu⟩ := cm_nonempty_of_adm (hAB.adm_left δ hδI)
  obtain ⟨v, hv⟩ := cm_nonempty_of_adm (hAB.adm_right δ hδI)
  have hu' : u ∈ dzzVIn ξ := dzzVXi_sub_dzzVIn le_rfl (hAB.subset_left δ hδI hu)
  have hv' : v ∈ dzzVIn ξ := dzzVXi_sub_dzzVIn le_rfl (hAB.subset_right δ hδI hv)
  have huv : u ≠ v := by
    intro h
    have := hAB.dist_ge δ hδI u hu v hv
    rw [h, dist_self] at this
    linarith
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ball (AffineMap.lineMap u v t) (ξ / 2) ⊆ K := fun t ht =>
    (ball_subset_ball (half_le_self hξ.le)).trans
      (cmw_ball_lineMap_sub hK ((hKin δ hδI).1 hu) ((hKin δ hδI).2 hv) ht)
  have hX := memLp_two_of_lintegral_sq (fun ω => logMinLGD_nonneg _ _ _ _)
    (aemeasurable_logMinLGD hμm δ (A δ) (B δ)) (by positivity)
    (h1 K (A δ) (B δ) u v hu hv hu' hv' huv hseg δ hδ.1 (hδ.2.trans he).le)
  have hY := memLp_two_of_lintegral_sq (fun ω => logApproxLGDOn_nonneg S γ W δ (A δ) (B δ) ω)
    (measurable_logApproxLGDOn hW S γ δ (A δ) (B δ)).aemeasurable (by positivity)
    (h2 S (A δ) (B δ) δ hδ.1 hδ1)
  refine ⟨⟨hX.1, hX.2.trans ((hfin a₁ b₁ ha₁ hb₁).trans ?_)⟩,
    ⟨hY.1, hY.2.trans ((hfin a₂ b₂ ha₂ hb₂).trans ?_)⟩⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **P-317K-MOM (D123)**: the walled crude moments for a dyadic wall `B̄` and the cells inside
it. -/
theorem dzzCrudeMomentsEvOn_inside {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (B : DyBox) {ξ : ℝ} (hξ : 0 < ξ) :
    DZZCrudeMomentsEvOn P γ W B.closedBox (cellsInside B)
      (fun ω => dzzWall B.closedBox (dzzMuIn γ W ω)) ξ :=
  dzzCrudeMomentsEvOn_dzzMuIn hW hγ hγ2 (convex_closedBox B) _ hξ

/-- The walled crude moments for a convex wall `K` and the cells meeting it (D117). -/
theorem dzzCrudeMomentsEvOn_meeting {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {K : Set ℂ} (hK : Convex ℝ K) {ξ : ℝ} (hξ : 0 < ξ) :
    DZZCrudeMomentsEvOn P γ W K (cellsMeeting K) (fun ω => dzzWall K (dzzMuIn γ W ω)) ξ :=
  dzzCrudeMomentsEvOn_dzzMuIn hW hγ hγ2 hK _ hξ

end DZZ
end LQGMetric
