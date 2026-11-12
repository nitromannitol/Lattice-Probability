/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CM8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B1

/-!
# DZZ crude moments at `μIn` (P2-DZZCM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-very-crude-prime), (eq-very-crude), l. 849–857,
for `ξ`-admissible pairs of sets (DZZ l. 1521: "the general case follows by the same proof"):

* **`dzzCrudeMomentsEv_dzzMuIn`**: `DZZCrudeMomentsEv P γ W (dzzMuIn γ W) ξ` for `ξ > 0`
  (from `lintegral_sq_logApproxLGD_le`, S3CM3, and `lintegral_sq_logMin_dzzMuIn_le`, S3CM6);
With `dzzProp317_of_approxEv` (S3CM7) and `dzz_prop32U_dzzMuIn` (S3P32G6) this gives DZZ
Prop 3.17 at `μIn` from `DZZConcApprox` alone. That composition cannot be compiled yet: the
import chain of S3P32G6 (through S3P32Z2) and that of `DG.dgL38Upper_muHU` (through
`DG.S3D105A`, `DZZ.S2L12Chain`) both declare `LQGMetric.DZZ.exists_grid_near`
(S3P32Z2 l. 30, S2L12Chain l. 99), so no module can import both.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

lemma cm_nonempty_of_adm {ξ δ : ℝ} {A : Set ℂ} (h : IsXiAdmissibleSet ξ δ A) : A.Nonempty := by
  rcases h with ⟨a, rfl⟩ | ⟨hc, -⟩
  · exact singleton_nonempty a
  · exact hc.nonempty

/-- `L ≥ 1` for `δ < e⁻¹` -/
lemma cm_one_le_log_inv {δ : ℝ} (hδ : 0 < δ) (hδe : δ < Real.exp (-1)) : 1 ≤ Real.log δ⁻¹ := by
  rw [Real.log_inv]
  have := Real.log_lt_log hδ hδe
  rw [Real.log_exp] at this
  linarith

/-- **DZZ (eq-very-crude), (eq-very-crude-prime) at `μIn`** for `ξ`-admissible pairs of sets,
for small `δ`. -/
theorem dzzCrudeMomentsEv_dzzMuIn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ : ℝ} (hξ : 0 < ξ) : DZZCrudeMomentsEv P γ W (dzzMuIn γ W) ξ := by
  obtain ⟨a₁, b₁, ha₁, hb₁, h1⟩ := lintegral_sq_logMin_dzzMuIn_le (P := P) hW hγ hγ2 hξ
  obtain ⟨a₂, b₂, ha₂, hb₂, h2⟩ := lintegral_sq_logApproxLGD_le (P := P) hW hγ hγ2
  have hμm : ∀ (c : ℂ) (r : ℝ), AEMeasurable (fun ω => dzzMuIn γ W ω (ball c r)) P :=
    fun c r => by
      simp only [dzzWall, dzzMuIn, Measure.add_apply, Measure.smul_apply]
      exact (aemeasurable_wickQArea_ball hW hγ hγ2 c r).add aemeasurable_const
  intro A B hAB
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
  have hX := memLp_two_of_lintegral_sq (fun ω => logMinLGD_nonneg _ _ _ _)
    (aemeasurable_logMinLGD hμm δ (A δ) (B δ)) (by positivity)
    (h1 (A δ) (B δ) u v hu hv hu' hv' huv δ hδ.1 (hδ.2.trans he).le)
  have hY := memLp_two_of_lintegral_sq (fun ω => logApproxLGD_nonneg γ W δ (A δ) (B δ) ω)
    (measurable_logApproxLGD hW γ δ (A δ) (B δ)).aemeasurable (by positivity)
    (h2 (A δ) (B δ) δ hδ.1 hδ1)
  refine ⟨⟨hX.1, hX.2.trans ((hfin a₁ b₁ ha₁ hb₁).trans ?_)⟩,
    ⟨hY.1, hY.2.trans ((hfin a₂ b₂ ha₂ hb₂).trans ?_)⟩⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end DZZ
end LQGMetric
