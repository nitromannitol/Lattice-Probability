/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistSFub at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistKerId

/-!
# Deterministic half of the stochastic Fubini step (task P2-EXIST)

`integral_d12_mul_inner_rectL2`: `∫ ∂_re ∂_im φ(x) ⟪rectL2 x, G⟫ dx = ∫ kerFun φ · G` for every
`G ∈ L²(ℝ × ℂ)` (Fubini over `ℂ × (ℝ × ℂ)` and `integral_d12_mul_kerFun`). Together with the
covariance of the white noise this gives `∫ F ∂_re ∂_im φ = W(kerFun φ)` a.s. Own elementary
proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace LQGMetric
namespace GFFExist

open WhiteNoise

lemma sgnInd_zero_left (b : ℝ) : sgnInd 0 b = 0 := by
  unfold sgnInd
  have h : ¬ (0 < b ∧ b ≤ 0) := fun h => absurd (h.1.trans_le h.2) (lt_irrefl _)
  simp [h]

lemma rectInd_zero (u : ℂ) : rectInd 0 u = 0 := by
  simp [rectInd, sgnInd_zero_left]

lemma integral_sq_kerFun_rect_le {x : ℂ} {L : ℝ} (hx : ‖x‖ ≤ L) :
    ∫ q, kerFun (rectInd x) q ^ 2 ≤ (2 * Real.pi + 32 * L ^ 4) * (4 * L * L) := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hx
  have h := integral_sq_kerFun_rect_sub_le (x := x) (x' := 0) (A := L)
    ((Complex.abs_re_le_norm x).trans hx) ((Complex.abs_im_le_norm x).trans hx) (by simpa using hL)
    (by simpa using hL)
  have e : (fun u => rectInd x u - rectInd 0 u) = rectInd x := by
    funext u; rw [rectInd_zero, sub_zero]
  rw [e, sub_zero] at h
  refine h.trans ?_
  gcongr

lemma measurable_kerFun_rect : Measurable fun p : ℂ × (ℝ × ℂ) => kerFun (rectInd p.1) p.2 := by
  have hK : Measurable fun p : ℂ × (ℝ × ℂ) => kerInner (rectInd p.1) p.2.1 p.2.2 := by
    unfold kerInner
    refine (StronglyMeasurable.integral_prod_right' (f := fun z : (ℂ × (ℝ × ℂ)) × ℂ =>
      rectInd z.1.1 z.2 * (heatKernel (z.1.2.1 / 2) z.2 z.1.2.2 - (Ioi (1 : ℝ)).indicator
        (fun _ => heatKernel (z.1.2.1 / 2) 0 z.1.2.2) z.1.2.1)) ?_).measurable
    refine Measurable.stronglyMeasurable ?_
    refine (measurable_rectInd₂.comp ((measurable_fst.comp measurable_fst).prodMk
      measurable_snd)).mul ((by unfold heatKernel; fun_prop : Measurable fun z :
        (ℂ × (ℝ × ℂ)) × ℂ => heatKernel (z.1.2.1 / 2) z.2 z.1.2.2).sub ?_)
    have e : (fun z : (ℂ × (ℝ × ℂ)) × ℂ => (Ioi (1 : ℝ)).indicator
        (fun _ => heatKernel (z.1.2.1 / 2) 0 z.1.2.2) z.1.2.1) =
        {z : (ℂ × (ℝ × ℂ)) × ℂ | 1 < z.1.2.1}.indicator
          (fun z => heatKernel (z.1.2.1 / 2) 0 z.1.2.2) := by
      funext z; simp [indicator]
    rw [e]
    exact (by unfold heatKernel; fun_prop : Measurable fun z : (ℂ × (ℝ × ℂ)) × ℂ =>
      heatKernel (z.1.2.1 / 2) 0 z.1.2.2).indicator
      (measurableSet_lt measurable_const (by fun_prop))
  have e : (fun p : ℂ × (ℝ × ℂ) => kerFun (rectInd p.1) p.2) = fun p => Real.sqrt Real.pi *
      {p : ℂ × (ℝ × ℂ) | 0 < p.2.1}.indicator
        (fun p => kerInner (rectInd p.1) p.2.1 p.2.2) p := by
    funext p; simp [kerFun, indicator]
  rw [e]
  exact measurable_const.mul (hK.indicator (measurableSet_lt measurable_const (by fun_prop)))

lemma inner_rectL2_eq (x : ℂ) (G : WNSpace) :
    ⟪rectL2 x, G⟫ = ∫ q, kerFun (rectInd x) q * G q := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_rectL2 x] with q h1
  rw [h1, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

/-- **Fubini against the rectangle kernels.** -/
theorem integral_d12_mul_inner_rectL2 (φ : TestC) (G : WNSpace) :
    ∫ x, d12 φ x * ⟪rectL2 x, G⟫ = ∫ q, kerFun φ q * G q := by
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish (d12 φ)
  set Ck := (2 * Real.pi + 32 * L ^ 4) * (4 * L * L) with hCk
  have hG2 : Integrable fun q => G q ^ 2 := (Lp.memLp G).integrable_sq
  set F : ℂ × (ℝ × ℂ) → ℝ := fun p => d12 φ p.1 * kerFun (rectInd p.1) p.2 * G p.2 with hF
  have hFm : AEStronglyMeasurable F (volume.prod volume) :=
    ((((d12 φ).continuous.measurable.comp measurable_fst).mul
      measurable_kerFun_rect).aestronglyMeasurable).mul (Lp.aestronglyMeasurable G).comp_snd
  have hslice : ∀ x, Integrable fun q => kerFun (rectInd x) q * G q := fun x =>
    ((rectInd_bddSupp x).memLp_kerFun.1.integrable_mul (Lp.memLp G))
  have hbd : ∀ x, ∫ q, ‖kerFun (rectInd x) q‖ * ‖G q‖ ≤
      ((∫ q, kerFun (rectInd x) q ^ 2) + ∫ q, G q ^ 2) / 2 := by
    intro x
    have h1 := (rectInd_bddSupp x).memLp_kerFun.1.integrable_sq
    calc ∫ q, ‖kerFun (rectInd x) q‖ * ‖G q‖
        ≤ ∫ q, (kerFun (rectInd x) q ^ 2 + G q ^ 2) / 2 := by
          refine integral_mono ((hslice x).norm.congr (Eventually.of_forall fun q => norm_mul _ _))
            ((h1.add hG2).div_const _) fun q => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|kerFun (rectInd x) q| - |G q|), sq_abs (kerFun (rectInd x) q),
            sq_abs (G q)]
      _ = _ := by rw [integral_div, integral_add h1 hG2]
  have hFi : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hFm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hF, mul_assoc]; exact (hslice x).const_mul _
    · refine Integrable.mono' ((GFFInv.integrable_test (d12 φ)).norm.mul_const
        ((Ck + ∫ q, G q ^ 2) / 2)) ?_ (Eventually.of_forall fun x => ?_)
      · exact hFm.norm.integral_prod_right'
      · simp only [hF, mul_assoc, norm_mul, integral_const_mul, norm_norm]
        rw [Real.norm_of_nonneg (integral_nonneg fun q => by positivity)]
        by_cases hx : L < ‖x‖
        · rw [hL x hx]; simp
        · push_neg at hx
          refine mul_le_mul_of_nonneg_left ((hbd x).trans ?_) (abs_nonneg _)
          gcongr
          exact integral_sq_kerFun_rect_le hx
  have e1 : ∀ x, d12 φ x * ⟪rectL2 x, G⟫ = ∫ q, F (x, q) := fun x => by
    rw [inner_rectL2_eq, ← integral_const_mul]
    congr 1; funext q; simp only [hF]; ring
  simp_rw [e1]
  rw [integral_integral_swap (f := fun x q => F (x, q)) hFi]
  congr 1; funext q
  simp only [hF]
  rw [integral_mul_const, integral_d12_mul_kerFun]

end GFFExist
end LQGMetric
