/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushSmooth at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInwardPush

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_inwardPush_joint_contDiff :
    ContDiff ℝ 1 (fun p : ℝ × ℂ => laneCInwardPush p.1 p.2) := by
  let a : ℝ × ℂ → ℝ := fun p =>
    1 / 2 + (1 + p.1 * (5 - ((p.2.re - 1 / 2) ^ 2 +
      (p.2.im - 1 / 2) ^ 2))) * (p.2.re - 1 / 2)
  let b : ℝ × ℂ → ℝ := fun p =>
    1 / 2 + (1 + p.1 * (5 - ((p.2.re - 1 / 2) ^ 2 +
      (p.2.im - 1 / 2) ^ 2))) * (p.2.im - 1 / 2)
  have hre : ContDiff ℝ 1 (fun p : ℝ × ℂ => p.2.re) :=
    Complex.reCLM.contDiff.comp contDiff_snd
  have him : ContDiff ℝ 1 (fun p : ℝ × ℂ => p.2.im) :=
    Complex.imCLM.contDiff.comp contDiff_snd
  have ha : ContDiff ℝ 1 a := by
    dsimp [a]
    fun_prop
  have hb : ContDiff ℝ 1 b := by
    dsimp [b]
    fun_prop
  have hc : ContDiff ℝ 1 (fun p : ℝ × ℂ =>
      (a p : ℂ) + (b p : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp ha).add
      ((Complex.ofRealCLM.contDiff.comp hb).mul contDiff_const)
  convert hc using 1
  funext p
  exact Complex.mk_eq_add_mul_I (a p) (b p)

theorem laneC_inwardPush_fderiv_eq (d : ℝ) (z : ℂ) :
    fderiv ℝ (laneCInwardPush d) z =
      (fderiv ℝ (fun p : ℝ × ℂ => laneCInwardPush p.1 p.2) (d, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ ℂ) := by
  have h := (laneC_inwardPush_joint_contDiff.differentiable (by norm_num) (d, z)).hasFDerivAt
  have hc := h.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) d z)
  exact hc.fderiv

theorem laneC_inwardPush_fderiv_continuous :
    Continuous (fun p : ℝ × ℂ => fderiv ℝ (laneCInwardPush p.1) p.2) := by
  have hderiv : Continuous (fun p : ℝ × ℂ =>
      fderiv ℝ (fun q : ℝ × ℂ => laneCInwardPush q.1 q.2) p) :=
    laneC_inwardPush_joint_contDiff.continuous_fderiv (by norm_num)
  have hcomp : Continuous (fun p : ℝ × ℂ =>
      (ContinuousLinearMap.compL ℝ ℂ (ℝ × ℂ) ℂ
        (fderiv ℝ (fun q : ℝ × ℂ => laneCInwardPush q.1 q.2) p))
        (ContinuousLinearMap.inr ℝ ℝ ℂ)) :=
    ((ContinuousLinearMap.compL ℝ ℂ (ℝ × ℂ) ℂ).continuous.comp hderiv).clm_apply
      continuous_const
  simpa only [ContinuousLinearMap.compL_apply, laneC_inwardPush_fderiv_eq] using hcomp

end SupercriticalLQGUniqueness.B2.DG20Conc
