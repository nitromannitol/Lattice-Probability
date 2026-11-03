/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqKer at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqMap
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm

/-!
# Covariances of circle averages of the zero-boundary GFF on the unit square (P2-GMC, WP-24)

With `φ = sqM` (the measurable version of the conformal map `𝕍 → ℍ`), the Green function of `𝕍`
is `G_𝕍(x,y) = G_ℍ(φ x, φ y) = −log‖x − y‖ + hS x y` with
`hS x y = log‖φ x − conj(φ y)‖ − log‖dslope φ x y‖`, harmonic in each variable on `𝕍`
(`log` of the norm of a zero-free holomorphic function). Hence, for circles inside `𝕍`
(`circleCov_same`, `circleCov_far`):

* `Cov(h_r(z), h_s(z)) = −log max(r, s) + hS z z`;
* `Cov(h_r(z), h_s(w)) = −log‖z − w‖ + hS z w` when `‖z − w‖ ≥ r + s`.

These are the circle-average covariances of Duplantier–Sheffield arXiv:0808.1560 §3.1 (proof of
Prop. 3.1: `Var h_ε(z) = log(1/ε) + log CR(z; D)`); the mean value computation follows QZ
`CoordReg` (`CoordRegHarm.lean`, mathlib `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`), and
the kernel form of the covariance is QZ `K3.dualCov_conformal_eq_kernel`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal ComplexConjugate

namespace LQGMetric

/-- the measurable version of the conformal map `𝕍 → ℍ` -/
def sqM : ℂ → ℂ := K3.confMod sqMap openSquare

lemma measurable_sqM : Measurable sqM := K3.measurable_confMod isConformalOnto_sqMap

lemma sqM_eq {x : ℂ} (hx : x ∈ openSquare) : sqM x = sqMap x := K3.confMod_eqOn hx

lemma differentiableOn_sqM : DifferentiableOn ℂ sqM openSquare :=
  isConformalOnto_sqMap.diffOn.congr fun _ hx => sqM_eq hx

lemma sqM_mem_H {x : ℂ} (hx : x ∈ openSquare) : sqM x ∈ H := sqM_eq hx ▸ sqMap_mem_H hx

lemma sqM_injOn : InjOn sqM openSquare := fun x hx y hy h =>
  isConformalOnto_sqMap.injOn hx hy (by rwa [← sqM_eq hx, ← sqM_eq hy])

lemma deriv_sqM {x : ℂ} (hx : x ∈ openSquare) : deriv sqM x = deriv sqMap x :=
  Filter.EventuallyEq.deriv_eq (eventually_of_mem (isOpen_openSquare.mem_nhds hx)
    fun _ hy => sqM_eq hy)

lemma differentiableOn_dslope_sqM {x : ℂ} (hx : x ∈ openSquare) :
    DifferentiableOn ℂ (dslope sqM x) openSquare :=
  (Complex.differentiableOn_dslope (isOpen_openSquare.mem_nhds hx)).2 differentiableOn_sqM

lemma dslope_sqM_ne_zero {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) :
    dslope sqM x y ≠ 0 := by
  by_cases h : y = x
  · subst h; rw [dslope_same, deriv_sqM hy]; exact isConformalOnto_sqMap.deriv_ne y hy
  · rw [dslope_of_ne _ h, slope_def_field]
    exact div_ne_zero (sub_ne_zero.2 fun e => h (sqM_injOn hy hx e)) (sub_ne_zero.2 h)

lemma sub_conj_ne_zero {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) :
    sqM y - conj (sqM x) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at this
  have h1 : 0 < (sqM y).im := sqM_mem_H hy
  have h2 : 0 < (sqM x).im := sqM_mem_H hx
  linarith

/-- the harmonic part of the Green function of `𝕍` -/
def hS (x y : ℂ) : ℝ := Real.log ‖sqM x - conj (sqM y)‖ - Real.log ‖dslope sqM x y‖

lemma hS_symm (x y : ℂ) : hS x y = hS y x := by
  unfold hS; rw [norm_sub_conj_comm, CoordReg.dslope_symm]

/-- `G_ℍ(φ x, φ y) = −log‖x − y‖ + hS x y` -/
lemma greenH_sqM {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) (hxy : x ≠ y) :
    greenH (sqM x) (sqM y) = -Real.log ‖x - y‖ + hS x y := by
  have hyx : y ≠ x := Ne.symm hxy
  have h0 : sqM y - sqM x ≠ 0 := sub_ne_zero.2 fun e => hyx (sqM_injOn hy hx e)
  unfold greenH hS
  rw [dslope_of_ne _ hyx, slope_def_field, norm_div,
    Real.log_div (norm_ne_zero_iff.2 h0) (norm_ne_zero_iff.2 (sub_ne_zero.2 hyx)),
    norm_sub_rev (sqM y), norm_sub_rev y]
  ring

/-! ## Mean value property of `hS` on circles in `𝕍` -/

lemma continuousOn_log_norm {F : ℂ → ℂ} {S : Set ℂ} (hF : ContinuousOn F S) (h0 : ∀ y ∈ S, F y ≠ 0) :
    ContinuousOn (fun y => Real.log ‖F y‖) S :=
  hF.norm.log fun y hy => norm_ne_zero_iff.2 (h0 y hy)

lemma hS_eq (x y : ℂ) :
    hS x y = Real.log ‖sqM y - conj (sqM x)‖ - Real.log ‖dslope sqM x y‖ := by
  unfold hS; rw [norm_sub_conj_comm]

lemma continuousOn_hS_right {x : ℂ} (hx : x ∈ openSquare) : ContinuousOn (hS x) openSquare := by
  have e : hS x = fun y => Real.log ‖sqM y - conj (sqM x)‖ - Real.log ‖dslope sqM x y‖ :=
    funext (hS_eq x)
  rw [e]
  exact (continuousOn_log_norm (differentiableOn_sqM.continuousOn.sub continuousOn_const)
    fun y hy => sub_conj_ne_zero hx hy).sub
    (continuousOn_log_norm (differentiableOn_dslope_sqM hx).continuousOn
      fun y hy => dslope_sqM_ne_zero hx hy)

lemma measurable_hS_right (x : ℂ) : Measurable (hS x) := by
  have e : hS x = fun y => Real.log ‖sqM y - conj (sqM x)‖ - Real.log ‖dslope sqM x y‖ :=
    funext (hS_eq x)
  rw [e]
  exact (Real.measurable_log.comp (measurable_sqM.sub_const _).norm).sub
    (Real.measurable_log.comp (CoordReg.measurable_dslope measurable_sqM x).norm)

lemma integrable_hS_right {x w : ℂ} {s : ℝ} (hx : x ∈ openSquare) (hs : 0 ≤ s)
    (hB : closedBall w s ⊆ openSquare) : Integrable (hS x) (circleUnif w s) :=
  CoordReg.integrable_circleUnif_of_continuousOn (measurable_hS_right x) hs
    ((continuousOn_hS_right hx).mono hB)

/-- **mean value of `hS` in the second variable** -/
theorem integral_hS_circle {x w : ℂ} {s : ℝ} (hx : x ∈ openSquare) (hs : 0 ≤ s)
    (hB : closedBall w s ⊆ openSquare) : ∫ y, hS x y ∂circleUnif w s = hS x w := by
  have hU := isOpen_openSquare
  have hA1 : AnalyticOnNhd ℂ (fun y => sqM y - conj (sqM x)) (closedBall w s) :=
    ((differentiableOn_sqM.sub_const _).analyticOnNhd hU).mono hB
  have hA2 : AnalyticOnNhd ℂ (dslope sqM x) (closedBall w s) :=
    ((differentiableOn_dslope_sqM hx).analyticOnNhd hU).mono hB
  have hm1 : Measurable fun y => sqM y - conj (sqM x) := measurable_sqM.sub_const _
  have hm2 := CoordReg.measurable_dslope measurable_sqM x
  have hi1 : Integrable (fun y => Real.log ‖sqM y - conj (sqM x)‖) (circleUnif w s) :=
    CoordReg.integrable_circleUnif_of_continuousOn (Real.measurable_log.comp hm1.norm) hs
      ((continuousOn_log_norm (differentiableOn_sqM.continuousOn.sub continuousOn_const)
        fun y hy => sub_conj_ne_zero hx hy).mono hB)
  have hi2 : Integrable (fun y => Real.log ‖dslope sqM x y‖) (circleUnif w s) :=
    CoordReg.integrable_circleUnif_of_continuousOn (Real.measurable_log.comp hm2.norm) hs
      ((continuousOn_log_norm (differentiableOn_dslope_sqM hx).continuousOn
        fun y hy => dslope_sqM_ne_zero hx hy).mono hB)
  simp_rw [hS_eq x]
  rw [integral_sub hi1 hi2,
    CoordReg.integral_log_norm_circleUnif_of_analytic hm1 hs hA1
      (fun y hy => sub_conj_ne_zero hx (hB hy)),
    CoordReg.integral_log_norm_circleUnif_of_analytic hm2 hs hA2
      (fun y hy => dslope_sqM_ne_zero hx (hB hy))]

/-- mean value of `hS` in the first variable -/
theorem integral_hS_circle_left {z w : ℂ} {r : ℝ} (hw : w ∈ openSquare) (hr : 0 ≤ r)
    (hB : closedBall z r ⊆ openSquare) : ∫ x, hS x w ∂circleUnif z r = hS z w := by
  simp_rw [hS_symm _ w]; exact integral_hS_circle hw hr hB

end LQGMetric
