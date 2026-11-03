/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCCircle at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenH2
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Circle averages of the zero-boundary GFF on the unit square: variance and exponential moment
(task P2-GMC, WP-24)

For a QZ zero-boundary GFF `X` on the open unit square `𝕍 = (0,1)²`
(`QuantumZipper.IsZeroBoundaryGFFOn openSquare X P`, the field of Statement/Dimension.lean) and a
circle `∂B(d, r)` inside `𝕍` (`InSq r d`):

* `isAdmissibleDual_openSquare_foldedCircle` : the circle measure is admissible for `X`;
* `dualNormSq_openSquare_foldedCircle_le` : `Var h_r(d) ≤ log (3/r)`;
* `lintegral_exp_foldedCircle_le` : `E e^{γ h_r(d)} ≤ (3/r)^{γ²/2}`.

This is the input of DZZ Lemma 2.10 (`LBM_LGDarXiv.tex` l. 673–682; Kahane 85, RV10) that we
use for the first moment of the LQG measure (`GMCMoment.lean`): the circle-average variance is
`log(1/r) + O(1)` (Duplantier–Sheffield arXiv:0808.1560 §3.1, `Var h_ε(z) = log(1/ε) + log CR(z)`;
here only the upper bound is needed). Proof: domain monotonicity of the dual Dirichlet norm
(QZ `K3.dualNormSq_zeroSpace_mono`), its value on `ℍ` (QZ `K3.dualNormSq_H_eq`, Green energy
of `G_ℍ`), the circle mean value of `G_ℍ` (QZ `integral_greenH_circleUnif`), and the Gaussian
moment generating function (mathlib `mgf_gaussianReal`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set QuantumZipper
open scoped ENNReal ComplexConjugate

namespace LQGMetric

/-- the closed disc `B̄(d, r)` lies in the open unit square (strictly) -/
def InSq (r : ℝ) (d : ℂ) : Prop := r < d.re ∧ d.re + r < 1 ∧ r < d.im ∧ d.im + r < 1

lemma closedBall_subset_openSquare {r : ℝ} {d : ℂ} (h : InSq r d) :
    Metric.closedBall d r ⊆ openSquare := by
  intro x hx
  rw [Metric.mem_closedBall, Complex.dist_eq] at hx
  have h1 : |(x - d).re| ≤ ‖x - d‖ := Complex.abs_re_le_norm _
  have h2 : |(x - d).im| ≤ ‖x - d‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
  obtain ⟨a, b, c, e⟩ := h
  have := abs_le.mp (h1.trans hx); have := abs_le.mp (h2.trans hx)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma InSq.pos {r : ℝ} {d : ℂ} (h : InSq r d) (hr : 0 < r) : 0 < d.im := hr.trans h.2.2.1

lemma foldedCircle_eq_of_inSq {r : ℝ} {d : ℂ} (h : InSq r d) (hr : 0 < r) :
    foldedCircle d r = circleUnif d r :=
  foldedCircle_eq_circleUnif hr.le h.2.2.1.le

lemma circleUnif_compl_closedBall {r : ℝ} (hr : 0 < r) (d : ℂ) :
    circleUnif d r (Metric.closedBall d r)ᶜ = 0 := by
  have := CircleMV.ae_circleUnif d r
  rw [ae_iff] at this
  refine measure_mono_null (fun x hx => ?_) this
  simp only [mem_compl_iff, Metric.mem_closedBall, Complex.dist_eq, not_le, mem_ofPred_eq] at hx ⊢
  rw [abs_of_pos hr]; exact hx.ne'

/-- **the Green energy of a circle in the square** : `∫∫ G_ℍ ≤ log (3/r)` -/
lemma kernelCov_greenH_circle_le {r : ℝ} {d : ℂ} (h : InSq r d) (hr : 0 < r) :
    kernelCov greenH (circleUnif d r) (circleUnif d r) ≤ Real.log (3 / r) := by
  have hr1 : r ≤ 1 := by obtain ⟨a, b, -, -⟩ := h; linarith
  have h3r : 0 ≤ Real.log (3 / r) :=
    Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  unfold kernelCov
  -- the inner integral, for `x` on the circle
  have hinner : ∀ᵐ x ∂circleUnif d r, ∫ y, greenH x y ∂circleUnif d r ≤ Real.log (3 / r) := by
    filter_upwards [CircleMV.ae_circleUnif d r] with x hx
    rw [abs_of_pos hr] at hx
    simp_rw [greenH_symm x]
    rw [integral_greenH_circleUnif d x hr]
    have hxd : ‖d - x‖ = r := by rw [norm_sub_rev]; exact hx
    rw [hxd, max_self]
    have hxs : x ∈ openSquare :=
      closedBall_subset_openSquare h (by rw [Metric.mem_closedBall, Complex.dist_eq]; linarith)
    have hds : d ∈ openSquare := closedBall_subset_openSquare h (Metric.mem_closedBall_self hr.le)
    have hb : ‖d - conj x‖ ≤ 3 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.conj_re, Complex.sub_im, Complex.conj_im, sub_neg_eq_add]
      obtain ⟨a1, a2, a3, a4⟩ := hxs; obtain ⟨b1, b2, b3, b4⟩ := hds
      have e1 : |d.re - x.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have e2 : |d.im + x.im| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hm : max r ‖d - conj x‖ ≤ 3 := max_le (by linarith) hb
    have hm0 : 0 < max r ‖d - conj x‖ := lt_max_of_lt_left hr
    rw [Real.log_div (by norm_num) hr.ne']
    linarith [Real.log_le_log hm0 hm]
  by_cases hint : Integrable (fun x => ∫ y, greenH x y ∂circleUnif d r) (circleUnif d r)
  · calc ∫ x, ∫ y, greenH x y ∂circleUnif d r ∂circleUnif d r
        ≤ ∫ _x, Real.log (3 / r) ∂circleUnif d r := integral_mono_ae hint (integrable_const _) hinner
      _ = Real.log (3 / r) := by simp
  · rw [integral_undef hint]; exact h3r

lemma closure_openSquare_supset {r : ℝ} {d : ℂ} (h : InSq r d) :
    Metric.closedBall d r ⊆ closure openSquare :=
  (closedBall_subset_openSquare h).trans subset_closure

/-- the circle measure is admissible for the zero-boundary GFF on the square, with dual norm
at most `log (3/r)` -/
theorem dualNormSq_openSquare_foldedCircle_le {r : ℝ} {d : ℂ} (h : InSq r d) (hr : 0 < r) :
    dualNormSq openSquare (zeroSpace openSquare) (foldedCircle d r) ≤
      ENNReal.ofReal (Real.log (3 / r)) := by
  have hadm := isAdmissibleH_foldedCircle (show d ∈ Hbar from (h.pos hr).le) hr
  refine (K3.dualNormSq_zeroSpace_mono isOpen_openSquare openSquare_subset_H).trans ?_
  rw [K3.dualNormSq_H_eq hadm, foldedCircle_eq_of_inSq h hr]
  exact ENNReal.ofReal_le_ofReal (kernelCov_greenH_circle_le h hr)

theorem isAdmissibleDual_openSquare_foldedCircle {r : ℝ} {d : ℂ} (h : InSq r d) (hr : 0 < r) :
    IsAdmissibleDual openSquare (zeroSpace openSquare) (foldedCircle d r) := by
  refine ⟨inferInstance, ⟨Metric.closedBall d r, isCompact_closedBall d r,
    closure_openSquare_supset h, ?_⟩,
    (dualNormSq_openSquare_foldedCircle_le h hr).trans_lt ENNReal.ofReal_lt_top⟩
  rw [foldedCircle_eq_of_inSq h hr]; exact circleUnif_compl_closedBall hr d

/-- `dualCov μ μ = dualNormSq μ` for a finite measure (the dual norm is quadratic) -/
lemma dualCov_self_eq {U : Set ℂ} (μ : Measure ℂ) [IsFiniteMeasure μ] :
    dualCov U (zeroSpace U) μ μ = (dualNormSq U (zeroSpace U) μ).toReal := by
  have h2 : dualNormSq U (zeroSpace U) (μ + μ) =
      ENNReal.ofReal ((2 : ℝ) ^ 2) * dualNormSq U (zeroSpace U) μ := by
    refine dualNormSq_eq_of_integral_eq_mul fun f hf => ?_
    have hi : Integrable f μ := by
      obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2.1
      exact Integrable.of_bound hf.1.continuous.aestronglyMeasurable C (ae_of_all _ hC)
    rw [integral_add_measure hi hi]; ring
  unfold dualCov
  rw [h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- **exponential moment of a circle average** : `E e^{γ h_r(d)} ≤ (3/r)^{γ²/2}` -/
theorem lintegral_exp_foldedCircle_le (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ)
    {r : ℝ} {d : ℂ} (h : InSq r d) (hr : 0 < r) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * X ω (foldedCircle d r))) ∂P ≤
      ENNReal.ofReal ((3 / r) ^ (γ ^ 2 / 2)) := by
  have hadm := isAdmissibleDual_openSquare_foldedCircle h hr
  have hG : HasGaussianLaw (fun ω => X ω (foldedCircle d r)) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨_, hadm⟩
  have := hG.isProbabilityMeasure
  have hm : AEMeasurable (fun ω => X ω (foldedCircle d r)) P :=
    (hX.measurable_coord _).aemeasurable
  set v := (dualNormSq openSquare (zeroSpace openSquare) (foldedCircle d r)).toReal with hv
  have hcov : Var[fun ω => X ω (foldedCircle d r); P] = v := by
    rw [← covariance_self hm, hX.covariance_eq _ _ hadm hadm, dualCov_self_eq]
  have hlaw : HasLaw (fun ω => X ω (foldedCircle d r)) (gaussianReal 0 v.toNNReal) P := by
    refine ⟨hm, ?_⟩
    rw [hG.map_eq_gaussianReal, hcov]
    congr 1
    exact hX.centered _ hadm
  have hmgf := mgf_gaussianReal hlaw γ
  have hint : Integrable (fun ω => Real.exp (γ * X ω (foldedCircle d r))) P :=
    hlaw.integrable_comp (f := fun x => Real.exp (γ * x)) (integrable_exp_mul_gaussianReal γ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmgf' : ∫ ω, Real.exp (γ * X ω (foldedCircle d r)) ∂P =
      Real.exp (0 * γ + (v.toNNReal : ℝ) * γ ^ 2 / 2) := by
    rw [← hmgf]; rfl
  rw [hmgf', Real.rpow_def_of_pos (by positivity), zero_mul, zero_add]
  refine Real.exp_le_exp.mpr ?_
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have hvle : v ≤ Real.log (3 / r) := by
    have hr1 : r ≤ 1 := by obtain ⟨a, b, -, -⟩ := h; linarith
    have h3r : 0 ≤ Real.log (3 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
    rw [hv]
    exact ENNReal.toReal_le_of_le_ofReal h3r (dualNormSq_openSquare_foldedCircle_le h hr)
  rw [Real.coe_toNNReal _ hv0]
  nlinarith [sq_nonneg γ]

end LQGMetric
