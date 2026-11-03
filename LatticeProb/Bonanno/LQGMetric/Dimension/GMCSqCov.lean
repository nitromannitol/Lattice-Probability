/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqCov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqKer

/-!
# Circle-average covariances of the zero-boundary GFF on the unit square (P2-GMC, WP-24)

For `hX : IsZeroBoundaryGFFOn openSquare X P` and circles `∂B(z, r)`, `∂B(w, s)` whose closed
discs lie in `𝕍`:

* `circleCov_eq_kernel` : `Cov(h_r(z), h_s(w)) = ∫∫ G_ℍ(φ x, φ y)` (QZ
  `K3.dualCov_conformal_eq_kernel`);
* `circleCov_same` : `Cov(h_r(z), h_s(z)) = −log max(r, s) + hS z z`;
* `circleCov_far` : `Cov(h_r(z), h_s(w)) = −log‖z − w‖ + hS z w` if `‖z − w‖ ≥ r + s`.

Duplantier–Sheffield arXiv:0808.1560 §3.1 (circle averages of the GFF; the Green function is
`−log|x−y| + harmonic`). The circle means of `log‖· − y‖` are QZ `integral_log_norm_sub_circleUnif`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal ComplexConjugate

namespace LQGMetric

lemma inSq_of_closedBall {z : ℂ} {r : ℝ} (hr : 0 < r) (hB : closedBall z r ⊆ openSquare) :
    InSq r z := by
  have p : ∀ u : ℂ, ‖u‖ = r → z + u ∈ openSquare := fun u hu =>
    hB (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hu])
  have h1 := p r (by rw [Complex.norm_of_nonneg hr.le])
  have h2 := p (-r) (by rw [norm_neg, Complex.norm_of_nonneg hr.le])
  have h3 := p (r * Complex.I) (by rw [norm_mul, Complex.norm_I, Complex.norm_of_nonneg hr.le,
    mul_one])
  have h4 := p (-(r * Complex.I)) (by rw [norm_neg, norm_mul, Complex.norm_I,
    Complex.norm_of_nonneg hr.le, mul_one])
  obtain ⟨-, a1, -, -⟩ := h1
  obtain ⟨a2, -, -, -⟩ := h2
  obtain ⟨-, -, -, a3⟩ := h3
  obtain ⟨-, -, a4, -⟩ := h4
  simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_add, add_zero, neg_zero] at a1 a2 a3 a4
  exact ⟨by linarith, a1, by linarith, a3⟩

lemma isAdmissibleH_circleUnif {z : ℂ} {r : ℝ} (hr : 0 < r) (hB : closedBall z r ⊆ openSquare) :
    IsAdmissibleH (circleUnif z r) := by
  have h := inSq_of_closedBall hr hB
  rw [← foldedCircle_eq_of_inSq h hr]
  exact isAdmissibleH_foldedCircle (show z ∈ Hbar from (h.pos hr).le) hr

lemma circleUnif_restrict_openSquare {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall z r ⊆ openSquare) : (circleUnif z r).restrict openSquare = circleUnif z r :=
  Measure.restrict_eq_self_of_ae_mem
    ((CoordReg.ae_mem_closedBall_circleUnif z hr.le).mono fun _ hx => hB hx)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- **kernel form of the covariance of two circle averages** -/
theorem circleCov_eq_kernel (hX : IsZeroBoundaryGFFOn openSquare X P) {z w : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hB₁ : closedBall z r ⊆ openSquare)
    (hB₂ : closedBall w s ⊆ openSquare) :
    cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w s); P] =
      ∫ x, ∫ y, greenH (sqM x) (sqM y) ∂circleUnif w s ∂circleUnif z r := by
  have h₁ := inSq_of_closedBall hr hB₁
  have h₂ := inSq_of_closedBall hs hB₂
  rw [hX.covariance_eq _ _ (isAdmissibleDual_openSquare_foldedCircle h₁ hr)
    (isAdmissibleDual_openSquare_foldedCircle h₂ hs), foldedCircle_eq_of_inSq h₁ hr,
    foldedCircle_eq_of_inSq h₂ hs,
    K3.dualCov_conformal_eq_kernel isConformalOnto_sqMap (isAdmissibleH_map_circle hr hB₁)
      (isAdmissibleH_map_circle hs hB₂),
    circleUnif_restrict_openSquare hr hB₁, circleUnif_restrict_openSquare hs hB₂]
  refine integral_congr_ae ?_
  filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hx
  refine integral_congr_ae ?_
  filter_upwards [CoordReg.ae_mem_closedBall_circleUnif w hs.le] with y hy
  rw [sqM_eq (hB₁ hx), sqM_eq (hB₂ hy)]

/-- the inner integral: `∫ G_ℍ(φ x, φ y) dσ_{w,s}(y) = −log max(s, ‖w − x‖) + hS x w` -/
lemma integral_greenH_sqM_circle {x w : ℂ} {s : ℝ} (hx : x ∈ openSquare) (hs : 0 < s)
    (hB : closedBall w s ⊆ openSquare) :
    ∫ y, greenH (sqM x) (sqM y) ∂circleUnif w s = -Real.log (max s ‖w - x‖) + hS x w := by
  have hat : ∀ᵐ y ∂circleUnif w s, y ≠ x := by
    rw [ae_iff]
    have := noAtoms_of_isAdmissibleH (isAdmissibleH_circleUnif hs hB) x
    simpa using this
  have hcongr : (fun y => greenH (sqM x) (sqM y)) =ᵐ[circleUnif w s]
      fun y => -Real.log ‖y - x‖ + hS x y := by
    filter_upwards [hat, CoordReg.ae_mem_closedBall_circleUnif w hs.le] with y hyx hy
    rw [greenH_sqM hx (hB hy) (Ne.symm hyx), norm_sub_rev]
  rw [integral_congr_ae hcongr, integral_add (f := fun y => -Real.log ‖y - x‖)
    (CircleMV.integrable_log_norm_sub_circleUnif w x s).neg
    (integrable_hS_right hx hs.le hB), integral_neg, integral_log_norm_sub_circleUnif w x hs,
    integral_hS_circle hx hs.le hB]

/-- **same centre** : `Cov(h_r(z), h_s(z)) = −log max(r, s) + hS z z` -/
theorem circleCov_same (hX : IsZeroBoundaryGFFOn openSquare X P) {z : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hB₁ : closedBall z r ⊆ openSquare)
    (hB₂ : closedBall z s ⊆ openSquare) :
    cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle z s); P] =
      -Real.log (max r s) + hS z z := by
  rw [circleCov_eq_kernel hX hr hs hB₁ hB₂]
  have hz : z ∈ openSquare := hB₁ (mem_closedBall_self hr.le)
  have hcongr : (fun x => ∫ y, greenH (sqM x) (sqM y) ∂circleUnif z s) =ᵐ[circleUnif z r]
      fun x => -Real.log (max r s) + hS x z := by
    filter_upwards [CircleMV.ae_circleUnif z r, CoordReg.ae_mem_closedBall_circleUnif z hr.le]
      with x hxr hx
    rw [integral_greenH_sqM_circle (hB₁ hx) hs hB₂, norm_sub_rev, hxr, abs_of_pos hr, max_comm]
  have hi : Integrable (fun x => hS x z) (circleUnif z r) := by
    simp_rw [hS_symm _ z]; exact integrable_hS_right hz hr.le hB₁
  rw [integral_congr_ae hcongr, integral_add (integrable_const _) hi, integral_const,
    integral_hS_circle_left hz hr.le hB₁]
  simp

/-- **distant centres** : `Cov(h_r(z), h_s(w)) = −log‖z − w‖ + hS z w` for `‖z − w‖ ≥ r + s` -/
theorem circleCov_far (hX : IsZeroBoundaryGFFOn openSquare X P) {z w : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hB₁ : closedBall z r ⊆ openSquare)
    (hB₂ : closedBall w s ⊆ openSquare) (hzw : r + s ≤ ‖z - w‖) :
    cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w s); P] =
      -Real.log ‖z - w‖ + hS z w := by
  rw [circleCov_eq_kernel hX hr hs hB₁ hB₂]
  have hw : w ∈ openSquare := hB₂ (mem_closedBall_self hs.le)
  have hcongr : (fun x => ∫ y, greenH (sqM x) (sqM y) ∂circleUnif w s) =ᵐ[circleUnif z r]
      fun x => -Real.log ‖x - w‖ + hS x w := by
    filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hx
    have hsx : s ≤ ‖w - x‖ := by
      rw [mem_closedBall, dist_eq_norm] at hx
      have := norm_sub_le_norm_sub_add_norm_sub z x w
      rw [norm_sub_rev z x, norm_sub_rev x w] at this
      linarith
    rw [integral_greenH_sqM_circle (hB₁ hx) hs hB₂, max_eq_right hsx, norm_sub_rev w x]
  have hi : Integrable (fun x => hS x w) (circleUnif z r) := by
    simp_rw [hS_symm _ w]; exact integrable_hS_right hw hr.le hB₁
  rw [integral_congr_ae hcongr, integral_add (f := fun y => -Real.log ‖y - w‖)
    (CircleMV.integrable_log_norm_sub_circleUnif z w r).neg hi,
    integral_neg, integral_log_norm_sub_circleUnif z w hr, integral_hS_circle_left hw hr.le hB₁,
    max_eq_right (by linarith)]

end LQGMetric
