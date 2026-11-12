/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePsiCmp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiL4
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The per-scale comparison of `φ` and `ψ`: DDDF (2.23) and (2.24) (task P2-DDDFPSI)

DDDF (arXiv:1904.08021, `tightness.tex` l. 423–451, proof of Prop 5): with
`D_k(x) := φ_{k−1,k}(x) − ψ_{k−1,k}(x)` (`φ_{m,n} = φ_{2^{-n},2^{-m}}`),

* (2.23) `Var D_k(x) ≤ C e^{−c k^{2ε₀}}`. Proof as DDDF l. 445–451:
  `E D_k² = ∫∫ p_{t/2}(y)² (1 − Φ_{σ_t}(y))² dy dt`; for every `y`,
  `p_{t/2}(y)(1 − Φ_{σ_t}(y)) ≤ (πt)⁻¹ e^{−σ_t²/t}` (`Φ_{σ_t} = 1` on `|y| ≤ σ_t`), and
  `∫ p_{t/2} = 1`. (DDDF print `(2πt)⁻¹`; the exact constant is `(πt)⁻¹`, harmless.)
  With σ_t of D-DDDF-3, `σ_t²/t = r₀²(1 + |log t|)^{2ε₀} ≥ r₀² k^{2ε₀}` on
  `t ∈ [2^{-2k}, 2^{-2k+2}]`, giving the explicit `Var D_k ≤ log 4 · e^{−r₀² k^{2ε₀}}`.
* (2.24) `Var(φ_k(x) − φ_k(y)) + Var(ψ_k(x) − ψ_k(y)) ≤ C 2^k |x − y|` (`φ_k = φ_{2^{-k}}`):
  from Lemma 4 (DDDF write the constant as `1`; any `C` serves DZZ Lemma 2.7).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace PsiParams

variable (Q : PsiParams)

lemma continuousOn_sigma : ContinuousOn Q.sigma (Ioi 0) := by
  unfold sigma
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono fun t ht => ne_of_gt (mem_Ioi.mp ht)
  refine (continuousOn_const.mul Real.continuous_sqrt.continuousOn).mul ?_
  exact (continuousOn_const.add hlog.abs).rpow_const fun _ _ => Or.inr Q.ε₀_pos.le

/-- The weight `(πt)⁻¹ e^{−σ_t²/t}` of DDDF l. 448. -/
def tailWeight (t : ℝ) : ℝ := (Real.pi * t)⁻¹ * Real.exp (-(Q.sigma t ^ 2 / t))

lemma tailWeight_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Q.tailWeight t := by
  unfold tailWeight; have := Real.pi_pos; positivity

lemma continuousOn_tailWeight : ContinuousOn Q.tailWeight (Ioi 0) := by
  unfold tailWeight
  refine ContinuousOn.mul ?_ ?_
  · exact (continuousOn_const.mul continuousOn_id).inv₀ fun t ht =>
      (mul_pos Real.pi_pos (mem_Ioi.mp ht)).ne'
  · refine Real.continuous_exp.comp_continuousOn (ContinuousOn.neg ?_)
    exact (Q.continuousOn_sigma.pow 2).div continuousOn_id fun t ht => (mem_Ioi.mp ht).ne'

/-- Pointwise: `(k_x − k_x T_x)² ≤ 1_{[a²,b²]}(t) (πt)⁻¹ e^{−σ_t²/t} p_{t/2}(x − y)`. -/
lemma sq_phiKernel_sub_psiKernel_le {a : ℝ} (ha : 0 < a) (b : ℝ) (x : ℂ) (p : ℝ × ℂ) :
    (phiKernel a b x p - Q.psiKernel a b x p) ^ 2 ≤
      (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator
        (fun p => Q.tailWeight p.1 * heatKernel (p.1 / 2) x p.2) p := by
  by_cases hp : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ)
  · have ht : 0 < p.1 := lt_of_lt_of_le (by positivity) (mem_prod.mp hp).1.1
    simp only [psiKernel, phiKernel, indicator_of_mem hp]
    set A := heatKernel (p.1 / 2) x p.2
    have hA : 0 ≤ A := heatKernel_nonneg _ (by linarith) _ _
    have hT0 := Q.trunc_nonneg x p
    have hT1 := Q.trunc_le_one x p
    have hs := Q.sigma_pos ht
    have hwt := Q.tailWeight_nonneg ht.le
    by_cases hy : ‖x - p.2‖ ≤ Q.sigma p.1
    · have hT : Q.trunc x p = 1 := by
        refine Q.cut.eq_one _ ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), inv_mul_le_iff₀ hs,
          mul_one]
        exact hy
      rw [hT, mul_one, sub_self]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · push_neg at hy
      have hAw : A ≤ Q.tailWeight p.1 := by
        simp only [A, heatKernel, tailWeight]
        rw [show 2 * Real.pi * (p.1 / 2) = Real.pi * p.1 by ring,
          show 2 * (p.1 / 2) = p.1 by ring]
        gcongr
        rw [neg_div]
        gcongr
      have e : A - A * Q.trunc x p = A * (1 - Q.trunc x p) := by ring
      rw [e, mul_pow]
      have h1 : (1 - Q.trunc x p) ^ 2 ≤ 1 := by nlinarith
      calc A ^ 2 * (1 - Q.trunc x p) ^ 2 ≤ A ^ 2 := mul_le_of_le_one_right (sq_nonneg _) h1
        _ = A * A := sq A
        _ ≤ Q.tailWeight p.1 * A := mul_le_mul_of_nonneg_right hAw hA
  · simp [psiKernel, phiKernel, indicator_of_notMem hp]

end PsiParams

/-- `Var(φ_{a,b}(x) − ψ_{a,b}(x)) ≤ π ∫_{a²}^{b²} (πt)⁻¹ e^{−σ_t²/t} dt` (DDDF l. 445–451). -/
theorem variance_phi_sub_psi_le (hW : IsWhiteNoise P W) (Q : PsiParams) {a : ℝ} (ha : 0 < a)
    (b : ℝ) (x : ℂ) :
    Var[fun ω => phi W a b x ω - psi Q W a b x ω; P] ≤
      Real.pi * ∫ t in Icc (a ^ 2) (b ^ 2), Q.tailWeight t := by
  have hV : Var[fun ω => phi W a b x ω - psi Q W a b x ω; P] =
      Real.pi * ∫ p, (phiKernel a b x p - Q.psiKernel a b x p) ^ 2 := by
    rw [← Q.sq_norm_phiKernelL2_sub_psi ha]; exact variance_sqrtPi_sub hW _ _
  have hpos : ∀ t ∈ Icc (a ^ 2) (b ^ 2), 0 < t := fun t ht =>
    lt_of_lt_of_le (by positivity) ht.1
  have hFub := integral_timeWeight (a := a) (b := b) (w := Q.tailWeight) (g := fun _ => 1)
    (G := fun p => heatKernel (p.1 / 2) x p.2)
    (Q.continuousOn_tailWeight.mono fun t ht => hpos t ht)
    (fun t ht => Q.tailWeight_nonneg (hpos t ht).le)
    (by
      unfold PsiParams.tailWeight
      have := Q.measurable_sigma
      fun_prop)
    continuousOn_const (measurable_heatKernel_half x)
    (fun p hp => heatKernel_nonneg (p.1 / 2) (by linarith [hpos p.1 hp]) _ _)
    (fun t ht => integrable_heatKernel (t / 2) (by linarith [hpos t ht]) x)
    (fun t ht => integral_heatKernel (t / 2) (by linarith [hpos t ht]) x)
  simp only [mul_one] at hFub
  have hint1 := PsiParams.integrable_sq_sub (memLp_phiKernel a b ha x)
    (Q.memLp_psiKernel a b ha x)
  have hmono := integral_mono hint1 hFub.1 (Q.sq_phiKernel_sub_psiKernel_le ha b x)
  rw [hFub.2] at hmono
  rw [hV]
  exact mul_le_mul_of_nonneg_left hmono Real.pi_pos.le

/-- `σ_t²/t ≥ r₀² k^{2ε₀}` on `t ∈ [2^{-2k}, 2^{-2k+2}]`, `k = m + 1`. -/
lemma PsiParams.sigma_sq_div_ge (Q : PsiParams) (m : ℕ) {t : ℝ}
    (ht : t ∈ Icc (((2 : ℝ)⁻¹ ^ (m + 1)) ^ 2) (((2 : ℝ)⁻¹ ^ m) ^ 2)) :
    Q.r₀ ^ 2 * ((m : ℝ) + 1) ^ (2 * Q.ε₀) ≤ Q.sigma t ^ 2 / t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  have hb1 : ((2 : ℝ)⁻¹ ^ m) ^ 2 ≤ 1 := by
    rw [← pow_mul]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hlogt : Real.log t ≤ -(2 * m * Real.log 2) := by
    calc Real.log t ≤ Real.log (((2 : ℝ)⁻¹ ^ m) ^ 2) := Real.log_le_log ht0 ht.2
      _ = -(2 * m * Real.log 2) := by
        rw [← pow_mul, Real.log_pow, Real.log_inv]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  have habs : (m : ℝ) + 1 ≤ 1 + |Real.log t| := by
    have : 0 ≤ (m : ℝ) := m.cast_nonneg
    have : |Real.log t| = -Real.log t := abs_of_nonpos (by nlinarith)
    rw [this]; nlinarith
  have hrp : ((m : ℝ) + 1) ^ Q.ε₀ ≤ (1 + |Real.log t|) ^ Q.ε₀ :=
    Real.rpow_le_rpow (by positivity) habs Q.ε₀_pos.le
  have e1 : ((m : ℝ) + 1) ^ (2 * Q.ε₀) = (((m : ℝ) + 1) ^ Q.ε₀) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by positivity), Real.rpow_two]
  have e2 : Q.sigma t ^ 2 / t = Q.r₀ ^ 2 * ((1 + |Real.log t|) ^ Q.ε₀) ^ 2 := by
    unfold PsiParams.sigma
    rw [mul_pow, mul_pow, Real.sq_sqrt ht0.le]
    field_simp
  rw [e1, e2]
  have : 0 ≤ ((m : ℝ) + 1) ^ Q.ε₀ := by positivity
  gcongr

/-- **DDDF (2.23)**: `Var(φ_{k−1,k}(x) − ψ_{k−1,k}(x)) ≤ log 4 · e^{−r₀² k^{2ε₀}}` for
`k = m + 1 ≥ 1` (`φ_{k−1,k} = φ_{2^{-k}, 2^{-k+1}}`; DDDF l. 445–451). -/
theorem variance_phi_sub_psi_scale_le (hW : IsWhiteNoise P W) (Q : PsiParams) (m : ℕ)
    (x : ℂ) :
    Var[fun ω => phi W ((2 : ℝ)⁻¹ ^ (m + 1)) ((2 : ℝ)⁻¹ ^ m) x ω -
        psi Q W ((2 : ℝ)⁻¹ ^ (m + 1)) ((2 : ℝ)⁻¹ ^ m) x ω; P] ≤
      Real.log 4 * Real.exp (-(Q.r₀ ^ 2 * ((m : ℝ) + 1) ^ (2 * Q.ε₀))) := by
  set a : ℝ := (2 : ℝ)⁻¹ ^ (m + 1)
  set b : ℝ := (2 : ℝ)⁻¹ ^ m
  have ha : 0 < a := by positivity
  have hab : a ^ 2 ≤ b ^ 2 := by
    have : a ≤ b := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ m)
    exact pow_le_pow_left₀ ha.le this 2
  refine (variance_phi_sub_psi_le hW Q ha b x).trans ?_
  set E := Real.exp (-(Q.r₀ ^ 2 * ((m : ℝ) + 1) ^ (2 * Q.ε₀)))
  have hpos : ∀ t ∈ Icc (a ^ 2) (b ^ 2), 0 < t := fun t ht =>
    lt_of_lt_of_le (by positivity) ht.1
  have hle : ∀ t ∈ Icc (a ^ 2) (b ^ 2), Q.tailWeight t ≤ E / Real.pi * t⁻¹ := by
    intro t ht
    have ht0 := hpos t ht
    unfold PsiParams.tailWeight
    have hE : Real.exp (-(Q.sigma t ^ 2 / t)) ≤ E := by
      simp only [E]; exact Real.exp_le_exp.mpr (neg_le_neg (Q.sigma_sq_div_ge m ht))
    have : 0 < (Real.pi)⁻¹ * t⁻¹ := by have := Real.pi_pos; positivity
    have h2 := mul_le_mul_of_nonneg_left hE this.le
    rw [mul_inv]
    calc (Real.pi)⁻¹ * t⁻¹ * Real.exp (-(Q.sigma t ^ 2 / t)) ≤ (Real.pi)⁻¹ * t⁻¹ * E := h2
      _ = E / Real.pi * t⁻¹ := by ring
  have hcont : ContinuousOn (fun t : ℝ => E / Real.pi * t⁻¹) (Icc (a ^ 2) (b ^ 2)) :=
    continuousOn_const.mul (continuousOn_inv₀.mono fun t ht => (hpos t ht).ne')
  have h1 := setIntegral_mono_on (μ := volume)
    ((Q.continuousOn_tailWeight.mono fun t ht => hpos t ht).integrableOn_compact
      (μ := volume) isCompact_Icc)
    (hcont.integrableOn_compact (μ := volume) isCompact_Icc) measurableSet_Icc hle
  have hq : b ^ 2 / a ^ 2 = 4 := by
    simp only [a, b, pow_succ]; field_simp; norm_num
  have hI : ∫ t in Icc (a ^ 2) (b ^ 2), t⁻¹ = Real.log 4 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      integral_inv_of_pos (by positivity) (by positivity), hq]
  rw [integral_const_mul, hI] at h1
  have := Real.pi_pos
  calc Real.pi * ∫ t in Icc (a ^ 2) (b ^ 2), Q.tailWeight t
      ≤ Real.pi * (E / Real.pi * Real.log 4) := mul_le_mul_of_nonneg_left h1 this.le
    _ = Real.log 4 * E := by field_simp

end WhiteNoise
end LQGMetric
