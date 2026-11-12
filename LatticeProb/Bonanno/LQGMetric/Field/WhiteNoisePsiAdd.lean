/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePsiAdd at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiCont

/-!
# Scale additivity and monotonicity for `ψ` (task P2-DDDFPSI; blueprint DDDF.D2.psi)

* `psi_add_ae`: `ψ_{a,c} = ψ_{a,b} + ψ_{b,c}` a.s. (the scale decomposition, DDDF l. 361–363).
* `variance_phi_sub_mono`, `variance_psi_sub_mono`: the increment variances of `φ_{a,b}`, `ψ_{a,b}`
  increase with `b` (the integrand only gains times `t ∈ [b², c²]`); used to bound the increments
  of `φ_{k−1,k}`, `ψ_{k−1,k}` by Lemma 4 at `δ = 2^{-k}` (DDDF (2.24)).
* `phi_sub_psi_self_ae`: `φ_{a,a} − ψ_{a,a} = 0` a.s. (empty time range).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma phiKernel_add_ae {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (x : ℂ) :
    phiKernel a c x =ᵐ[volume] fun p => phiKernel a b x p + phiKernel b c x p := by
  have hb : 0 < b := ha.trans_le hab
  have h := congrArg (fun f : WNSpace => (f : ℝ × ℂ → ℝ)) (phiKernelL2_add ha hab hbc x)
  filter_upwards [coeFn_phiKernelL2 a c ha x, coeFn_phiKernelL2 a b ha x,
    coeFn_phiKernelL2 b c hb x, Lp.coeFn_add (phiKernelL2 a b x) (phiKernelL2 b c x)]
    with p h1 h2 h3 h4
  rw [← h1, ← h2, ← h3, h, h4, Pi.add_apply]

namespace PsiParams

variable (Q : PsiParams)

lemma psiKernelL2_add {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (x : ℂ) :
    Q.psiKernelL2 a c x = Q.psiKernelL2 a b x + Q.psiKernelL2 b c x := by
  have hb : 0 < b := ha.trans_le hab
  refine Lp.ext ?_
  filter_upwards [Q.coeFn_psiKernelL2 a c ha x, Q.coeFn_psiKernelL2 a b ha x,
    Q.coeFn_psiKernelL2 b c hb x, Lp.coeFn_add (Q.psiKernelL2 a b x) (Q.psiKernelL2 b c x),
    phiKernel_add_ae ha hab hbc x] with p h1 h2 h3 h4 h5
  rw [h4, Pi.add_apply, h1, h2, h3]
  simp only [psiKernel]
  rw [h5]; ring

/-- Truncating the upper scale: `k_{a,b} = 1_{t ≤ b²} k_{a,c}` for `0 ≤ b ≤ c`. -/
lemma phiKernel_eq_ite (a : ℝ) {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (x : ℂ) (p : ℝ × ℂ) :
    phiKernel a b x p = if p.1 ≤ b ^ 2 then phiKernel a c x p else 0 := by
  have hb2 : b ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hb hbc 2
  unfold phiKernel
  simp only [indicator, mem_prod, mem_Icc, mem_univ, and_true]
  by_cases h : p.1 ≤ b ^ 2
  · by_cases h' : a ^ 2 ≤ p.1
    · simp [h, h', h.trans hb2]
    · simp [h, h']
  · simp [h]

lemma psiKernel_eq_ite (a : ℝ) {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (x : ℂ) (p : ℝ × ℂ) :
    Q.psiKernel a b x p = if p.1 ≤ b ^ 2 then Q.psiKernel a c x p else 0 := by
  simp only [psiKernel, phiKernel_eq_ite a hb hbc x p]
  split_ifs <;> simp

lemma sq_phiKernel_sub_mono (a : ℝ) {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (x x' : ℂ)
    (p : ℝ × ℂ) :
    (phiKernel a b x p - phiKernel a b x' p) ^ 2 ≤ (phiKernel a c x p - phiKernel a c x' p) ^ 2 := by
  rw [phiKernel_eq_ite a hb hbc x p, phiKernel_eq_ite a hb hbc x' p]
  split_ifs
  · exact le_rfl
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity

lemma sq_psiKernel_sub_mono (a : ℝ) {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (x x' : ℂ)
    (p : ℝ × ℂ) :
    (Q.psiKernel a b x p - Q.psiKernel a b x' p) ^ 2 ≤
      (Q.psiKernel a c x p - Q.psiKernel a c x' p) ^ 2 := by
  rw [Q.psiKernel_eq_ite a hb hbc x p, Q.psiKernel_eq_ite a hb hbc x' p]
  split_ifs
  · exact le_rfl
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity

end PsiParams


/-- `ψ_{a,c} = ψ_{a,b} + ψ_{b,c}` almost surely (DDDF l. 361–363). -/
theorem psi_add_ae (hW : IsWhiteNoise P W) (Q : PsiParams) {a b c : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (x : ℂ) :
    psi Q W a c x =ᵐ[P] fun ω => psi Q W a b x ω + psi Q W b c x ω := by
  filter_upwards [hW.add_ae (Q.psiKernelL2 a b x) (Q.psiKernelL2 b c x)] with ω h
  simp only [psi]
  rw [Q.psiKernelL2_add ha hab hbc, h, mul_add]

/-- The increment variance of `φ_{a,b}` increases with `b`. -/
theorem variance_phi_sub_mono (hW : IsWhiteNoise P W) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbc : b ≤ c) (x x' : ℂ) :
    Var[fun ω => phi W a b x ω - phi W a b x' ω; P] ≤
      Var[fun ω => phi W a c x ω - phi W a c x' ω; P] := by
  have hb : 0 ≤ b := ha.le.trans hab
  rw [show (fun ω => phi W a b x ω - phi W a b x' ω) = fun ω =>
      Real.sqrt Real.pi * W (phiKernelL2 a b x) ω - Real.sqrt Real.pi * W (phiKernelL2 a b x') ω
      from rfl, variance_sqrtPi_sub hW,
    show (fun ω => phi W a c x ω - phi W a c x' ω) = fun ω =>
      Real.sqrt Real.pi * W (phiKernelL2 a c x) ω - Real.sqrt Real.pi * W (phiKernelL2 a c x') ω
      from rfl, variance_sqrtPi_sub hW, PsiParams.sq_norm_phiKernelL2_sub' ha,
    PsiParams.sq_norm_phiKernelL2_sub' ha]
  refine mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ fun p =>
    PsiParams.sq_phiKernel_sub_mono a hb hbc x x' p) Real.pi_pos.le
  · exact PsiParams.integrable_sq_sub (memLp_phiKernel a b ha x) (memLp_phiKernel a b ha x')
  · exact PsiParams.integrable_sq_sub (memLp_phiKernel a c ha x) (memLp_phiKernel a c ha x')

/-- The increment variance of `ψ_{a,b}` increases with `b`. -/
theorem variance_psi_sub_mono (hW : IsWhiteNoise P W) (Q : PsiParams) {a b c : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (x x' : ℂ) :
    Var[fun ω => psi Q W a b x ω - psi Q W a b x' ω; P] ≤
      Var[fun ω => psi Q W a c x ω - psi Q W a c x' ω; P] := by
  have hb : 0 ≤ b := ha.le.trans hab
  rw [show (fun ω => psi Q W a b x ω - psi Q W a b x' ω) = fun ω =>
      Real.sqrt Real.pi * W (Q.psiKernelL2 a b x) ω -
        Real.sqrt Real.pi * W (Q.psiKernelL2 a b x') ω from rfl, variance_sqrtPi_sub hW,
    show (fun ω => psi Q W a c x ω - psi Q W a c x' ω) = fun ω =>
      Real.sqrt Real.pi * W (Q.psiKernelL2 a c x) ω -
        Real.sqrt Real.pi * W (Q.psiKernelL2 a c x') ω from rfl, variance_sqrtPi_sub hW,
    Q.sq_norm_psiKernelL2_sub ha, Q.sq_norm_psiKernelL2_sub ha]
  refine mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ fun p =>
    Q.sq_psiKernel_sub_mono a hb hbc x x' p) Real.pi_pos.le
  · exact PsiParams.integrable_sq_sub (Q.memLp_psiKernel a b ha x) (Q.memLp_psiKernel a b ha x')
  · exact PsiParams.integrable_sq_sub (Q.memLp_psiKernel a c ha x) (Q.memLp_psiKernel a c ha x')

/-- `φ_{a,a} − ψ_{a,a} = 0` almost surely. -/
theorem phi_sub_psi_self_ae (hW : IsWhiteNoise P W) (Q : PsiParams) {a : ℝ} (ha : 0 < a)
    (x : ℂ) : (fun ω => phi W a a x ω - psi Q W a a x ω) =ᵐ[P] 0 := by
  have hnull : ∀ᵐ p : ℝ × ℂ ∂volume, p.1 ≠ a ^ 2 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have : {p : ℝ × ℂ | p.1 = a ^ 2} = {a ^ 2} ×ˢ univ := by ext p; simp
    rw [this, show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, Measure.prod_prod]
    simp
  have h0 : ∫ p, (phiKernel a a x p - Q.psiKernel a a x p) ^ 2 = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hnull] with p hp
    have : p ∉ Icc (a ^ 2) (a ^ 2) ×ˢ (univ : Set ℂ) := by
      intro h
      exact hp (le_antisymm (mem_prod.mp h).1.2 (mem_prod.mp h).1.1)
    simp only [PsiParams.psiKernel, phiKernel]
    rw [indicator_of_notMem this]
    simp
  have hn : ‖Real.sqrt Real.pi • phiKernelL2 a a x + (-Real.sqrt Real.pi) • Q.psiKernelL2 a a x‖
      = 0 := by
    rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul]
    have : ‖phiKernelL2 a a x - Q.psiKernelL2 a a x‖ ^ 2 = 0 := by
      rw [Q.sq_norm_phiKernelL2_sub_psi ha]; exact h0
    rw [pow_eq_zero_iff two_ne_zero] at this
    rw [this, mul_zero]
  have h := hW.ae_eq_zero_of_norm_eq_zero ![phiKernelL2 a a x, Q.psiKernelL2 a a x]
    ![Real.sqrt Real.pi, -Real.sqrt Real.pi] (by simpa [Fin.sum_univ_two] using hn)
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at hω
  simp only [phi, psi, Pi.zero_apply]
  linarith

end WhiteNoise
end LQGMetric
