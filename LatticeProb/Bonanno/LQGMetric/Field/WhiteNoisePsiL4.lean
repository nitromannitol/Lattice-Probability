/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePsiL4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsi

/-!
# DDDF Lemma 4 for `ψ_δ` and the full Lemma 4 (task P2-DDDFPSI; blueprint DDDF.L4)

DDDF (arXiv:1904.08021, `tightness.tex` l. 380–418, Lemma 4 = `lem:FieldScale`, (2.21)):
`Var(φ_δ(x) − φ_δ(x')) + Var(ψ_δ(x) − ψ_δ(x')) ≤ C|x − x'|/δ` for `δ ∈ (0,1]`.

The `φ` half is `variance_phi_sub_le` (P2-WN). For the `ψ` half DDDF write
`p^{Tr} * p^{Tr} = p_t q_t` and bound `q_t(0) − q_t(z)` and `p_t(0) − p_t(z)` separately, using
`0 ≤ Φ ≤ 1`, `|Φ_{σ_t}(u) − Φ_{σ_t}(v)| ≤ ‖∇Φ‖_∞ |u − v|/σ_t` and `√t/σ_t ≤ C` (l. 405–417).
We use the same three ingredients but split the integrand before integrating (own elementary
rearrangement of the paper's computation, proposed DEVIATION D-DDDF-PSI-1):
`k_x T_x − k_{x'} T_{x'} = (k_x − k_{x'}) T_x + k_{x'} (T_x − T_{x'})`, so
`(k_x T_x − k_{x'} T_{x'})² ≤ 2 (k_x − k_{x'})² + 2 k_{x'}² · L|x − x'|/(r₀ √t)`
(`T = Φ_{σ_t}(x − ·) ∈ [0,1]`, `L` = Lipschitz constant of `Φ`, `σ_t ≥ r₀√t`).
The first part is the `φ` variance; the second integrates (`∫ p_{t/2}² = p_t(0) = (2πt)⁻¹`) to
`L|x−x'|/(2πr₀) ∫_{δ²}^1 t^{-3/2} dt ≤ L|x−x'|/(π r₀ δ)`.
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

lemma sq_norm_psiKernelL2_sub {a : ℝ} (ha : 0 < a) (b : ℝ) (x x' : ℂ) :
    ‖Q.psiKernelL2 a b x - Q.psiKernelL2 a b x'‖ ^ 2 =
      ∫ p, (Q.psiKernel a b x p - Q.psiKernel a b x' p) ^ 2 := by
  simp only [psiKernelL2, ha, ↓reduceDIte]
  exact sq_norm_toLp_sub _ _

lemma sq_norm_phiKernelL2_sub' {a : ℝ} (ha : 0 < a) (b : ℝ) (x x' : ℂ) :
    ‖phiKernelL2 a b x - phiKernelL2 a b x'‖ ^ 2 =
      ∫ p, (phiKernel a b x p - phiKernel a b x' p) ^ 2 := by
  simp only [phiKernelL2, ha, ↓reduceDIte]
  exact sq_norm_toLp_sub _ _

lemma sq_norm_phiKernelL2_sub_psi {a : ℝ} (ha : 0 < a) (b : ℝ) (x : ℂ) :
    ‖phiKernelL2 a b x - Q.psiKernelL2 a b x‖ ^ 2 =
      ∫ p, (phiKernel a b x p - Q.psiKernel a b x p) ^ 2 := by
  simp only [phiKernelL2, psiKernelL2, ha, ↓reduceDIte]
  exact sq_norm_toLp_sub _ _

lemma integrable_sq_sub {f g : ℝ × ℂ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable fun p => (f p - g p) ^ 2 :=
  (memLp_two_iff_integrable_sq (hf.sub hg).aestronglyMeasurable).mp (hf.sub hg)

/-- `|Φ_{σ_t}(x − y) − Φ_{σ_t}(x' − y)| ≤ L |x − x'| / (r₀ √t)` for `t > 0`. -/
lemma abs_trunc_sub_le {L : NNReal} (hL : LipschitzWith L Q.cut.Φ) (x x' : ℂ) (p : ℝ × ℂ)
    (ht : 0 < p.1) :
    |Q.trunc x p - Q.trunc x' p| ≤ L * ‖x - x'‖ / (Q.r₀ * Real.sqrt p.1) := by
  have hs := Q.sigma_pos ht
  have h1 := hL.dist_le_mul ((Q.sigma p.1)⁻¹ • (x - p.2)) ((Q.sigma p.1)⁻¹ • (x' - p.2))
  rw [Real.dist_eq, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs), show x - p.2 - (x' - p.2) = x - x' by ring] at h1
  have h2 : 0 < Q.r₀ * Real.sqrt p.1 := mul_pos Q.r₀_pos (Real.sqrt_pos.mpr ht)
  refine h1.trans ?_
  rw [inv_mul_eq_div, mul_div_assoc']
  exact div_le_div_of_nonneg_left (by positivity) h2 (Q.r₀_mul_sqrt_le_sigma p.1)

/-- The pointwise split of the `ψ` increment integrand. -/
lemma sq_psiKernel_sub_le {L : NNReal} (hL : LipschitzWith L Q.cut.Φ) {a : ℝ} (ha : 0 < a)
    (b : ℝ) (x x' : ℂ) (p : ℝ × ℂ) :
    (Q.psiKernel a b x p - Q.psiKernel a b x' p) ^ 2 ≤
      2 * (phiKernel a b x p - phiKernel a b x' p) ^ 2 +
        2 * (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator (fun p =>
          L * ‖x - x'‖ / (Q.r₀ * Real.sqrt p.1) * heatKernel (p.1 / 2) x' p.2 ^ 2) p := by
  by_cases hp : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ)
  · have ht : 0 < p.1 := lt_of_lt_of_le (by positivity) (mem_prod.mp hp).1.1
    simp only [psiKernel, phiKernel, indicator_of_mem hp]
    set A := heatKernel (p.1 / 2) x p.2
    set B := heatKernel (p.1 / 2) x' p.2
    set T := Q.trunc x p
    set T' := Q.trunc x' p
    have hT0 := Q.trunc_nonneg x p
    have hT1 := Q.trunc_le_one x p
    have hT0' := Q.trunc_nonneg x' p
    have hT1' := Q.trunc_le_one x' p
    have hd := Q.abs_trunc_sub_le hL x x' p ht
    have hsq : (T - T') ^ 2 ≤ L * ‖x - x'‖ / (Q.r₀ * Real.sqrt p.1) := by
      have : (T - T') ^ 2 ≤ |T - T'| := by
        rw [← sq_abs]
        have : |T - T'| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
        nlinarith [abs_nonneg (T - T')]
      linarith
    have e : A * T - B * T' = (A - B) * T + B * (T - T') := by ring
    rw [e]
    have h1 : ((A - B) * T) ^ 2 ≤ (A - B) ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith)
    have h2 : (B * (T - T')) ^ 2 ≤ L * ‖x - x'‖ / (Q.r₀ * Real.sqrt p.1) * B ^ 2 := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    nlinarith [sq_nonneg ((A - B) * T - B * (T - T'))]
  · simp [psiKernel, phiKernel, indicator_of_notMem hp]

end PsiParams

/-- **DDDF Lemma 4 (ψ part)**: there is `C` with `Var(ψ_δ(x) − ψ_δ(x')) ≤ C|x − x'|/δ` for all
`δ ∈ (0, 1]`, `x, x'` (DDDF l. 397–418). -/
theorem exists_variance_psi_sub_le (hW : IsWhiteNoise P W) (Q : PsiParams) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x x' : ℂ,
      Var[fun ω => psi Q W δ 1 x ω - psi Q W δ 1 x' ω; P] ≤ C * ‖x - x'‖ / δ := by
  obtain ⟨L, hL⟩ := Q.cut.exists_lipschitz
  refine ⟨2 * Real.sqrt 2 + 2 * L / Q.r₀, fun δ hδ hδ1 x x' => ?_⟩
  have hr₀ := Q.r₀_pos
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  set r := ‖x - x'‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  -- the variances as kernel integrals
  have hV : Var[fun ω => psi Q W δ 1 x ω - psi Q W δ 1 x' ω; P] =
      Real.pi * ∫ p, (Q.psiKernel δ 1 x p - Q.psiKernel δ 1 x' p) ^ 2 := by
    rw [← Q.sq_norm_psiKernelL2_sub hδ]; exact variance_sqrtPi_sub hW _ _
  have hVφ : Var[fun ω => phi W δ 1 x ω - phi W δ 1 x' ω; P] =
      Real.pi * ∫ p, (phiKernel δ 1 x p - phiKernel δ 1 x' p) ^ 2 := by
    rw [← PsiParams.sq_norm_phiKernelL2_sub' hδ]; exact variance_sqrtPi_sub hW _ _
  have hφ := variance_phi_sub_le hW hδ hδ1 x x'
  rw [hVφ] at hφ
  -- the time-weighted Fubini term
  have hpos : ∀ t ∈ Icc (δ ^ 2) ((1 : ℝ) ^ 2), 0 < t := fun t ht =>
    lt_of_lt_of_le (by positivity) ht.1
  have hsqrt : ContinuousOn (fun t : ℝ => (Real.sqrt t)⁻¹) (Icc (δ ^ 2) ((1 : ℝ) ^ 2)) :=
    (Real.continuous_sqrt.continuousOn).inv₀ fun t ht => (Real.sqrt_pos.mpr (hpos t ht)).ne'
  have hFub := integral_timeWeight (a := δ) (b := 1)
    (w := fun t => L * r / (Q.r₀ * Real.sqrt t)) (g := fun t => heatKernel t x' x')
    (G := fun p => heatKernel (p.1 / 2) x' p.2 ^ 2)
    (by
      have : (fun t : ℝ => L * r / (Q.r₀ * Real.sqrt t)) =
          fun t => L * r / Q.r₀ * (Real.sqrt t)⁻¹ := by
        funext t; rw [div_mul_eq_div_div, div_eq_mul_inv]
      rw [this]; exact continuousOn_const.mul hsqrt)
    (fun t ht => by positivity) (by fun_prop)
    (continuousOn_heatKernel_time δ hδ 1 x' x') (by
      have := measurable_heatKernel_half x'; fun_prop)
    (fun p _ => sq_nonneg _)
    (fun t ht => by
      simpa [sq] using integrable_heatKernel_mul_heatKernel (t / 2) (by linarith [hpos t ht]) x' x')
    (fun t ht => by
      simp only [sq]
      rw [integral_heatKernel_mul_heatKernel (t / 2) (by linarith [hpos t ht])]
      congr 1; ring)
  have hval : ∫ t in Icc (δ ^ 2) ((1 : ℝ) ^ 2), L * r / (Q.r₀ * Real.sqrt t) * heatKernel t x' x'
      = L * r / (2 * Real.pi * Q.r₀) * (2 / δ - 2) := by
    have e : ∀ t ∈ Icc (δ ^ 2) ((1 : ℝ) ^ 2), L * r / (Q.r₀ * Real.sqrt t) * heatKernel t x' x'
        = L * r / (2 * Real.pi * Q.r₀) * (t⁻¹ * (Real.sqrt t)⁻¹) := by
      intro t ht
      have := hpos t ht
      have : 0 < Real.sqrt t := Real.sqrt_pos.mpr this
      unfold heatKernel
      simp only [sub_self, norm_zero]
      norm_num
      field_simp
    rw [setIntegral_congr_fun measurableSet_Icc e, integral_const_mul, integral_Icc_eq_integral_Ioc,
      one_pow, ← intervalIntegral.integral_of_le hδ2, integral_inv_mul_inv_sqrt hδ hδ1]
  rw [hval] at hFub
  -- integrate the pointwise split
  have hint1 := PsiParams.integrable_sq_sub (Q.memLp_psiKernel δ 1 hδ x)
    (Q.memLp_psiKernel δ 1 hδ x')
  have hint2 := PsiParams.integrable_sq_sub (memLp_phiKernel δ 1 hδ x) (memLp_phiKernel δ 1 hδ x')
  have hmono := integral_mono hint1 ((hint2.const_mul 2).add (hFub.1.const_mul 2))
    (Q.sq_psiKernel_sub_le hL hδ 1 x x')
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hint2.const_mul 2) (hFub.1.const_mul 2), integral_const_mul,
    integral_const_mul, hFub.2] at hmono
  rw [hV]
  have hpi := Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hL0 : (0 : ℝ) ≤ L := L.2
  set I1 := ∫ p, (Q.psiKernel δ 1 x p - Q.psiKernel δ 1 x' p) ^ 2
  set I2 := ∫ p, (phiKernel δ 1 x p - phiKernel δ 1 x' p) ^ 2
  have hm : I1 ≤ 2 * I2 + 2 * (L * r / (2 * Real.pi * Q.r₀) * (2 / δ - 2)) := by
    convert hmono using 3
  have hφ' : Real.pi * I2 ≤ Real.sqrt 2 * r / δ := hφ
  have e1 : Real.pi * (2 * I2 + 2 * (L * r / (2 * Real.pi * Q.r₀) * (2 / δ - 2))) =
      2 * (Real.pi * I2) + L * r / Q.r₀ * (2 / δ - 2) := by
    field_simp
  have hK : 0 ≤ L * r / Q.r₀ := by positivity
  have e2 : (2 * Real.sqrt 2 + 2 * L / Q.r₀) * r / δ =
      2 * (Real.sqrt 2 * r / δ) + L * r / Q.r₀ * (2 / δ) := by
    field_simp
  rw [e2]
  have h3 := mul_le_mul_of_nonneg_left hm hpi.le
  rw [e1] at h3
  nlinarith

end WhiteNoise
end LQGMetric
