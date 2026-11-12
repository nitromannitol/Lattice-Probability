/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127I3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127I2

/-!
# (L4) of D127, part 3: stochastic Fubini for the coarse field (packet P-127I, P2-HEATI)

CONF (arXiv:1905.00381, `confluence-final.tex`) C:722–731. For the continuous version `Y` of
`h_{t,∞}(x) = √π W(K^{(t,∞)}_x)` (`wnField W U (Ioi t)`, DZZ (eq:WND_decomposition)):
`∫ ψ(x) Y(x) dx = W(√π K^{(t,∞)}(ψ 1_U))` a.s. (`ae_integral_mul_coarse`), from the copied
stochastic Fubini `ae_integral_tmul_eq_gen` (S3D127I1). The kernel bound `‖K_x‖² ≤ K (2R)^α`
comes from the Hölder bound of (L2) and `K_x = 0` off `U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

lemma wndKernel_eq_zero_of_not_mem {I : Set ℝ} (hI0 : I ⊆ Ioi 0) {x : ℂ} (hx : x ∉ U)
    (p : ℝ × ℂ) : wndKernel U I x p = 0 := by
  unfold wndKernel
  by_cases hp : p.1 ∈ I
  · rw [indicator_of_mem hp]
    have h0 : 0 < p.1 / 2 := by have := hI0 hp; simp only [mem_Ioi] at this; linarith
    exact killedHeat_eq_zero_of_not_mem_left (Real.toNNReal_pos.2 h0).ne' hx _
  · rw [indicator_of_notMem hp]

lemma wndKernelL2_eq_zero_of_not_mem {I : Set ℝ} (hI0 : I ⊆ Ioi 0) {x : ℂ} (hx : x ∉ U) :
    wndKernelL2 U I x = 0 := by
  unfold wndKernelL2
  split_ifs with h
  · refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [h.coeFn_toLp] with p hp
    rw [hp, wndKernel_eq_zero_of_not_mem hI0 hx]; rfl
  · rfl

/-- `‖K_x‖² ≤ K (2|R|)^α` from the Hölder bound (compare with `x₀ = c + |R| ∉ U`) -/
lemma sq_norm_wndKernelL2_le_of_holder (hUR : U ⊆ ball c R) {I : Set ℝ} (hI0 : I ⊆ Ioi 0)
    {K α : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hF : ∀ x x', ‖wndKernelL2 U I x - wndKernelL2 U I x'‖ ^ 2 ≤ K * ‖x - x'‖ ^ α) (x : ℂ) :
    ‖wndKernelL2 U I x‖ ^ 2 ≤ K * (2 * |R|) ^ α := by
  by_cases hx : x ∈ U
  · set x₀ : ℂ := c + ((|R| : ℝ) : ℂ) with hx₀
    have hn : ‖x₀ - c‖ = |R| := by
      rw [hx₀, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    have hx₀U : x₀ ∉ U := fun h => by
      have := hUR h
      rw [mem_ball, dist_eq_norm, hn] at this
      exact absurd this (not_lt.2 (le_abs_self R))
    have hxc : ‖x - c‖ < R := by have := hUR hx; rwa [mem_ball, dist_eq_norm] at this
    have hd : ‖x - x₀‖ ≤ 2 * |R| := by
      calc ‖x - x₀‖ = ‖(x - c) - (x₀ - c)‖ := by ring_nf
        _ ≤ ‖x - c‖ + ‖x₀ - c‖ := norm_sub_le _ _
        _ ≤ 2 * |R| := by rw [hn]; linarith [le_abs_self R]
    have h := hF x x₀
    rw [wndKernelL2_eq_zero_of_not_mem hI0 hx₀U, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hd hα.le) hK)
  · rw [wndKernelL2_eq_zero_of_not_mem hI0 hx, norm_zero]
    have : 0 ≤ K * (2 * |R|) ^ α := by positivity
    simpa using this

lemma inner_wndKernelL2_eq' {I : Set ℝ} {x : ℂ} (h : MemLp (wndKernel U I x) 2 volume)
    (G : WNSpace) : ⟪wndKernelL2 U I x, G⟫ = ∫ q, wndKernel U I x q * G q := by
  rw [wndKernelL2, dite_eq_left_of_eq_true (eq_true h), L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_toLp] with q h1
  rw [h1, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Stochastic Fubini for the coarse field**: `∫ ψ h_{t,∞} = W(√π K^{(t,∞)}(ψ 1_U))` a.s. -/
theorem ae_integral_mul_coarse (hW : IsWhiteNoise P W) (hU : IsOpen U) (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {t : ℝ} (ht : 0 < t) {K α : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hF : ∀ x x', ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x'‖ ^ 2 ≤ K * ‖x - x'‖ ^ α)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] wnField W U (Ioi t) x) (ψ : TestC) :
    (fun ω => ∫ x, ψ x * Y x ω) =ᵐ[P]
      W (Real.sqrt Real.pi • uKerL2 U (Ioi t) (U.indicator ψ)) := by
  have hI0 : Ioi t ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ht.le
  have hmem : ∀ x, MemLp (wndKernel U (Ioi t) x) 2 volume := fun x =>
    memLp_wndKernel hU hR hUR measurableSet_Ioi ht subset_rfl x
  have hb := sq_norm_wndKernelL2_le_of_holder hUR hI0 hK hα hF
  have hRb : ∀ x, ‖Real.sqrt Real.pi • wndKernelL2 U (Ioi t) x‖ ^ 2 ≤
      Real.pi * (K * (2 * |R|) ^ α) := fun x => by
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt Real.pi_pos.le]
    exact mul_le_mul_of_nonneg_left (hb x) Real.pi_pos.le
  have hYW' : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (Real.sqrt Real.pi • wndKernelL2 U (Ioi t) x) :=
    fun x => by
      filter_upwards [hYW x, hW.smul_ae (Real.sqrt Real.pi) (wndKernelL2 U (Ioi t) x)]
        with ω h1 h2
      rw [h1, h2]; rfl
  obtain ⟨C, hC⟩ := testC_abs_le ψ
  obtain ⟨m1, b1, i1⟩ := indicator_props hU ψ hC
  have hφm := memLp_uKer hU hR hUR measurableSet_Ioi hI0 m1 b1 i1
  refine ae_integral_tmul_eq_gen hW hRb hYc hYm hYW' ψ fun G => ?_
  simp only [real_inner_smul_left, inner_wndKernelL2_eq' (hmem _), inner_uKerL2_eq hφm]
  have e : ∀ x, ψ x * (Real.sqrt Real.pi * ∫ q, wndKernel U (Ioi t) x q * G q) =
      Real.sqrt Real.pi * (ψ x * ∫ q, wndKernel U (Ioi t) x q * G q) := fun x => by ring
  simp_rw [e]
  rw [integral_const_mul]
  congr 1
  refine integral_tmul_inner_gen ψ (fun x => wndKernel U (Ioi t) x)
    (measurable_wndKernel_comp hU measurableSet_Ioi measurable_fst measurable_snd) hmem
    (Ck := K * (2 * |R|) ^ α) (fun x => ?_) _ (fun q => ?_) G
  · calc ∫ q, wndKernel U (Ioi t) x q ^ 2 = ‖wndKernelL2 U (Ioi t) x‖ ^ 2 := by
          rw [sq_norm_L2_eq]
          refine integral_congr_ae ?_
          rw [wndKernelL2, dite_eq_left_of_eq_true (eq_true (hmem x))]
          filter_upwards [(hmem x).coeFn_toLp] with q h1
          rw [h1]
      _ ≤ _ := hb x
  · unfold uKer
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ U
    · simp only [indicator_of_mem hy]
    · simp only [indicator_of_notMem hy, wndKernel_eq_zero_of_not_mem hI0 hy, mul_zero]

end LQGMetric.CONF.ZBM
