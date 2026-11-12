/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L5Kernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Bridge
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatMeas
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsi
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary

/-!
# DZZ's white-noise fields `h̃` (eq:WND_decomposition) and their covariance (P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 424–441:
`h̃_δ^{δ̃}(v) = √π ∫_{𝕍 × (δ², δ̃²)} p_𝕍(s/2; v, w) W(dw, ds)`, and (eq-cov-tildeh), "the
Chapman–Kolmogorov equations give that `E(h̃_δ^{δ̃}(u) h̃_δ^{δ̃}(v)) = π ∫_{δ²}^{δ̃²} p_𝕍(t; u, v) dt`".

* `wndKernel A I v (s, w) = 1_I(s) p_A(s/2; v, w)` — DZZ's kernel for a time set `I`
  (`I = (δ², δ̃²)`, or `(δ², ∞)` for `δ̃ = ∞`), with the killed heat kernel `p_A` of D53.
  The restriction to `w ∈ 𝕍` in DZZ's integral is automatic (`p_𝕍(s; v, w) = 0` for `w ∉ 𝕍`).
* `lintegral_wndKernel_mul`, `inner_wndKernelL2`: Chapman–Kolmogorov (`ofReal_killedHeat_add`)
  gives `⟪K_u, K_v⟫ = ∫_I p_A(s; u, v) ds`, for bounded open `A` and `I ⊆ (c₀, ∞)`, `c₀ > 0`.
* `wnField W A I v = √π W(K_v)`, `tildeH W δ δ' v = h̃_δ^{δ'}(v)`, `tildeHInf W δ v = h̃_δ(v)`.
* `cov_wnField` = (eq-cov-tildeh); `variance_wnField_sub` = DZZ l. 512.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

/-- DZZ's white-noise kernel `(s, w) ↦ 1_I(s) p_A(s/2; v, w)` (eq:WND_decomposition). -/
def wndKernel (A : Set ℂ) (I : Set ℝ) (v : ℂ) (p : ℝ × ℂ) : ℝ :=
  I.indicator (fun s => killedHeat A (s / 2).toNNReal v p.2) p.1

lemma wndKernel_nonneg (A : Set ℂ) (I : Set ℝ) (v : ℂ) (p : ℝ × ℂ) : 0 ≤ wndKernel A I v p :=
  indicator_nonneg (fun _ _ => killedHeat_nonneg _ _ _ _) _

lemma measurable_wndKernel {A : Set ℂ} (hA : IsOpen A) {I : Set ℝ} (hI : MeasurableSet I)
    (v : ℂ) : Measurable (wndKernel A I v) := by
  have e : wndKernel A I v =
      (Prod.fst ⁻¹' I).indicator (fun p : ℝ × ℂ => killedHeat A (p.1 / 2).toNNReal v p.2) := by
    funext p
    by_cases h : p.1 ∈ I <;> simp [wndKernel, h]
  rw [e]
  refine Measurable.indicator ?_ (hI.preimage measurable_fst)
  exact (measurable_killedHeat hA).comp
    ((measurable_fst.div_const 2).real_toNNReal.prodMk (measurable_const.prodMk measurable_snd))

/-- **Chapman–Kolmogorov for the kernels** (DZZ eq-cov-tildeh, lintegral form):
`∫ K_u K_v = ∫_I p_A(s; u, v) ds`. -/
theorem lintegral_wndKernel_mul {A : Set ℂ} (hA : IsOpen A) {I : Set ℝ} (hI : MeasurableSet I)
    (hI0 : I ⊆ Ioi 0) (u v : ℂ) :
    ∫⁻ p, ENNReal.ofReal (wndKernel A I u p) * ENNReal.ofReal (wndKernel A I v p) =
      ∫⁻ s in I, ENNReal.ofReal (killedHeat A s.toNNReal u v) := by
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl,
    lintegral_prod (fun p => ENNReal.ofReal (wndKernel A I u p) *
      ENNReal.ofReal (wndKernel A I v p)) (Measurable.aemeasurable (by
        exact (measurable_wndKernel hA hI u).ennreal_ofReal.mul
          (measurable_wndKernel hA hI v).ennreal_ofReal)),
    ← lintegral_indicator hI]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ I
  · simp only [wndKernel, indicator_of_mem hs]
    have hs0 : (0 : ℝ) < s := hI0 hs
    have ht : (s / 2).toNNReal ≠ 0 := by
      simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith
    have hsum : (s / 2).toNNReal + (s / 2).toNNReal = s.toNNReal := by
      rw [← Real.toNNReal_add (by linarith) (by linarith)]; ring_nf
    rw [← hsum, ofReal_killedHeat_add hA ht ht]
    refine lintegral_congr fun w => ?_
    rw [killedHeat_symm hA _ v w]
  · simp [wndKernel, hs]

lemma lintegral_killedHeat_lt_top {A : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball c R) {I : Set ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hI0 : I ⊆ Ioi c₀)
    (u v : ℂ) : ∫⁻ s in I, ENNReal.ofReal (killedHeat A s.toNNReal u v) < ∞ :=
  lt_of_le_of_lt (lintegral_mono_set hI0) (lintegral_killedHeat_Ioi_lt_top hR hAR u v hc₀)

/-- The kernels are square integrable. -/
theorem memLp_wndKernel {A : Set ℂ} (hA : IsOpen A) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball c R) {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (v : ℂ) : MemLp (wndKernel A I v) 2 volume := by
  have hI0' : I ⊆ Ioi 0 := hI0.trans (Ioi_subset_Ioi hc₀.le)
  rw [memLp_two_iff_integrable_sq (measurable_wndKernel hA hI v).aestronglyMeasurable]
  refine ⟨((measurable_wndKernel hA hI v).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg _)]
  have e : (fun p => ENNReal.ofReal (wndKernel A I v p ^ 2)) =
      fun p => ENNReal.ofReal (wndKernel A I v p) * ENNReal.ofReal (wndKernel A I v p) := by
    funext p; rw [sq, ENNReal.ofReal_mul (wndKernel_nonneg _ _ _ _)]
  rw [e, lintegral_wndKernel_mul hA hI hI0' v v]
  exact lintegral_killedHeat_lt_top hR hAR hc₀ hI0 v v

lemma measurable_killedHeat_time {A : Set ℂ} (hA : IsOpen A) (u v : ℂ) :
    Measurable fun s : ℝ => killedHeat A s.toNNReal u v := by
  have hf : Measurable fun s : ℝ ↦ ((s.toNNReal, u, v) : ℝ≥0 × ℂ × ℂ) :=
    measurable_real_toNNReal.prodMk measurable_const
  exact Measurable.comp (g := fun x : ℝ≥0 × ℂ × ℂ ↦ killedHeat A x.1 x.2.1 x.2.2)
    (measurable_killedHeat hA) hf

open Classical in
/-- The `L²` class of the kernel (junk `0` if it is not square integrable). -/
def wndKernelL2 (A : Set ℂ) (I : Set ℝ) (v : ℂ) : WNSpace :=
  if h : MemLp (wndKernel A I v) 2 volume then h.toLp _ else 0

/-- **(eq-cov-tildeh)**: `⟪K_u, K_v⟫ = ∫_I p_A(s; u, v) ds`. -/
theorem inner_wndKernelL2 {A : Set ℂ} (hA : IsOpen A) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball c R) {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (u v : ℂ) :
    ⟪wndKernelL2 A I u, wndKernelL2 A I v⟫ = ∫ s in I, killedHeat A s.toNNReal u v := by
  have hI0' : I ⊆ Ioi 0 := hI0.trans (Ioi_subset_Ioi hc₀.le)
  have hu := memLp_wndKernel hA hR hAR hI hc₀ hI0 u
  have hv := memLp_wndKernel hA hR hAR hI hc₀ hI0 v
  rw [wndKernelL2, wndKernelL2, dite_eq_left_of_eq_true (eq_true hu), dite_eq_left_of_eq_true (eq_true hv), L2.inner_def]
  have h1 : (fun p => ⟪(hu.toLp _ : ℝ × ℂ → ℝ) p, (hv.toLp _ : ℝ × ℂ → ℝ) p⟫) =ᵐ[volume]
      fun p => wndKernel A I u p * wndKernel A I v p := by
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with p h1 h2
    rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
    simp [mul_comm]
  rw [integral_congr_ae h1, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun p => mul_nonneg (wndKernel_nonneg _ _ _ _) (wndKernel_nonneg _ _ _ _))
      ((measurable_wndKernel hA hI u).mul (measurable_wndKernel hA hI v)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => killedHeat_nonneg _ _ _ _)
      (measurable_killedHeat_time hA u v).aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_mul (wndKernel_nonneg _ _ _ _)]
  rw [lintegral_wndKernel_mul hA hI hI0' u v]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The white-noise field `√π ∫ 1_I(s) p_A(s/2; v, w) W(dw, ds)`. -/
def wnField (W : WNSpace → Ω → ℝ) (A : Set ℂ) (I : Set ℝ) (v : ℂ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (wndKernelL2 A I v) ω

/-- **DZZ (eq:WND_decomposition)**: `h̃_δ^{δ'}(v)` for `0 < δ < δ'`. -/
def tildeH (W : WNSpace → Ω → ℝ) (δ δ' : ℝ) (v : ℂ) (ω : Ω) : ℝ :=
  wnField W openSquare (Ioo (δ ^ 2) (δ' ^ 2)) v ω

/-- **DZZ (eq:WND_decomposition)** with `δ̃ = ∞`: `h̃_δ(v)`. -/
def tildeHInf (W : WNSpace → Ω → ℝ) (δ : ℝ) (v : ℂ) (ω : Ω) : ℝ :=
  wnField W openSquare (Ioi (δ ^ 2)) v ω

lemma openSquare_subset_ball : openSquare ⊆ Metric.ball (0 : ℂ) 2 := by
  intro z ⟨h1, h2, h3, h4⟩
  rw [Metric.mem_ball, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im z).trans_lt ?_
  rw [abs_of_pos h1, abs_of_pos h3]; linarith

/-- **(eq-cov-tildeh)** for the general field. -/
theorem cov_wnField (hW : IsWhiteNoise P W) {A : Set ℂ} (hA : IsOpen A) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hAR : A ⊆ Metric.ball c R) {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hI0 : I ⊆ Ioi c₀) (u v : ℂ) :
    cov[wnField W A I u, wnField W A I v; P] =
      Real.pi * ∫ s in I, killedHeat A s.toNNReal u v := by
  unfold wnField
  rw [covariance_const_mul_left, covariance_const_mul_right, hW.cov_eq,
    inner_wndKernelL2 hA hR hAR hI hc₀ hI0, ← mul_assoc, Real.mul_self_sqrt Real.pi_pos.le]

/-- **DZZ l. 512**: `Var(F(u) − F(v)) = π∫_I (p(u,u) − p(u,v)) + π∫_I (p(v,v) − p(u,v))`, in the
form `π(∫_I p(u,u) + ∫_I p(v,v) − 2∫_I p(u,v))`. -/
theorem variance_wnField_sub (hW : IsWhiteNoise P W) {A : Set ℂ} (hA : IsOpen A) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hAR : A ⊆ Metric.ball c R) {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hI0 : I ⊆ Ioi c₀) (u v : ℂ) :
    Var[fun ω => wnField W A I u ω - wnField W A I v ω; P] =
      Real.pi * ((∫ s in I, killedHeat A s.toNNReal u u) + (∫ s in I, killedHeat A s.toNNReal v v)
        - 2 * ∫ s in I, killedHeat A s.toNNReal u v) := by
  unfold wnField
  rw [variance_sqrtPi_sub hW, @norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_wndKernelL2 hA hR hAR hI hc₀ hI0,
    inner_wndKernelL2 hA hR hAR hI hc₀ hI0, inner_wndKernelL2 hA hR hAR hI hc₀ hI0]
  ring

end DZZ
end LQGMetric
