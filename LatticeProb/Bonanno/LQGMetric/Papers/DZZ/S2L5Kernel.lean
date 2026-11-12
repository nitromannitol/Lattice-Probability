/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L5Kernel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
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

open Classical in
/-- The `L²` class of the kernel (junk `0` if it is not square integrable). -/
def wndKernelL2 (A : Set ℂ) (I : Set ℝ) (v : ℂ) : WNSpace :=
  if h : MemLp (wndKernel A I v) 2 volume then h.toLp _ else 0

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma openSquare_subset_ball : openSquare ⊆ Metric.ball (0 : ℂ) 2 := by
  intro z ⟨h1, h2, h3, h4⟩
  rw [Metric.mem_ball, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im z).trans_lt ?_
  rw [abs_of_pos h1, abs_of_pos h3]; linarith

end DZZ
end LQGMetric
