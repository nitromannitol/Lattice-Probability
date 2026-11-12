/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L7Eta at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Meas

/-!
# DZZ's truncated white-noise field `η` (eq:WND_decomposition-approximation; P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 444–447:
`η_δ^{δ̃}(v) = √π ∫_{𝕍 × (δ², δ̃²)} p_{𝕍 ∩ B_{r(s)}(v)}(s/2; v, w) W(dw, ds)`,
`r(s) = 4^{-1} s^{1/2} |log s^{-1}| ∧ 10^{-1}`.

* `etaRad s = r(s)`, `etaKernel I v (s, w) = 1_I(s) p_{𝕍 ∩ B(v, r(s))}(s/2; v, w)` (measurable by
  `measurable_killedHeat_inter_ball`), square integrable since `p_{𝕍 ∩ B} ≤ p_𝕍`.
* `etaField W I v = √π W(K^η_v)`, `eta W δ δ' v = η_δ^{δ'}(v)`, `etaInf W δ v = η_δ(v)`.
* `lintegral_etaKernel_sq`: Chapman–Kolmogorov at each fixed `s` gives
  `‖K^η_v‖² = ∫_I p_{𝕍 ∩ B(v, r(s))}(s; v, v) ds` (both factors use the same domain).
* `sq_norm_wnd_sub_eta_le`: `‖K^{h̃}_v − K^η_v‖² ≤ ∫_I (p_𝕍(s; v, v) − p_{𝕍∩B(v,r(s))}(s; v, v)) ds`,
  the first step of DZZ (eq-variance-truncation), l. 554–559 (from `0 ≤ k' ≤ k ⇒ (k − k')² ≤ k² − k'²`;
  own elementary step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

/-- DZZ's truncation radius `r(s) = 4^{-1} s^{1/2} |log s^{-1}| ∧ 10^{-1}` (l. 446). -/
def etaRad (s : ℝ) : ℝ := min (Real.sqrt s * |Real.log s⁻¹| / 4) (1 / 10)

lemma measurable_etaRad : Measurable etaRad := by
  unfold etaRad
  fun_prop

/-- The kernel of `η`: `(s, w) ↦ 1_I(s) p_{𝕍 ∩ B(v, r(s))}(s/2; v, w)`. -/
def etaKernel (I : Set ℝ) (v : ℂ) (p : ℝ × ℂ) : ℝ :=
  I.indicator (fun s => killedHeat (openSquare ∩ Metric.ball v (etaRad s)) (s / 2).toNNReal v p.2)
    p.1

lemma etaKernel_nonneg (I : Set ℝ) (v : ℂ) (p : ℝ × ℂ) : 0 ≤ etaKernel I v p :=
  indicator_nonneg (fun _ _ => killedHeat_nonneg _ _ _ _) _

lemma etaKernel_le (I : Set ℝ) (v : ℂ) (p : ℝ × ℂ) :
    etaKernel I v p ≤ wndKernel openSquare I v p := by
  unfold etaKernel wndKernel
  by_cases h : p.1 ∈ I
  · simp only [indicator_of_mem h]
    exact killedHeat_mono inter_subset_left _ _ _
  · simp [h]

lemma measurable_etaKernel {I : Set ℝ} (hI : MeasurableSet I) (v : ℂ) :
    Measurable (etaKernel I v) := by
  have e : etaKernel I v = (Prod.fst ⁻¹' I).indicator (fun p : ℝ × ℂ =>
      killedHeat (openSquare ∩ Metric.ball v (etaRad p.1)) (p.1 / 2).toNNReal v p.2) := by
    funext p
    by_cases h : p.1 ∈ I <;> simp [etaKernel, h]
  rw [e]
  refine Measurable.indicator ?_ (hI.preimage measurable_fst)
  exact measurable_killedHeat_inter_ball (c := fun _ => v) (z := fun _ => v)
    LQGMetric.isOpen_openSquare (measurable_fst.div_const 2).real_toNNReal measurable_const
    (measurable_etaRad.comp measurable_fst) measurable_const measurable_snd

theorem memLp_etaKernel {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (v : ℂ) : MemLp (etaKernel I v) 2 volume := by
  refine MemLp.of_le (memLp_wndKernel LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball hI hc₀ hI0 v) (measurable_etaKernel hI v).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (etaKernel_nonneg _ _ _),
    abs_of_nonneg (wndKernel_nonneg _ _ _ _)]
  exact etaKernel_le I v p

open Classical in
/-- The `L²` class of `η`'s kernel (junk `0` if not square integrable). -/
def etaKernelL2 (I : Set ℝ) (v : ℂ) : WNSpace :=
  if h : MemLp (etaKernel I v) 2 volume then h.toLp _ else 0

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The field `√π ∫ 1_I(s) p_{𝕍 ∩ B(v, r(s))}(s/2; v, w) W(dw, ds)`. -/
def etaField (W : WNSpace → Ω → ℝ) (I : Set ℝ) (v : ℂ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (etaKernelL2 I v) ω

/-- **DZZ (eq:WND_decomposition-approximation)**: `η_δ^{δ'}(v)`. -/
def eta (W : WNSpace → Ω → ℝ) (δ δ' : ℝ) (v : ℂ) (ω : Ω) : ℝ :=
  etaField W (Ioo (δ ^ 2) (δ' ^ 2)) v ω

/-- `η_δ(v)` (`δ̃ = ∞`). -/
def etaInf (W : WNSpace → Ω → ℝ) (δ : ℝ) (v : ℂ) (ω : Ω) : ℝ :=
  etaField W (Ioi (δ ^ 2)) v ω

/-- Chapman–Kolmogorov at fixed `s`: `∫ (K^η_v)² = ∫_I p_{𝕍 ∩ B(v, r(s))}(s; v, v) ds`. -/
theorem lintegral_etaKernel_sq {I : Set ℝ} (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) (v : ℂ) :
    ∫⁻ p, ENNReal.ofReal (etaKernel I v p) * ENNReal.ofReal (etaKernel I v p) =
      ∫⁻ s in I, ENNReal.ofReal
        (killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v) := by
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl,
    lintegral_prod (fun p => ENNReal.ofReal (etaKernel I v p) *
      ENNReal.ofReal (etaKernel I v p)) (Measurable.aemeasurable (by
        exact (measurable_etaKernel hI v).ennreal_ofReal.mul
          (measurable_etaKernel hI v).ennreal_ofReal)),
    ← lintegral_indicator hI]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ I
  · simp only [etaKernel, indicator_of_mem hs]
    have hs0 : (0 : ℝ) < s := hI0 hs
    have hD : IsOpen (openSquare ∩ Metric.ball v (etaRad s)) :=
      LQGMetric.isOpen_openSquare.inter Metric.isOpen_ball
    have ht : (s / 2).toNNReal ≠ 0 := by
      simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith
    have hsum : (s / 2).toNNReal + (s / 2).toNNReal = s.toNNReal := by
      rw [← Real.toNNReal_add (by linarith) (by linarith)]; ring_nf
    rw [← hsum, ofReal_killedHeat_add hD ht ht]
    refine lintegral_congr fun w => ?_
    rw [killedHeat_symm hD _ v w]
  · simp [etaKernel, hs]

end DZZ
end LQGMetric
