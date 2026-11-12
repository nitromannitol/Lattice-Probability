/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L7Trunc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Eta
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatMeas

/-!
# DZZ (eq-variance-truncation), first steps (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Lemma 2.7, l. 554–559:
"`Var Δ_i(v) = O(1) P(τ_i ≤ 2^{-2i}) = O(1) e^{−Ω(i²)}`", where `τ_i` is the exit time of the
bridge from a ball. Here:

* `killedHeat_sub_inter_ball_le`: `p_A(t; v, v) − p_{A ∩ B(v, r)}(t; v, v) ≤ (2πt)⁻¹ · 4e^{−2(r/3)²/t}`:
  the difference is `p_t(v, v)` times the probability that the bridge from `v` to `v` stays in `A`
  but leaves `B(v, r)`; then one coordinate of `B_s − (s/t)B_t` exceeds `r/3` in absolute value,
  and the reflection principle (`measureReal_bridge_max_gt`, DZZ l. 491–498) bounds each of the
  four cases by `e^{−2(r/3)²/t}`. (DZZ use the sup-norm ball of radius `i2^{-i}/8`; same argument.)
* `variance_wnField_sub_etaField_le`: `Var(h̃_I(v) − η_I(v)) ≤ π ∫_I (p_𝕍(s; v, v) −
  p_{𝕍 ∩ B(v, r(s))}(s; v, v)) ds` (own elementary step: `0 ≤ k' ≤ k ⇒ (k − k')² ≤ k² − k'²`, and
  Chapman–Kolmogorov for both kernels).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

/-- The bridge from `v` to `v` leaves `B(v, r)`: `p_A(t;v,v) − p_{A∩B(v,r)}(t;v,v) ≤
(2πt)⁻¹ · 4 e^{−2(r/3)²/t}` (DZZ l. 557, via the reflection principle). -/
theorem killedHeat_sub_inter_ball_le {t : ℝ≥0} (ht : t ≠ 0) (A : Set ℂ) (v : ℂ) {r : ℝ}
    (hr : 0 < r) :
    killedHeat A t v v - killedHeat (A ∩ Metric.ball v r) t v v ≤
      (2 * Real.pi * t)⁻¹ * (4 * Real.exp (-(2 * (r / 3) ^ 2 / t))) := by
  set X := stdBridge t
  have hX : IsPlanarBridge t X P2 := isPlanarBridge_stdBridge ht
  have hY := isPlanarBridge_neg hX
  haveI := hX.gauss.isProbabilityMeasure
  have hr3 : 0 < r / 3 := by positivity
  set EA := bridgeEvent A t v v X
  set EB := bridgeEvent (A ∩ Metric.ball v r) t v v X
  set F : Bool → (ℝ≥0 → Ω2 → ℂ) → Set Ω2 := fun b Z =>
    {ω | ∃ s : ℝ≥0, s ≤ t ∧ r / 3 < coordProc Z (b, s) ω}
  have hsub : EA \ EB ⊆ (F false X ∪ F true X) ∪ (F false (fun s ω => -X s ω) ∪
      F true (fun s ω => -X s ω)) := by
    rintro ω ⟨hA, hB⟩
    simp only [EA, EB, bridgeEvent, mem_setOf_eq, not_forall] at hA hB
    obtain ⟨s, hs, hsB⟩ := hB
    have hpath : bridgePath t v v X s ω = v + X s ω := by simp [bridgePath]
    have hnot : X s ω ∉ Metric.ball (0 : ℂ) r := by
      intro h
      apply hsB
      refine ⟨hA s hs, ?_⟩
      rw [hpath, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      simpa using h
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hnot
    have hle := Complex.norm_le_abs_re_add_abs_im (X s ω)
    simp only [F, mem_union, mem_setOf_eq, coordProc_false, coordProc_true, Complex.neg_re,
      Complex.neg_im]
    rcases le_total (r / 2) |(X s ω).re| with h | h
    · rcases le_or_gt 0 (X s ω).re with h0 | h0
      · rw [abs_of_nonneg h0] at h
        exact Or.inl (Or.inl ⟨s, hs, by linarith⟩)
      · rw [abs_of_neg h0] at h
        exact Or.inr (Or.inl ⟨s, hs, by linarith⟩)
    · have h' : r / 2 ≤ |(X s ω).im| := by linarith
      rcases le_or_gt 0 (X s ω).im with h0 | h0
      · rw [abs_of_nonneg h0] at h'
        exact Or.inl (Or.inr ⟨s, hs, by linarith⟩)
      · rw [abs_of_neg h0] at h'
        exact Or.inr (Or.inr ⟨s, hs, by linarith⟩)
  have hq : P2.real EA - P2.real EB ≤ 4 * Real.exp (-(2 * (r / 3) ^ 2 / t)) := by
    have h1 : P2.real EA ≤ P2.real (EA \ EB) + P2.real EB :=
      (measureReal_mono (fun ω hω => by
        by_cases h : ω ∈ EB
        · exact Or.inr h
        · exact Or.inl ⟨hω, h⟩) (measure_ne_top P2 _)).trans (measureReal_union_le _ _)
    have h2 := (measureReal_mono hsub (measure_ne_top P2 _)).trans
      ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _)
        (measureReal_union_le _ _)))
    have b1 := measureReal_bridge_max_gt ht hX false hr3
    have b2 := measureReal_bridge_max_gt ht hX true hr3
    have b3 := measureReal_bridge_max_gt ht hY false hr3
    have b4 := measureReal_bridge_max_gt ht hY true hr3
    simp only [F] at h2
    linarith
  have hh : heatKernel t v v = (2 * Real.pi * t)⁻¹ := by simp [heatKernel]
  have hh0 : 0 ≤ (2 * Real.pi * t)⁻¹ := by positivity
  rw [killedHeat, killedHeat, hh, ← mul_sub]
  exact mul_le_mul_of_nonneg_left hq hh0

lemma integral_sq_eq_of_lintegral {f : ℝ × ℂ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ s, 0 ≤ g s) {I : Set ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (f x) = ∫⁻ s in I, ENNReal.ofReal (g s)) :
    ∫ x, f x ^ 2 = ∫ s in I, g s := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (f x))
      (hf.pow_const 2).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable]
  congr 1
  simp_rw [sq, ENNReal.ofReal_mul (hf0 _)]
  exact h

lemma measurable_killedHeat_eta_time (v : ℂ) :
    Measurable fun s : ℝ => killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v :=
  measurable_killedHeat_inter_ball (c := fun _ => v) (z := fun _ => v) (w := fun _ => v)
    LQGMetric.isOpen_openSquare measurable_real_toNNReal measurable_const measurable_etaRad
    measurable_const measurable_const

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- First step of **(eq-variance-truncation)**:
`Var(h̃_I(v) − η_I(v)) ≤ π ∫_I (p_𝕍(s; v, v) − p_{𝕍 ∩ B(v, r(s))}(s; v, v)) ds`. -/
theorem variance_wnField_sub_etaField_le (hW : IsWhiteNoise P W) {I : Set ℝ}
    (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀) (hI0 : I ⊆ Ioi c₀) (v : ℂ) :
    Var[fun ω => wnField W openSquare I v ω - etaField W I v ω; P] ≤
      Real.pi * ((∫ s in I, killedHeat openSquare s.toNNReal v v) -
        ∫ s in I, killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v) := by
  have hI0' : I ⊆ Ioi 0 := hI0.trans (Ioi_subset_Ioi hc₀.le)
  have hu := memLp_wndKernel LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball hI hc₀ hI0 v
  have he := memLp_etaKernel hI hc₀ hI0 v
  unfold wnField etaField
  rw [variance_sqrtPi_sub hW, wndKernelL2, etaKernelL2, dite_eq_left_of_eq_true (eq_true hu),
    dite_eq_left_of_eq_true (eq_true he), sq_norm_toLp_sub hu he]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  have hku := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).1 hu
  have hke := (memLp_two_iff_integrable_sq he.aestronglyMeasurable).1 he
  have h1 := integral_sq_eq_of_lintegral (measurable_wndKernel LQGMetric.isOpen_openSquare hI v)
    (wndKernel_nonneg _ _ _) (measurable_killedHeat_time LQGMetric.isOpen_openSquare v v)
    (fun s => killedHeat_nonneg _ _ _ _)
    (lintegral_wndKernel_mul LQGMetric.isOpen_openSquare hI hI0' v v)
  have h2 := integral_sq_eq_of_lintegral (measurable_etaKernel hI v) (etaKernel_nonneg _ _)
    (measurable_killedHeat_eta_time v) (fun s => killedHeat_nonneg _ _ _ _)
    (lintegral_etaKernel_sq hI hI0' v)
  rw [← h1, ← h2, ← integral_sub hku hke]
  refine integral_mono ((hu.sub he).integrable_sq) (hku.sub hke) fun p => ?_
  have a0 := etaKernel_nonneg I v p
  have a1 := etaKernel_le I v p
  simp only [Pi.sub_apply]
  nlinarith

end DZZ
end LQGMetric
