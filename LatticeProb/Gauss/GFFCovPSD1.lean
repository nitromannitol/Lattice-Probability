import Mathlib
import LatticeProb.Gauss.GFFCovSymm

/-!
# Positive semidefiniteness of the whole-plane covariance, 1: smearing representations

Each admissible observable `o` smears a function as an integral
over a σ-finite measure space: `o.smear f = ∫ a, w a * f (p a) ∂lam`. The pairing `(h, φ)` is represented on `ℂ` by
`w = φ`, `p = id` (Lebesgue measure restricted to a ball containing `supp φ`); the circle average `h_r(z)` is represented
on `ℝ` by `lam = Lebesgue measure on (0, 2π]`, `w = (2π)⁻¹`, `p θ = circleMap z r θ` (`Real.circleAverage_def`).

This file proves the integrability of the bilinear kernel `wholePlaneCov` against two representations, the a.e.
off-diagonality of the points, and the double-integral formula for the covariance. The uniform logarithmic estimate
`logU` is a field of `SmearRep`; its two instances (pairing, circle) are constructed in `LatticeProb.Gauss.GFFCovPSD2`.
The local integrability of `log` and the dominating functions are those of `LatticeProb.Gauss.GFFCovSymm`
(Duplantier-Sheffield, arXiv:0808.1560, Section 3; Armitage-Gardiner for the logarithmic potential).
-/

open MeasureTheory Metric Set Filter Topology
open scoped Real

namespace LatticeProb.Gauss

namespace GFFCovPSD

open GFFCovSymm

/-- A smearing representation of an admissible observable `o`: a σ-finite measure `lam` on a type `α`, weights
`w`, points `p`, with `o.smear f = ∫ a, w a * f (p a) ∂lam`. The weights are integrable, supported in a bounded set of
points, and the logarithmic singularity is uniformly integrable against the representation (`logU`). -/
structure SmearRep (o : GFFObservable) where
  α : Type
  [inst : MeasurableSpace α]
  lam : Measure α
  sfin : SFinite lam
  w : α → ℝ
  p : α → ℂ
  w_meas : Measurable w
  w_int : Integrable w lam
  w_supp : ∃ R : ℝ, ∀ a, w a ≠ 0 → ‖p a‖ ≤ R
  p_meas : Measurable p
  atom : ∀ y : ℂ, lam {a | p a = y} = 0
  smear_eq : ∀ f : ℂ → ℝ, o.smear f = ∫ a, w a * f (p a) ∂lam
  logU : ∀ R : ℝ, ∃ C : ℝ, ∀ y : ℂ, ‖y‖ ≤ R →
    Integrable (fun a => |w a| * |Real.log ‖p a - y‖|) lam ∧ ∫ a, |w a| * |Real.log ‖p a - y‖| ∂lam ≤ C

attribute [instance] SmearRep.inst

instance sfinSmearRep {o : GFFObservable} (S : SmearRep o) : SFinite S.lam := S.sfin

namespace SmearRep

variable {o o' : GFFObservable}

/-- The bilinear integrand of the covariance of two representations, on `X.α × Y.α`. -/
noncomputable def kern (X : SmearRep o) (Y : SmearRep o') (q : X.α × Y.α) : ℝ :=
  X.w q.1 * Y.w q.2 * wholePlaneCov (X.p q.1) (Y.p q.2)

lemma kern_measurable (X : SmearRep o) (Y : SmearRep o') : Measurable (kern X Y) :=
  ((X.w_meas.comp measurable_fst).mul (Y.w_meas.comp measurable_snd)).mul
    (measurable_wholePlaneCov_pair.comp ((X.p_meas.comp measurable_fst).prodMk (Y.p_meas.comp measurable_snd)))

/-- Pointwise bound of the kernel on the supports: `|K(x, y)| ≤ 2 log R + |log |x - y||` for `|x|, |y| ≤ R`. -/
lemma abs_kern_le (X : SmearRep o) (Y : SmearRep o') {R : ℝ} (hR : 1 ≤ R) (a : X.α) (b : Y.α)
    (ha : ‖X.p a‖ ≤ R ∨ X.w a = 0) (hb : ‖Y.p b‖ ≤ R ∨ Y.w b = 0) :
    |kern X Y (a, b)| ≤ |X.w a| * |Y.w b| * (2 * Real.log R + |Real.log ‖X.p a - Y.p b‖|) := by
  unfold kern
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_wholePlaneCov_le hR ha hb) (by positivity)
    · simp [hb]
  · simp [ha]

/-- Integrability of a bilinear function dominated by a section bound: if
`|F(a,b)| ≤ |w_X a| (c |w_Y b| + |w_Y b| |log ‖p_Y b - p_X a‖|)`, then `F` is integrable on the product. -/
lemma integrable_of_bound (X : SmearRep o) (Y : SmearRep o') (F : X.α × Y.α → ℝ) (hF : Measurable F) (c : ℝ)
    (hbd : ∀ a b, |F (a, b)| ≤ |X.w a| * (c * |Y.w b| + |Y.w b| * |Real.log ‖Y.p b - X.p a‖|)) :
    Integrable F (X.lam.prod Y.lam) := by
  obtain ⟨RX, hRX⟩ := X.w_supp
  have hRX' : RX ≤ max 1 RX := le_max_right _ _
  obtain ⟨CY, hCY⟩ := Y.logU (max 1 RX)
  have hsec : ∀ a : X.α,
      Integrable (fun b => |X.w a| * (c * |Y.w b| + |Y.w b| * |Real.log ‖Y.p b - X.p a‖|)) Y.lam ∧
      ∫ b, |X.w a| * (c * |Y.w b| + |Y.w b| * |Real.log ‖Y.p b - X.p a‖|) ∂Y.lam ≤
        |X.w a| * (c * ∫ b, |Y.w b| ∂Y.lam + CY) := by
    intro a
    by_cases ha : X.w a = 0
    · simp [ha]
    · have hXa : ‖X.p a‖ ≤ max 1 RX := (hRX a ha).trans hRX'
      obtain ⟨hint, hbound⟩ := hCY (X.p a) hXa
      have hw : Integrable (fun b => c * |Y.w b|) Y.lam := Y.w_int.abs.const_mul c
      have hsum : Integrable (fun b => c * |Y.w b| + |Y.w b| * |Real.log ‖Y.p b - X.p a‖|) Y.lam := hw.add hint
      refine ⟨hsum.const_mul |X.w a|, ?_⟩
      rw [integral_const_mul, integral_add hw hint, integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      linarith
  have hmeas : ∀ a : X.α, Measurable (fun b => F (a, b)) := fun a => hF.comp measurable_prodMk_left
  refine (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨ae_of_all _ fun a => ?_, ?_⟩
  · refine Integrable.mono' (hsec a).1 (hmeas a).aestronglyMeasurable (ae_of_all _ fun b => ?_)
    rw [Real.norm_eq_abs]
    exact hbd a b
  · have hmeas2 : AEStronglyMeasurable (fun a => ∫ b, ‖F (a, b)‖ ∂Y.lam) X.lam :=
      (hF.norm.stronglyMeasurable.integral_prod_right' (ν := Y.lam)).aestronglyMeasurable
    refine Integrable.mono' (X.w_int.abs.mul_const (c * ∫ b, |Y.w b| ∂Y.lam + CY)) hmeas2
      (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun b => norm_nonneg _)]
    refine le_trans ?_ (hsec a).2
    refine integral_mono_of_nonneg (ae_of_all _ fun b => norm_nonneg _) (hsec a).1 (ae_of_all _ fun b => ?_)
    dsimp only
    rw [Real.norm_eq_abs]
    exact hbd a b

/-- The kernel is integrable against two representations. -/
lemma integrable_kern (X : SmearRep o) (Y : SmearRep o') : Integrable (kern X Y) (X.lam.prod Y.lam) := by
  obtain ⟨RX, hRX⟩ := X.w_supp
  obtain ⟨RY, hRY⟩ := Y.w_supp
  have hR : 1 ≤ max 1 (max RX RY) := le_max_left _ _
  have hRX' : RX ≤ max 1 (max RX RY) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRY' : RY ≤ max 1 (max RX RY) := le_trans (le_max_right _ _) (le_max_right _ _)
  refine integrable_of_bound X Y (kern X Y) (kern_measurable X Y) (2 * Real.log (max 1 (max RX RY))) fun a b => ?_
  by_cases ha : X.w a = 0
  · simp [kern, ha]
  by_cases hb : Y.w b = 0
  · simp [kern, hb]
  have h := abs_kern_le X Y hR a b (Or.inl ((hRX a ha).trans hRX')) (Or.inl ((hRY b hb).trans hRY'))
  rw [norm_sub_rev (Y.p b) (X.p a)]
  exact h.trans (le_of_eq (by ring))

/-- The logarithmic integrand `w_X w_Y log ‖p_X - p_Y‖` is integrable on the product. -/
lemma integrable_log_mul (X : SmearRep o) (Y : SmearRep o') :
    Integrable (fun q : X.α × Y.α => X.w q.1 * Y.w q.2 * Real.log ‖X.p q.1 - Y.p q.2‖) (X.lam.prod Y.lam) := by
  refine integrable_of_bound X Y _ ?_ 0 fun a b => ?_
  · exact ((X.w_meas.comp measurable_fst).mul (Y.w_meas.comp measurable_snd)).mul
      (Real.measurable_log.comp (((X.p_meas.comp measurable_fst).sub (Y.p_meas.comp measurable_snd)).norm))
  · rw [norm_sub_rev (Y.p b) (X.p a)]
    simp only [zero_mul, zero_add, abs_mul]
    exact le_of_eq (by ring)

/-- The covariance of two observables as the integral of the kernel against the product of the representations. -/
lemma wholePlaneGFFCov_eq_integral (X : SmearRep o) (Y : SmearRep o') :
    wholePlaneGFFCov o o' = ∫ q, kern X Y q ∂(X.lam.prod Y.lam) := by
  rw [integral_prod _ (integrable_kern X Y)]
  unfold wholePlaneGFFCov
  rw [X.smear_eq]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only
  rw [Y.smear_eq, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  simp only [kern]
  ring

/-- The points of the two representations coincide only on a null set of the product measure. -/
lemma ae_ne (X : SmearRep o) (Y : SmearRep o') : ∀ᵐ q ∂(X.lam.prod Y.lam), X.p q.1 ≠ Y.p q.2 := by
  have hS : MeasurableSet {q : X.α × Y.α | X.p q.1 = Y.p q.2} :=
    measurableSet_eq_fun (X.p_meas.comp measurable_fst) (Y.p_meas.comp measurable_snd)
  have h0 : (X.lam.prod Y.lam) {q : X.α × Y.α | X.p q.1 = Y.p q.2} = 0 := by
    rw [Measure.measure_prod_null hS]
    refine ae_of_all _ fun a => ?_
    have hset : Prod.mk a ⁻¹' {q : X.α × Y.α | X.p q.1 = Y.p q.2} = {b | Y.p b = X.p a} := by
      ext b
      simp [eq_comm]
    simp only [Pi.zero_apply]
    rw [hset]
    exact Y.atom (X.p a)
  exact measure_eq_zero_iff_ae_notMem.1 h0

/-- Off the diagonal, `wholePlaneCov` splits into the two `log max(|·|, 1)` terms and `-log |x - y|`. -/
lemma kern_eq_log {X : SmearRep o} {Y : SmearRep o'} {q : X.α × Y.α} (h : X.p q.1 ≠ Y.p q.2) :
    kern X Y q = X.w q.1 * Y.w q.2 *
      (Real.log (max ‖X.p q.1‖ 1) + Real.log (max ‖Y.p q.2‖ 1) - Real.log ‖X.p q.1 - Y.p q.2‖) := by
  unfold kern
  rw [wholePlaneCov_eq_log_sub h]

end SmearRep

end GFFCovPSD

end LatticeProb.Gauss
