/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.ReverseHolo at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseODE
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Holomorphy and injectivity of the reverse Loewner map

For `W` continuous and `T ≥ 0`, writing `f_t := revMap W t`:

* `revMap_sub_revMap_eq`: `f_t w - f_t z = (w - z) * exp (∫₀ᵗ 2 / (f_s w * f_s z))`.
* `injOn_revMap`, `hasDerivAt_revMap`, `differentiableOn_revMap`, `deriv_revMap`,
  `deriv_revMap_ne_zero`, `log_norm_deriv_revMap`.

Method: `D_t := f_t w - f_t z` solves `D' = a D` with `a = 2/(f w f z)`, so
`D_t exp(-∫₀ᵗ a)` has zero right derivative. The derivative follows from the slope formula
and a Lipschitz estimate for the exponent in `w`.
-/

noncomputable section

open Complex Filter MeasureTheory intervalIntegral
open scoped Topology

namespace QuantumZipper

namespace ReverseHolo

private lemma icc_mem_nhdsWithin_Ici' {a b t : ℝ} (ht1 : a ≤ t) (ht2 : t < b) :
    Set.Icc a b ∈ 𝓝[Set.Ici t] t := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Iio b, isOpen_Iio, ht2, fun x hx => ?_⟩
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici] at hx
  exact ⟨le_trans ht1 hx.2, le_of_lt hx.1⟩

end ReverseHolo

open ReverseHolo

theorem continuousOn_revMap_time (W : ℝ → ℝ) (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {T : ℝ} (hT : 0 ≤ T) : ContinuousOn (fun s => revMap W s z) (Set.Icc 0 T) := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz T hT
  exact hu.1.congr fun s hs => revMap_eq W hW z hs.1 hs.2 hu

theorem revMap_ne_zero_of_im {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {s : ℝ} (hs : 0 ≤ s) : revMap W s z ≠ 0 := by
  intro h
  have := im_le_im_revMap W hW z hz hs
  rw [h] at this; simp at this; linarith

theorem intervalIntegrable_revMap_prod (W : ℝ → ℝ) (hW : Continuous W) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => (2 : ℂ) / (revMap W s w * revMap W s z)) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hT]
  exact continuousOn_const.div ((continuousOn_revMap_time W hW hw hT).mul
    (continuousOn_revMap_time W hW hz hT)) fun s hs =>
      mul_ne_zero (revMap_ne_zero_of_im hW hw hs.1) (revMap_ne_zero_of_im hW hz hs.1)

/-- Key identity: the difference of two reverse flows solves a linear equation. -/
theorem revMap_sub_revMap_eq (W : ℝ → ℝ) (hW : Continuous W) {z w : ℂ} (hz : z ∈ H)
    (hw : w ∈ H) {T : ℝ} (hT : 0 ≤ T) :
    revMap W T w - revMap W T z =
      (w - z) * Complex.exp (∫ s in (0 : ℝ)..T, 2 / (revMap W s w * revMap W s z)) := by
  have hz' : 0 < z.im := hz
  have hw' : 0 < w.im := hw
  obtain ⟨uz, huz⟩ := exists_isReverseSol W hW z hz' T hT
  obtain ⟨uw, huw⟩ := exists_isReverseSol W hW w hw' T hT
  have hEz : Set.EqOn (fun s => revMap W s z) uz (Set.Icc 0 T) :=
    fun s hs => revMap_eq W hW z hs.1 hs.2 huz
  have hEw : Set.EqOn (fun s => revMap W s w) uw (Set.Icc 0 T) :=
    fun s hs => revMap_eq W hW w hs.1 hs.2 huw
  have hne : ∀ {u : ℝ → ℂ} {x : ℂ}, IsReverseSol W x T u → ∀ s ∈ Set.Icc (0 : ℝ) T, u s ≠ 0 := by
    intro u x hu s hs h0
    have := (hu.2 s hs).1
    rw [h0] at this; simp at this
  set a : ℝ → ℂ := fun s => 2 / (uw s * uz s) with ha
  have hacont : ContinuousOn a (Set.Icc 0 T) :=
    continuousOn_const.div (huw.1.mul huz.1) fun s hs => mul_ne_zero (hne huw s hs) (hne huz s hs)
  set A : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, a s with hA
  have hAder : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt A (a t) (Set.Icc 0 T) t := by
    intro t ht
    have : Fact (t ∈ Set.Icc (0 : ℝ) T) := ⟨ht⟩
    have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc_right ht.2
    exact intervalIntegral.integral_hasDerivWithinAt_right
      ((hacont.mono hsub).intervalIntegrable)
      (hacont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hacont t ht)
  set E : ℝ → ℂ := fun t => ((uw t + (W t : ℂ)) - (uz t + (W t : ℂ))) * Complex.exp (-A t)
    with hE
  have hEder : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt E 0 (Set.Icc 0 T) t := by
    intro t ht
    have h1 := ((isReverseSol_hasDerivWithinAt W w T huw ht).sub
      (isReverseSol_hasDerivWithinAt W z T huz ht)).mul (hAder t ht).neg.cexp
    have n1 := hne huw t ht
    have n2 := hne huz t ht
    have hval : (-2 / uw t - -2 / uz t) * Complex.exp (-A t) +
        ((uw t + (W t : ℂ)) - (uz t + (W t : ℂ))) * (Complex.exp (-A t) * -a t) = 0 := by
      simp only [ha]
      field_simp
      ring
    exact h1.congr_deriv hval
  have hconst := constant_of_has_deriv_right_zero
    (fun t ht => (hEder t ht).continuousWithinAt)
    (fun t ht => (hEder t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (icc_mem_nhdsWithin_Ici' ht.1 ht.2)) T ⟨hT, le_rfl⟩
  have hw0 := (huw.2 0 ⟨le_rfl, hT⟩).2
  have hz0 := (huz.2 0 ⟨le_rfl, hT⟩).2
  simp only [hE, hA, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [hw0, hz0, intervalIntegral.integral_same, intervalIntegral.integral_same] at hconst
  have hint : (∫ s in (0 : ℝ)..T, 2 / (revMap W s w * revMap W s z)) = A T := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hT] at hs
    simp only [ha, hEz hs, hEw hs]
  have e1 : revMap W T w = uw T := hEw ⟨hT, le_rfl⟩
  have e2 : revMap W T z = uz T := hEz ⟨hT, le_rfl⟩
  rw [hint, e1, e2]
  have hx : uw T - uz T = (uw T + W T - (uz T + W T)) := by ring
  rw [hx, ← mul_one (uw T + W T - (uz T + W T)), ← Complex.exp_zero, ← neg_add_cancel (A T),
    Complex.exp_add, ← mul_assoc, hconst]
  ring

theorem injOn_revMap (W : ℝ → ℝ) (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    Set.InjOn (revMap W T) H := by
  intro z hz w hw h
  have := revMap_sub_revMap_eq W hW hz hw hT
  rw [h, sub_self] at this
  rcases mul_eq_zero.mp this.symm with h0 | h0
  · exact (sub_eq_zero.mp h0).symm
  · exact absurd h0 (Complex.exp_ne_zero _)

/-- Lipschitz bound for the flow in the initial point, for `w` with `w.im ≥ δ/2`. -/
private lemma norm_revMap_sub_le_aux (W : ℝ → ℝ) (hW : Continuous W) {z w : ℂ}
    (hz : 0 < z.im) (hwz : z.im / 2 ≤ w.im) {s : ℝ} (hs : 0 ≤ s) :
    ‖revMap W s w - revMap W s z‖ ≤ ‖w - z‖ * Real.exp (4 / z.im ^ 2 * s) := by
  have hw : 0 < w.im := by linarith
  rw [revMap_sub_revMap_eq W hW (show z ∈ H from hz) (show w ∈ H from hw) hs, norm_mul,
    Complex.norm_exp]
  gcongr
  refine (Complex.re_le_norm _).trans ?_
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_).trans_eq
    (by rw [sub_zero, abs_of_nonneg hs])
  rw [Set.uIoc_of_le hs] at hr
  have h1 := im_le_im_revMap W hW w hw hr.1.le
  have h2 := im_le_im_revMap W hW z hz hr.1.le
  have n1 : z.im / 2 ≤ ‖revMap W r w‖ := hwz.trans (h1.trans (Complex.im_le_norm _))
  have n2 : z.im ≤ ‖revMap W r z‖ := h2.trans (Complex.im_le_norm _)
  rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_div_iff₀
    (mul_pos (by linarith) (by linarith)) (by positivity)]
  have := mul_le_mul n1 n2 hz.le (by positivity)
  nlinarith

theorem hasDerivAt_revMap (W : ℝ → ℝ) (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H) :
    HasDerivAt (revMap W T) (Complex.exp (∫ s in (0 : ℝ)..T, 2 / (revMap W s z) ^ 2)) z := by
  have hz' : 0 < z.im := hz
  set δ := z.im with hδ
  set I : ℂ → ℂ := fun w => ∫ s in (0 : ℝ)..T, 2 / (revMap W s w * revMap W s z) with hI
  have hIz : (∫ s in (0 : ℝ)..T, 2 / (revMap W s z) ^ 2) = I z := by simp [hI, sq]
  set M := Real.exp (4 / δ ^ 2 * T)
  set K := 2 * M / (δ / 2 * δ * δ) * T
  have hlip : ∀ w, ‖w - z‖ < δ / 2 → ‖I w - I z‖ ≤ K * ‖w - z‖ := by
    intro w hwd
    have hwz : δ / 2 ≤ w.im := by
      have := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im, abs_le] at this
      linarith
    have hw : 0 < w.im := by linarith
    simp only [hI]
    rw [← intervalIntegral.integral_sub (intervalIntegrable_revMap_prod W hW hz' hw hT)
      (intervalIntegrable_revMap_prod W hW hz' hz' hT)]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 2 * M / (δ / 2 * δ * δ) * ‖w - z‖) fun r hr => ?_).trans_eq
      (by rw [sub_zero, abs_of_nonneg hT]; ring)
    rw [Set.uIoc_of_le hT] at hr
    have h1 := im_le_im_revMap W hW w hw hr.1.le
    have h2 := im_le_im_revMap W hW z hz' hr.1.le
    have n1 : δ / 2 ≤ ‖revMap W r w‖ := hwz.trans (h1.trans (Complex.im_le_norm _))
    have n2 : δ ≤ ‖revMap W r z‖ := h2.trans (Complex.im_le_norm _)
    have p0 : revMap W r w ≠ 0 := revMap_ne_zero_of_im hW hw hr.1.le
    have q0 : revMap W r z ≠ 0 := revMap_ne_zero_of_im hW hz' hr.1.le
    have hL := norm_revMap_sub_le_aux W hW hz' hwz hr.1.le
    have hM : Real.exp (4 / δ ^ 2 * r) ≤ M :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2 (by positivity))
    have hrw : 2 / (revMap W r w * revMap W r z) - 2 / (revMap W r z * revMap W r z)
        = 2 * (revMap W r z - revMap W r w) / (revMap W r w * revMap W r z * revMap W r z) := by
      field_simp
    rw [hrw, norm_div, norm_mul, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num,
      norm_sub_rev, div_le_iff₀ (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))]
    have hden := mul_le_mul (mul_le_mul n1 n2 (by positivity) (by positivity)) n2
      (by positivity) (by positivity)
    have hnum : ‖revMap W r w - revMap W r z‖ ≤ ‖w - z‖ * M :=
      hL.trans (mul_le_mul_of_nonneg_left hM (norm_nonneg _))
    have e : 2 * M / (δ / 2 * δ * δ) * ‖w - z‖ * (‖revMap W r w‖ * ‖revMap W r z‖ *
        ‖revMap W r z‖) ≥ 2 * M / (δ / 2 * δ * δ) * ‖w - z‖ * (δ / 2 * δ * δ) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    have e2 : 2 * M / (δ / 2 * δ * δ) * ‖w - z‖ * (δ / 2 * δ * δ) = 2 * (‖w - z‖ * M) := by
      field_simp
    nlinarith
  have hcont : Tendsto I (𝓝 z) (𝓝 (I z)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hK : 0 ≤ K := by positivity
    filter_upwards [Metric.ball_mem_nhds z (show 0 < min (δ / 2) (ε / (K + 1)) by positivity)]
      with w hw
    rw [Metric.mem_ball, dist_eq_norm, lt_min_iff] at hw
    rw [dist_eq_norm]
    refine (hlip w hw.1).trans_lt ?_
    calc K * ‖w - z‖ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hw.2.le hK
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  rw [hasDerivAt_iff_tendsto_slope, hIz]
  refine ((Complex.continuous_exp.tendsto _).comp hcont).mono_left nhdsWithin_le_nhds
    |>.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z (show 0 < δ by positivity)),
    self_mem_nhdsWithin] with w hw hwne
  have hwH : w ∈ H := by
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := Complex.abs_im_le_norm (w - z)
    rw [Complex.sub_im, abs_le] at this
    show 0 < w.im
    linarith
  have hsub : w - z ≠ 0 := sub_ne_zero.mpr hwne
  rw [slope_def_field, revMap_sub_revMap_eq W hW hz hwH hT]
  simp only [Function.comp, hI]
  field_simp

theorem differentiableOn_revMap (W : ℝ → ℝ) (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    DifferentiableOn ℂ (revMap W T) H := fun _ hz =>
  (hasDerivAt_revMap W hW hT hz).differentiableAt.differentiableWithinAt

theorem deriv_revMap (W : ℝ → ℝ) (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H) :
    deriv (revMap W T) z = Complex.exp (∫ s in (0 : ℝ)..T, 2 / (revMap W s z) ^ 2) :=
  (hasDerivAt_revMap W hW hT hz).deriv

theorem deriv_revMap_ne_zero (W : ℝ → ℝ) (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H) : deriv (revMap W T) z ≠ 0 := by
  rw [deriv_revMap W hW hT hz]; exact Complex.exp_ne_zero _

theorem log_norm_deriv_revMap (W : ℝ → ℝ) (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H) :
    Real.log ‖deriv (revMap W T) z‖ = (∫ s in (0 : ℝ)..T, 2 / (revMap W s z) ^ 2).re := by
  rw [deriv_revMap W hW hT hz, Complex.norm_exp, Real.log_exp]

end QuantumZipper
