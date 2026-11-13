import LatticeProb.Prob.GaussianLogSobolevTensor
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Smooth approximation of densities with Lipschitz logarithm

This file states and proves `LatticeProb.LipschitzLogApprox n` in every dimension: a positive
probability density of the standard Gaussian product law on `Fin n → ℝ` with `C`-Lipschitz
logarithm and finite entropy is the entropy limit of `C¹` positive densities of mass one whose
logarithms are again `C`-Lipschitz. It is the approximation step of the proof of
`LatticeProb.gaussianLogSobolev_holds`.

Let `h > 0` have a `C`-Lipschitz logarithm. For a normalised smooth bump `φ` supported in the ball
of radius `r`, the convolution `g = φ ⋆ h` satisfies, pointwise,

* `e^{-C r} h ≤ g ≤ e^{C r} h`, since `h (x - t) / h x ∈ [e^{-C ‖t‖}, e^{C ‖t‖}]`;
* `g y ≤ e^{C ‖y - x‖} g x`, since `h (y - t) ≤ e^{C ‖y - x‖} h (x - t)` for every `t`.

The second bound says that `log g` is again `C`-Lipschitz, and `g` is `C¹`. Lebesgue convolution
does not preserve the mass under a probability measure `γ`, so `g` is divided by
`c = ∫ g ∂γ ∈ [e^{-C r}, e^{C r}]`; this leaves the Lipschitz constant of the logarithm
unchanged. The normalised approximants `q` satisfy `e^{-2 C r} h ≤ q ≤ e^{2 C r} h`, which gives
every integrability requirement, and, as `r → 0`, pointwise convergence `q → h` with a
dominating function for `q log q`, so the entropies converge by dominated convergence.

## Main results

* `LatticeProb.LipschitzLogApprox`: the approximation statement;
* `LatticeProb.lipschitzLogApprox`: `LipschitzLogApprox n` for every `n`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Real
open scoped NNReal Topology Convolution

namespace LatticeProb

namespace LogLipschitzMollify

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A positive function with `C`-Lipschitz logarithm changes by at most the factor
`exp (C * dist y x)` between `x` and `y`. -/
lemma le_exp_mul_dist_mul {h : E → ℝ} {C : ℝ≥0} (hpos : ∀ x, 0 < h x)
    (hlip : LipschitzWith C fun x => Real.log (h x)) (x y : E) :
    h y ≤ Real.exp (C * dist y x) * h x := by
  have h1 : Real.log (h y) - Real.log (h x) ≤ C * dist y x := by
    have := hlip.dist_le_mul y x
    rw [Real.dist_eq] at this
    exact (le_abs_self _).trans this
  calc h y = Real.exp (Real.log (h y)) := (Real.exp_log (hpos y)).symm
    _ ≤ Real.exp (C * dist y x + Real.log (h x)) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (C * dist y x) * h x := by rw [Real.exp_add, Real.exp_log (hpos x)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Conversely, a positive function that changes by at most the factor `exp (C * dist y x)`
between any two points has a `C`-Lipschitz logarithm. -/
lemma lipschitzWith_log_of_le_exp_mul_dist {q : E → ℝ} {C : ℝ≥0} (hpos : ∀ x, 0 < q x)
    (hq : ∀ x y, q y ≤ Real.exp (C * dist y x) * q x) :
    LipschitzWith C fun x => Real.log (q x) := by
  have key : ∀ x y, Real.log (q y) - Real.log (q x) ≤ C * dist y x := by
    intro x y
    have := Real.log_le_log (hpos y) (hq x y)
    rw [Real.log_mul (Real.exp_pos _).ne' (hpos x).ne', Real.log_exp] at this
    linarith
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  exact ⟨key y x, by rw [dist_comm]; exact key x y⟩

/-- The mollification `φ ⋆ h` of `h` by the normalised bump `φ`, with respect to an additive Haar
measure. -/
def smooth (φ : ContDiffBump (0 : E)) (h : E → ℝ) : E → ℝ :=
  φ.normed Measure.addHaar ⋆[ContinuousLinearMap.lsmul ℝ ℝ, Measure.addHaar] h

lemma smooth_apply (φ : ContDiffBump (0 : E)) (h : E → ℝ) (x : E) :
    smooth φ h x = ∫ t, φ.normed Measure.addHaar t * h (x - t) ∂Measure.addHaar := by
  simp [smooth, convolution_def]

section Smooth

variable (φ : ContDiffBump (0 : E)) {h : E → ℝ} {C : ℝ≥0}

lemma integrable_normed_mul (hc : Continuous h) (x : E) :
    Integrable (fun t => φ.normed Measure.addHaar t * h (x - t)) Measure.addHaar :=
  Continuous.integrable_of_hasCompactSupport
    (φ.continuous_normed.mul (hc.comp (continuous_const.sub continuous_id)))
    φ.hasCompactSupport_normed.mul_right

lemma contDiff_smooth (hc : Continuous h) : ContDiff ℝ 1 (smooth φ h) := by
  have := φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.contDiff_normed (μ := Measure.addHaar) (n := 1))
    (hc.locallyIntegrable (μ := Measure.addHaar))
  exact_mod_cast this

/-- The mollification satisfies the same ratio bound as `h`. -/
lemma smooth_le_exp_mul_dist_mul (hpos : ∀ x, 0 < h x)
    (hlip : LipschitzWith C fun x => Real.log (h x)) (hc : Continuous h) (x y : E) :
    smooth φ h y ≤ Real.exp (C * dist y x) * smooth φ h x := by
  rw [smooth_apply, smooth_apply, ← integral_const_mul]
  refine integral_mono (integrable_normed_mul φ hc y)
    ((integrable_normed_mul φ hc x).const_mul _) fun t => ?_
  have := le_exp_mul_dist_mul hpos hlip (x - t) (y - t)
  rw [dist_sub_right] at this
  calc φ.normed Measure.addHaar t * h (y - t)
      ≤ φ.normed Measure.addHaar t * (Real.exp (C * dist y x) * h (x - t)) :=
        mul_le_mul_of_nonneg_left this (φ.nonneg_normed t)
    _ = _ := by ring

/-- The mollification lies within the factor `exp (C * φ.rOut)` of `h`. -/
lemma smooth_mem_Icc (hpos : ∀ x, 0 < h x) (hlip : LipschitzWith C fun x => Real.log (h x))
    (hc : Continuous h) (x : E) :
    Real.exp (-(C * φ.rOut)) * h x ≤ smooth φ h x ∧
      smooth φ h x ≤ Real.exp (C * φ.rOut) * h x := by
  have hnorm : ∀ t, φ.normed Measure.addHaar t ≠ 0 → ‖t‖ < φ.rOut := by
    intro t ht
    have : t ∈ Function.support (φ.normed Measure.addHaar) := ht
    rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at this
    exact this
  have hdist : ∀ t, dist (x - t) x = ‖t‖ := fun t => by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
  have hint := integrable_normed_mul φ hc x
  have hconst : ∀ c : ℝ, ∫ t, φ.normed Measure.addHaar t * c ∂Measure.addHaar = c := fun c => by
    rw [integral_mul_const, φ.integral_normed, one_mul]
  constructor
  · rw [smooth_apply, ← hconst (Real.exp (-(C * φ.rOut)) * h x)]
    refine integral_mono (φ.integrable_normed.mul_const _) hint fun t => ?_
    by_cases ht : φ.normed Measure.addHaar t = 0
    · simp [ht]
    refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
    have h1 := le_exp_mul_dist_mul hpos hlip (x - t) x
    rw [dist_comm, hdist] at h1
    have h2 : Real.exp (-(C * φ.rOut)) ≤ Real.exp (-(C * ‖t‖)) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (hnorm t ht).le C.2))
    calc Real.exp (-(C * φ.rOut)) * h x ≤ Real.exp (-(C * ‖t‖)) * h x :=
          mul_le_mul_of_nonneg_right h2 (hpos x).le
      _ ≤ Real.exp (-(C * ‖t‖)) * (Real.exp (C * ‖t‖) * h (x - t)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = h (x - t) := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  · rw [smooth_apply, ← hconst (Real.exp (C * φ.rOut) * h x)]
    refine integral_mono hint (φ.integrable_normed.mul_const _) fun t => ?_
    by_cases ht : φ.normed Measure.addHaar t = 0
    · simp [ht]
    refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
    have h1 := le_exp_mul_dist_mul hpos hlip x (x - t)
    rw [hdist] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hnorm t ht).le C.2)) (hpos x).le)

end Smooth

/-- On a positive number `q` within the factor `exp (2 * a)` of `h > 0`, the entropy integrand
`q * log q` is dominated by `exp (2 * A) * (|h * log h| + 2 * A * h)` for every `A ≥ a`. -/
lemma abs_mul_log_le {q h a A : ℝ} (hh : 0 < h) (haA : a ≤ A)
    (hlo : Real.exp (-(2 * a)) * h ≤ q) (hhi : q ≤ Real.exp (2 * a) * h) :
    |q * Real.log q| ≤ Real.exp (2 * A) * (|h * Real.log h| + 2 * A * h) := by
  have hq : 0 < q := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hh) hlo
  have hl1 : Real.log q ≤ 2 * a + Real.log h := by
    have := Real.log_le_log hq hhi
    rwa [Real.log_mul (Real.exp_pos _).ne' hh.ne', Real.log_exp] at this
  have hl2 : -(2 * a) + Real.log h ≤ Real.log q := by
    have := Real.log_le_log (mul_pos (Real.exp_pos _) hh) hlo
    rwa [Real.log_mul (Real.exp_pos _).ne' hh.ne', Real.log_exp] at this
  have habs : |Real.log q| ≤ |Real.log h| + 2 * A := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log h), le_abs_self (Real.log h)]
  have hqA : q ≤ Real.exp (2 * A) * h :=
    hhi.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hh.le)
  rw [abs_mul, abs_of_pos hq, abs_mul, abs_of_pos hh]
  calc q * |Real.log q| ≤ (Real.exp (2 * A) * h) * (|Real.log h| + 2 * A) :=
        mul_le_mul hqA habs (abs_nonneg _) (mul_pos (Real.exp_pos _) hh).le
    _ = _ := by ring

section Approx

variable (γ : Measure E) (φ : ContDiffBump (0 : E)) (h : E → ℝ)

/-- The mollification of `h` normalised to mass one under `γ`. -/
def approx : E → ℝ := fun x => (∫ y, smooth φ h y ∂γ)⁻¹ * smooth φ h x

variable {γ φ h} {C : ℝ≥0}

/-- One normalised mollification is a positive `C¹` density of mass one with `C`-Lipschitz
logarithm, and lies within the factor `exp (2 * C * φ.rOut)` of `h`. -/
theorem approx_spec (hpos : ∀ x, 0 < h x) (hlip : LipschitzWith C fun x => Real.log (h x))
    (hint : Integrable h γ) (hmass : ∫ x, h x ∂γ = 1) :
    (∀ x, 0 < approx γ φ h x) ∧ ContDiff ℝ 1 (approx γ φ h) ∧
      LipschitzWith C (fun x => Real.log (approx γ φ h x)) ∧ Integrable (approx γ φ h) γ ∧
      (∫ x, approx γ φ h x ∂γ = 1) ∧
      ∀ x, Real.exp (-(2 * (C * φ.rOut))) * h x ≤ approx γ φ h x ∧
        approx γ φ h x ≤ Real.exp (2 * (C * φ.rOut)) * h x := by
  have hc : Continuous h :=
    (Real.continuous_exp.comp hlip.continuous).congr fun x => Real.exp_log (hpos x)
  set a : ℝ := C * φ.rOut with ha
  have hb := smooth_mem_Icc φ hpos hlip hc
  have hgc : Continuous (smooth φ h) := (contDiff_smooth φ hc).continuous
  have hgpos : ∀ x, 0 < smooth φ h x := fun x =>
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) (hpos x)) (hb x).1
  have hgint : Integrable (smooth φ h) γ :=
    (hint.const_mul (Real.exp a)).mono' hgc.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (hgpos x)]; exact (hb x).2)
  set c := ∫ y, smooth φ h y ∂γ with hcdef
  have hclo : Real.exp (-a) ≤ c := by
    have := integral_mono (hint.const_mul (Real.exp (-a))) hgint fun x => (hb x).1
    rwa [integral_const_mul, hmass, mul_one] at this
  have hchi : c ≤ Real.exp a := by
    have := integral_mono hgint (hint.const_mul (Real.exp a)) fun x => (hb x).2
    rwa [integral_const_mul, hmass, mul_one] at this
  have hcpos : 0 < c := (Real.exp_pos _).trans_le hclo
  have happ : ∀ x, approx γ φ h x = c⁻¹ * smooth φ h x := fun x => rfl
  have hqpos : ∀ x, 0 < approx γ φ h x := fun x => by
    rw [happ]; exact mul_pos (inv_pos.2 hcpos) (hgpos x)
  refine ⟨hqpos, contDiff_const.mul (contDiff_smooth φ hc), ?_, hgint.const_mul _, ?_,
    fun x => ⟨?_, ?_⟩⟩
  · refine lipschitzWith_log_of_le_exp_mul_dist hqpos fun x y => ?_
    rw [happ, happ, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (smooth_le_exp_mul_dist_mul φ hpos hlip hc x y)
      (inv_pos.2 hcpos).le
  · simp only [happ]
    rw [integral_const_mul, ← hcdef, inv_mul_cancel₀ hcpos.ne']
  · have h1 : Real.exp (-a) ≤ c⁻¹ := by
      rw [Real.exp_neg]; exact inv_anti₀ hcpos hchi
    rw [happ, show -(2 * a) = -a + -a by ring, Real.exp_add, mul_assoc]
    exact mul_le_mul h1 (hb x).1 (mul_pos (Real.exp_pos _) (hpos x)).le (inv_pos.2 hcpos).le
  · have h2 : c⁻¹ ≤ Real.exp a := by
      have := inv_anti₀ (Real.exp_pos _) hclo
      rwa [Real.exp_neg, inv_inv] at this
    rw [happ, show 2 * a = a + a by ring, Real.exp_add, mul_assoc]
    exact mul_le_mul h2 (hb x).2 (hgpos x).le (Real.exp_pos _).le

end Approx

/-- The mollifiers of radius `1 / (k + 1)`. -/
def bump (k : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / ((k : ℝ) + 2)
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

end LogLipschitzMollify

open LogLipschitzMollify

/-- **Approximation of densities with Lipschitz logarithm.**  A positive density on
`Fin n → ℝ` whose logarithm is `C`-Lipschitz is the entropy limit of a sequence of `C¹` positive
densities with the same `C`-Lipschitz logarithm, total mass `1`, and integrable `h`-weighted
squared gradient of the logarithm. -/
def LipschitzLogApprox (n : ℕ) : Prop :=
  ∀ (h : (Fin n → ℝ) → ℝ) (C : NNReal),
    (∀ x, 0 < h x) →
    LipschitzWith C (fun x => Real.log (h x)) →
    Integrable h (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    Integrable (fun x => h x * Real.log (h x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    (∫ x, h x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1) →
      ∃ hε : ℕ → (Fin n → ℝ) → ℝ,
        (∀ k, (∀ x, 0 < hε k x) ∧ ContDiff ℝ 1 (hε k) ∧
          LipschitzWith C (fun x => Real.log (hε k x)) ∧
          Integrable (hε k) (Measure.pi fun _ : Fin n => gaussianReal 0 1) ∧
          Integrable (fun x => hε k x * Real.log (hε k x))
            (Measure.pi fun _ : Fin n => gaussianReal 0 1) ∧
          Integrable (fun x => ‖fderiv ℝ (fun y => Real.log (hε k y)) x‖ ^ 2 * hε k x)
            (Measure.pi fun _ : Fin n => gaussianReal 0 1) ∧
          (∫ x, hε k x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1)) ∧
        Tendsto (fun k => ∫ x, hε k x * Real.log (hε k x)
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) atTop
          (𝓝 (∫ x, h x * Real.log (h x)
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))

/-- **Approximation of densities with Lipschitz logarithm**, in every dimension: a positive
density with `C`-Lipschitz logarithm and finite entropy under the standard Gaussian measure is the
entropy limit of `C¹` positive densities of mass one with `C`-Lipschitz logarithms. -/
theorem lipschitzLogApprox (n : ℕ) : LipschitzLogApprox n := by
  intro h C hpos hlip hint hintlog hmass
  set γ := Measure.pi fun _ : Fin n => gaussianReal 0 1
  have spec := fun k => approx_spec (φ := bump (E := Fin n → ℝ) k) hpos hlip hint hmass
  have hr : ∀ k, (bump (E := Fin n → ℝ) k).rOut = 1 / ((k : ℝ) + 1) := fun k => rfl
  set a : ℕ → ℝ := fun k => C * (bump (E := Fin n → ℝ) k).rOut with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => by simp only [ha, hr]; positivity
  have haC : ∀ k, a k ≤ C := fun k => by
    simp only [ha, hr]
    exact mul_le_of_le_one_right C.2 ((div_le_one (by positivity)).2 (by simp))
  have hbound : ∀ k x, |approx γ (bump k) h x * Real.log (approx γ (bump k) h x)| ≤
      Real.exp (2 * C) * (|h x * Real.log (h x)| + 2 * C * h x) := fun k x =>
    abs_mul_log_le (hpos x) (haC k) ((spec k).2.2.2.2.2 x).1 ((spec k).2.2.2.2.2 x).2
  have hdom : Integrable (fun x => Real.exp (2 * C) * (|h x * Real.log (h x)| + 2 * C * h x)) γ :=
    (hintlog.abs.add (hint.const_mul (2 * C))).const_mul _
  refine ⟨fun k => approx γ (bump k) h, fun k => ?_, ?_⟩
  · obtain ⟨hp, hcd, hl, hi, hm, -⟩ := spec k
    refine ⟨hp, hcd, hl, hi, ?_, ?_, hm⟩
    · exact hdom.mono' (Real.continuous_mul_log.comp hcd.continuous).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hbound k x)
    · refine (hi.const_mul ((C : ℝ) ^ 2)).mono'
        ((((hcd.log fun x => (hp x).ne').continuous_fderiv one_ne_zero).norm.pow 2).mul
          hcd.continuous).aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hp x).le)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hl) 2) (hp x).le
  · have hlim : Tendsto a atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (C : ℝ)
      simpa only [ha, hr, mul_zero] using this
    refine tendsto_integral_of_dominated_convergence _
      (fun k => (Real.continuous_mul_log.comp (spec k).2.1.continuous).aestronglyMeasurable) hdom
      (fun k => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hbound k x)
      (ae_of_all _ fun x => ?_)
    have hlo : Tendsto (fun k => Real.exp (-(2 * a k)) * h x) atTop (𝓝 (h x)) := by
      have := ((Real.continuous_exp.tendsto _).comp ((hlim.const_mul 2).neg)).mul_const (h x)
      simpa only [Function.comp_def, mul_zero, neg_zero, Real.exp_zero, one_mul] using this
    have hhi : Tendsto (fun k => Real.exp (2 * a k) * h x) atTop (𝓝 (h x)) := by
      have := ((Real.continuous_exp.tendsto _).comp (hlim.const_mul 2)).mul_const (h x)
      simpa only [Function.comp_def, mul_zero, Real.exp_zero, one_mul] using this
    have hq := tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
      (fun k => ((spec k).2.2.2.2.2 x).1) (fun k => ((spec k).2.2.2.2.2 x).2)
    exact (Real.continuous_mul_log.tendsto (h x)).comp hq

end LatticeProb
