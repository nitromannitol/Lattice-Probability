import Mathlib
import LatticeProb.Analysis.GammaLaplaceIntegral

/-!
# Negative moments from a polynomial bound on the Laplace transform

Let `Z ≥ 0` be a random variable on a probability space with `E exp(-t Z) ≤ A t^{-a}` for every `t > 0`.
Then `Z > 0` almost surely, and `E Z^{-q} ≤ Γ(q)^{-1} (1/q + A/(a-q))` for every `0 < q < a`, from
`z^{-q} Γ(q) = ∫_0^∞ t^{q-1} e^{-z t} dt` and Tonelli's theorem.

* `LatticeProb.measure_eq_zero_of_laplace_le`: `P(Z = 0) = 0`.
* `LatticeProb.lintegral_rpow_neg_le_of_laplace_le`: the bound on `E Z^{-q}` (in `[0, ∞]`, so also `Z > 0` a.s.).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The Laplace transform `E exp(-t Z)` of a nonnegative random variable, in `[0, ∞]`, is at most `1` and,
under `E exp(-t Z) ≤ B` (real integral), at most `ofReal B`. -/
theorem lintegral_exp_neg_le [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    (h0 : ∀ ω, 0 ≤ Z ω) {t B : ℝ} (ht : 0 < t) (hB : ∫ ω, Real.exp (-(t * Z ω)) ∂P ≤ B) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(t * Z ω))) ∂P ≤ ENNReal.ofReal (min 1 B) := by
  have hle1 : ∀ ω, Real.exp (-(t * Z ω)) ≤ 1 :=
    fun ω => Real.exp_le_one_iff.2 (by linarith [mul_nonneg ht.le (h0 ω)])
  have hint : Integrable (fun ω => Real.exp (-(t * Z ω))) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun ω => ?_)
    · exact (Real.measurable_exp.comp (measurable_const.mul hZ).neg).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hle1 ω
  have hL : ∫⁻ ω, ENNReal.ofReal (Real.exp (-(t * Z ω))) ∂P =
      ENNReal.ofReal (∫ ω, Real.exp (-(t * Z ω)) ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => (Real.exp_pos _).le)).symm
  rw [hL]
  refine ENNReal.ofReal_le_ofReal (le_min ?_ hB)
  calc ∫ ω, Real.exp (-(t * Z ω)) ∂P ≤ ∫ ω, (1 : ℝ) ∂P := integral_mono hint (integrable_const _) hle1
    _ = 1 := by simp

/-- Under a polynomial bound on the Laplace transform, `P(Z = 0) = 0`. -/
theorem measure_eq_zero_of_laplace_le [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    (h0 : ∀ ω, 0 ≤ Z ω) {a A : ℝ} (ha : 0 < a)
    (hL : ∀ t : ℝ, 0 < t → ∫ ω, Real.exp (-(t * Z ω)) ∂P ≤ A * t ^ (-a)) :
    P {ω | Z ω = 0} = 0 := by
  have hbound : ∀ t : ℝ, 0 < t → P {ω | Z ω = 0} ≤ ENNReal.ofReal (A * t ^ (-a)) := by
    intro t ht
    calc P {ω | Z ω = 0} = ∫⁻ ω, {ω | Z ω = 0}.indicator 1 ω ∂P := by
          rw [lintegral_indicator_one (measurableSet_eq_fun hZ measurable_const)]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-(t * Z ω))) ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : Z ω = 0
          · simp [hω]
          · simp [hω]
      _ ≤ ENNReal.ofReal (min 1 (A * t ^ (-a))) := lintegral_exp_neg_le hZ h0 ht (hL t ht)
      _ ≤ ENNReal.ofReal (A * t ^ (-a)) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (A * t ^ (-a))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => A * t ^ (-a)) atTop (𝓝 (A * 0)) :=
      (tendsto_rpow_neg_atTop ha).const_mul A
    rw [mul_zero] at h1
    simpa using ENNReal.tendsto_ofReal h1
  exact le_antisymm (ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun t ht => hbound t (by linarith)⟩))
    bot_le

/-- **Negative moments from the Laplace transform.** If `Z ≥ 0` is measurable and `E exp(-t Z) ≤ A t^{-a}`
for every `t > 0`, then for `0 < q < a`, `E Z^{-q} ≤ Γ(q)^{-1} (1/q + A/(a-q))` in `[0, ∞]`. -/
theorem lintegral_rpow_neg_le_of_laplace_le [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    (h0 : ∀ ω, 0 ≤ Z ω) {q a A : ℝ} (hq : 0 < q) (hqa : q < a) (hA : 0 ≤ A)
    (hL : ∀ t : ℝ, 0 < t → ∫ ω, Real.exp (-(t * Z ω)) ∂P ≤ A * t ^ (-a)) :
    ∫⁻ ω, ENNReal.ofReal (Z ω) ^ (-q) ∂P ≤
      ENNReal.ofReal ((Real.Gamma q)⁻¹ * (1 / q + A / (a - q))) := by
  have hΓ : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq
  have hpos : ∀ᵐ ω ∂P, 0 < Z ω := by
    have := measure_eq_zero_of_laplace_le hZ h0 (by linarith) hL
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) this
    exact le_antisymm (not_lt.1 hω) (h0 ω)
  set F : Ω → ℝ → ℝ≥0∞ := fun ω t => ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(Z ω * t))) with hF
  have hFm : Measurable (Function.uncurry F) := by
    have : Measurable fun p : Ω × ℝ => p.2 ^ (q - 1) * Real.exp (-(Z p.1 * p.2)) :=
      (measurable_snd.pow_const _).mul
        (Real.measurable_exp.comp ((hZ.comp measurable_fst).mul measurable_snd).neg)
    exact ENNReal.measurable_ofReal.comp this
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (Z ω) ^ (-q) * ENNReal.ofReal (Real.Gamma q) =
      ∫⁻ t in Ioi (0 : ℝ), F ω t := by
    filter_upwards [hpos] with ω hω
    exact ofReal_rpow_neg_mul_gamma hω hq
  have hmeas : Measurable fun ω => ENNReal.ofReal (Z ω) ^ (-q) :=
    (ENNReal.measurable_ofReal.comp hZ).pow_const _
  have hstep : (∫⁻ ω, ENNReal.ofReal (Z ω) ^ (-q) ∂P) * ENNReal.ofReal (Real.Gamma q) ≤
      ENNReal.ofReal (1 / q + A / (a - q)) := by
    calc (∫⁻ ω, ENNReal.ofReal (Z ω) ^ (-q) ∂P) * ENNReal.ofReal (Real.Gamma q)
        = ∫⁻ ω, ENNReal.ofReal (Z ω) ^ (-q) * ENNReal.ofReal (Real.Gamma q) ∂P :=
          (lintegral_mul_const _ hmeas).symm
      _ = ∫⁻ ω, (∫⁻ t in Ioi (0 : ℝ), F ω t) ∂P := lintegral_congr_ae hae
      _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, F ω t ∂P :=
          lintegral_lintegral_swap hFm.aemeasurable
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (min 1 (A * t ^ (-a))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := ht
          have : ∫⁻ ω, F ω t ∂P = ENNReal.ofReal (t ^ (q - 1)) *
              ∫⁻ ω, ENNReal.ofReal (Real.exp (-(t * Z ω))) ∂P := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun ω => ?_
            simp only [hF]
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), mul_comm (Z ω) t]
          rw [this]
          exact mul_le_mul' le_rfl (lintegral_exp_neg_le hZ h0 ht0 (hL t ht0))
      _ ≤ ENNReal.ofReal (1 / q + A / (a - q)) := lintegral_Ioi_rpow_mul_min_le hq hqa hA
  have hfin : ENNReal.ofReal (Real.Gamma q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hne : ENNReal.ofReal (Real.Gamma q) ≠ 0 := (ENNReal.ofReal_pos.2 hΓ).ne'
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hΓ.le), ENNReal.ofReal_inv_of_pos hΓ]
  rw [mul_comm, ← div_eq_mul_inv]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl hfin)).2 hstep

end LatticeProb
