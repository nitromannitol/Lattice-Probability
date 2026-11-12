import Mathlib

/-!
# Paley-Zygmund bound for a half of the mean, and the resulting bound on the Laplace transform

Let `Z ≥ 0` be a random variable on a probability space with mean `m > 0` and a moment `E Z^p ≤ C` for some
`p > 1`. Hölder's inequality applied to `E[Z 1_{Z > m/2}] ≥ m/2` gives
`P(Z > m/2) ≥ (m/2)^{p/(p-1)} C^{-1/(p-1)}`, and consequently `E exp(-λ Z) ≤ 1 - η/2` for every
`λ ≥ 2 log 2 / m` whenever `P(Z > m/2) ≥ η`.

* `LatticeProb.measure_gt_half_ge`: the Paley-Zygmund bound at the level `m/2`.
* `LatticeProb.integral_exp_neg_le_of_measure_gt_half`: the Laplace transform is at most `1 - η/2` for `λ ≥ 2 log 2 / m`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Paley-Zygmund at half the mean.** If `Z` is measurable with `∫ Z⁺ = m > 0` and `∫ Z^p ≤ C` for some
`p > 1`, then `P(Z > m/2) ≥ (m/2)^{p/(p-1)} C^{-1/(p-1)}`. -/
theorem measure_gt_half_ge [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    {m C p : ℝ} (hm : 0 < m) (hp : 1 < p) (hC : 0 < C)
    (hmean : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P = ENNReal.ofReal m)
    (hmom : ∫⁻ ω, ENNReal.ofReal (Z ω) ^ p ∂P ≤ ENNReal.ofReal C) :
    ENNReal.ofReal ((m / 2) ^ (p / (p - 1)) * C ^ (-(1 / (p - 1)))) ≤ P {ω | m / 2 < Z ω} := by
  set A : Set Ω := {ω | m / 2 < Z ω} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hZ
  set q : ℝ := p / (p - 1) with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq0 : 0 < q := hpq.symm.pos
  have hfm : Measurable fun ω => ENNReal.ofReal (Z ω) := ENNReal.measurable_ofReal.comp hZ
  -- pointwise split
  have hsplit : ∀ ω, ENNReal.ofReal (Z ω) ≤
      ENNReal.ofReal (m / 2) + ENNReal.ofReal (Z ω) * A.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp [hω]
    · have : Z ω ≤ m / 2 := not_lt.1 hω
      simp [hω, ENNReal.ofReal_le_ofReal this]
  have h1 : ENNReal.ofReal m ≤ ENNReal.ofReal (m / 2) +
      ∫⁻ ω, ENNReal.ofReal (Z ω) * A.indicator 1 ω ∂P := by
    calc ENNReal.ofReal m = ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P := hmean.symm
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (m / 2) + ENNReal.ofReal (Z ω) * A.indicator 1 ω) ∂P :=
          lintegral_mono hsplit
      _ = ENNReal.ofReal (m / 2) + ∫⁻ ω, ENNReal.ofReal (Z ω) * A.indicator 1 ω ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hfm.aemeasurable
    ((measurable_one.indicator hAm).aemeasurable)
  have hgq : ∫⁻ ω, (A.indicator (1 : Ω → ℝ≥0∞) ω) ^ q ∂P = P A := by
    have : ∀ ω, (A.indicator (1 : Ω → ℝ≥0∞) ω) ^ q = A.indicator 1 ω := by
      intro ω
      by_cases hω : ω ∈ A <;> simp [hω, ENNReal.zero_rpow_of_pos hq0]
    simp_rw [this]
    simp [lintegral_indicator_one hAm]
  have h2 : ENNReal.ofReal (m / 2) ≤ ENNReal.ofReal C ^ (1 / p) * P A ^ (1 / q) := by
    have hh : ENNReal.ofReal (m / 2) + ENNReal.ofReal (m / 2) ≤
        ENNReal.ofReal (m / 2) + ENNReal.ofReal C ^ (1 / p) * P A ^ (1 / q) := by
      calc ENNReal.ofReal (m / 2) + ENNReal.ofReal (m / 2) = ENNReal.ofReal m := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
        _ ≤ ENNReal.ofReal (m / 2) + ∫⁻ ω, ENNReal.ofReal (Z ω) * A.indicator 1 ω ∂P := h1
        _ ≤ _ := by
            gcongr
            refine hHolder.trans ?_
            rw [hgq]
            gcongr
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 hh
  have ha0 : ENNReal.ofReal C ^ (1 / (p - 1)) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hC) ENNReal.ofReal_ne_top).ne'
  have hatop : ENNReal.ofReal C ^ (1 / (p - 1)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have h3 : ENNReal.ofReal (m / 2) ^ q ≤ ENNReal.ofReal C ^ (1 / (p - 1)) * P A := by
    calc ENNReal.ofReal (m / 2) ^ q ≤ (ENNReal.ofReal C ^ (1 / p) * P A ^ (1 / q)) ^ q :=
          ENNReal.rpow_le_rpow h2 hq0.le
      _ = (ENNReal.ofReal C ^ (1 / p)) ^ q * (P A ^ (1 / q)) ^ q :=
          ENNReal.mul_rpow_of_nonneg _ _ hq0.le
      _ = ENNReal.ofReal C ^ (1 / (p - 1)) * P A := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
          congr 2
          rw [hq]; field_simp
  have hinv : ENNReal.ofReal (C ^ (-(1 / (p - 1)))) = (ENNReal.ofReal C ^ (1 / (p - 1)))⁻¹ := by
    have e1 : ENNReal.ofReal (C ^ (-(1 / (p - 1)))) = ENNReal.ofReal C ^ (-(1 / (p - 1))) :=
      (ENNReal.ofReal_rpow_of_pos hC).symm
    rw [e1, ENNReal.rpow_neg]
  have e2 : ENNReal.ofReal ((m / 2) ^ (p / (p - 1))) = ENNReal.ofReal (m / 2) ^ (p / (p - 1)) :=
    (ENNReal.ofReal_rpow_of_pos (by positivity)).symm
  rw [ENNReal.ofReal_mul (by positivity), e2, hinv]
  calc ENNReal.ofReal (m / 2) ^ (p / (p - 1)) * (ENNReal.ofReal C ^ (1 / (p - 1)))⁻¹
      ≤ (ENNReal.ofReal C ^ (1 / (p - 1)) * P A) * (ENNReal.ofReal C ^ (1 / (p - 1)))⁻¹ := by
        gcongr
    _ = P A := by
        rw [mul_comm (ENNReal.ofReal C ^ (1 / (p - 1))) (P A), mul_assoc,
          ENNReal.mul_inv_cancel ha0 hatop, mul_one]

/-- **The Laplace transform at large `λ`.** If `Z ≥ 0` is measurable with `P(Z > m/2) ≥ η`, then
`E exp(-λ Z) ≤ 1 - η/2` for every `λ ≥ 2 log 2 / m`. -/
theorem integral_exp_neg_le_of_measure_gt_half [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    (h0 : ∀ ω, 0 ≤ Z ω) {m η lam : ℝ} (hm : 0 < m)
    (hη : ENNReal.ofReal η ≤ P {ω | m / 2 < Z ω}) (hlam : 2 * Real.log 2 / m ≤ lam) :
    ∫ ω, Real.exp (-(lam * Z ω)) ∂P ≤ 1 - η / 2 := by
  set A : Set Ω := {ω | m / 2 < Z ω} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hZ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlam0 : 0 ≤ lam := le_trans (by positivity) hlam
  have hlm : Real.log 2 ≤ lam * (m / 2) := by
    have := (div_le_iff₀ hm).1 hlam
    linarith
  have hpt : ∀ ω, Real.exp (-(lam * Z ω)) ≤ 1 - (1 / 2) * A.indicator (1 : Ω → ℝ) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · have hz : m / 2 < Z ω := hω
      have : Real.log 2 ≤ lam * Z ω := hlm.trans (by nlinarith)
      have h2 : Real.exp (-(lam * Z ω)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
      have h3 : Real.exp (-Real.log 2) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      simp [hω]; linarith
    · have : 0 ≤ lam * Z ω := mul_nonneg hlam0 (h0 ω)
      have h1 : Real.exp (-(lam * Z ω)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      simpa [hω] using h1
  have hint : Integrable (fun ω => Real.exp (-(lam * Z ω))) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun ω => ?_)
    · exact (Real.measurable_exp.comp (measurable_const.mul hZ).neg).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by linarith [mul_nonneg hlam0 (h0 ω)])
  have hind : Integrable (A.indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hmono := integral_mono hint ((integrable_const (1 : ℝ)).sub (hind.const_mul (1 / 2))) hpt
  have hPA : η ≤ (P A).toReal := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hη
  have hcalc : ∫ ω, (1 - (1 / 2) * A.indicator (1 : Ω → ℝ) ω) ∂P = 1 - (1 / 2) * (P A).toReal := by
    rw [integral_sub (integrable_const _) (hind.const_mul _), integral_const_mul]
    simp [integral_indicator_one hAm, Measure.real]
  have hmono' : ∫ ω, Real.exp (-(lam * Z ω)) ∂P ≤ ∫ ω, (1 - (1 / 2) * A.indicator (1 : Ω → ℝ) ω) ∂P :=
    hmono
  rw [hcalc] at hmono'
  linarith

end LatticeProb
