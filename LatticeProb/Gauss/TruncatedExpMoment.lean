import Mathlib

/-!
# Truncated exponential moments of a centered real Gaussian

For `X ~ N(0, v)` and real `t`, `a`:

* `E[e^{tX}; X ≥ a] ≤ exp (t² v / 2 - (a - t v)² / (2 v))` when `t v ≤ a`
  (`setIntegral_Ici_exp_mul_gaussianReal_le`);
* `E[e^{tX}; X ≤ a] ≤ exp (t² v / 2 - (t v - a)² / (2 v))` when `a ≤ t v`
  (`setIntegral_Iic_exp_mul_gaussianReal_le`).

Both are Chernoff bounds: under the exponential tilt by `e^{tX}` the variable `X` has mean `t v`, and the
truncation event is a deviation of size `|a - t v|` from that mean. In the scale parametrization `v = L`,
`a = α L` the exponents are `L (t² / 2 - (α - t)² / 2)`; with `L = log (1 / ε)` these are the thick-point
estimates of Gaussian multiplicative chaos (Duplantier and Sheffield, *Liouville quantum gravity and KPZ*,
Invent. Math. 185 (2011), Section 3.2; Berestycki, *An elementary approach to Gaussian multiplicative chaos*,
Electron. Commun. Probab. 22 (2017), Section 3): the mass carried by points where the field at scale `ε` exceeds
`α log (1 / ε)`, `α > γ`, is at most `ε ^ ((α - γ)² / 2)` in expectation, and the second moment of the density
restricted to the complementary event is at most `ε ^ (-γ² + (2 γ - α)² / 2)` for `α ≤ 2 γ`.

The versions `integral_indicator_exp_mul_le_of_hasLaw_Ici` and `integral_indicator_exp_mul_le_of_hasLaw_Iic` are
for a random variable with law `N(0, v)`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace LatticeProb.GaussTail

/-- The moment generating function of `N(0, v)` as an integral. -/
theorem integral_exp_mul_gaussianReal_zero (v : ℝ≥0) (s : ℝ) :
    ∫ x, rexp (s * x) ∂(gaussianReal 0 v) = rexp (v * s ^ 2 / 2) := by
  have h := mgf_gaussianReal (X := fun x : ℝ => x) (μ := 0) (v := v) (p := gaussianReal 0 v) (by simp) s
  simpa [mgf] using h

/-- Chernoff bound for the exponential moment of `N(0, v)` on the upper tail `[a, ∞)`, with a free tilt `θ ≥ 0`. -/
theorem setIntegral_Ici_exp_mul_gaussianReal_le_tilt (v : ℝ≥0) (t a : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ x in Set.Ici a, rexp (t * x) ∂(gaussianReal 0 v) ≤ rexp (-(θ * a) + v * (t + θ) ^ 2 / 2) := by
  calc ∫ x in Set.Ici a, rexp (t * x) ∂(gaussianReal 0 v)
      = ∫ x, (Set.Ici a).indicator (fun x => rexp (t * x)) x ∂(gaussianReal 0 v) :=
        (integral_indicator measurableSet_Ici).symm
    _ ≤ ∫ x, rexp (-(θ * a)) * rexp ((t + θ) * x) ∂(gaussianReal 0 v) := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
        · exact (integrable_exp_mul_gaussianReal (t + θ)).const_mul _
        · refine ae_of_all _ fun x => ?_
          by_cases hx : x ∈ Set.Ici a
          · simp only [Set.indicator_of_mem hx]
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hax : a ≤ x := hx
            nlinarith [mul_nonneg hθ (sub_nonneg.mpr hax)]
          · simp only [Set.indicator_of_notMem hx]
            positivity
    _ = rexp (-(θ * a) + v * (t + θ) ^ 2 / 2) := by
        rw [integral_const_mul, integral_exp_mul_gaussianReal_zero, ← Real.exp_add]

/-- Chernoff bound for the exponential moment of `N(0, v)` on the lower tail `(-∞, a]`, with a free tilt `θ ≥ 0`. -/
theorem setIntegral_Iic_exp_mul_gaussianReal_le_tilt (v : ℝ≥0) (t a : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ x in Set.Iic a, rexp (t * x) ∂(gaussianReal 0 v) ≤ rexp (θ * a + v * (t - θ) ^ 2 / 2) := by
  calc ∫ x in Set.Iic a, rexp (t * x) ∂(gaussianReal 0 v)
      = ∫ x, (Set.Iic a).indicator (fun x => rexp (t * x)) x ∂(gaussianReal 0 v) :=
        (integral_indicator measurableSet_Iic).symm
    _ ≤ ∫ x, rexp (θ * a) * rexp ((t - θ) * x) ∂(gaussianReal 0 v) := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
        · exact (integrable_exp_mul_gaussianReal (t - θ)).const_mul _
        · refine ae_of_all _ fun x => ?_
          by_cases hx : x ∈ Set.Iic a
          · simp only [Set.indicator_of_mem hx]
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hxa : x ≤ a := hx
            nlinarith [mul_nonneg hθ (sub_nonneg.mpr hxa)]
          · simp only [Set.indicator_of_notMem hx]
            positivity
    _ = rexp (θ * a + v * (t - θ) ^ 2 / 2) := by
        rw [integral_const_mul, integral_exp_mul_gaussianReal_zero, ← Real.exp_add]

/-- **Upper-truncated exponential moment.** For `X ~ N(0, v)` and `t v ≤ a`:
`E[e^{tX}; X ≥ a] ≤ exp (t² v / 2 - (a - t v)² / (2 v))`. -/
theorem setIntegral_Ici_exp_mul_gaussianReal_le (v : ℝ≥0) {t a : ℝ} (hta : t * v ≤ a) :
    ∫ x in Set.Ici a, rexp (t * x) ∂(gaussianReal 0 v) ≤
      rexp (t ^ 2 * v / 2 - (a - t * v) ^ 2 / (2 * v)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using setIntegral_Ici_exp_mul_gaussianReal_le_tilt 0 t a (θ := 0) le_rfl
  · have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
    have hθ : 0 ≤ a / v - t := by
      rw [sub_nonneg, le_div_iff₀ hv']
      exact hta
    refine (setIntegral_Ici_exp_mul_gaussianReal_le_tilt v t a hθ).trans (le_of_eq ?_)
    congr 1
    field_simp
    ring

/-- **Lower-truncated exponential moment.** For `X ~ N(0, v)` and `a ≤ t v`:
`E[e^{tX}; X ≤ a] ≤ exp (t² v / 2 - (t v - a)² / (2 v))`. -/
theorem setIntegral_Iic_exp_mul_gaussianReal_le (v : ℝ≥0) {t a : ℝ} (hta : a ≤ t * v) :
    ∫ x in Set.Iic a, rexp (t * x) ∂(gaussianReal 0 v) ≤
      rexp (t ^ 2 * v / 2 - (t * v - a) ^ 2 / (2 * v)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using setIntegral_Iic_exp_mul_gaussianReal_le_tilt 0 t a (θ := 0) le_rfl
  · have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
    have hθ : 0 ≤ t - a / v := by
      rw [sub_nonneg, div_le_iff₀ hv']
      exact hta
    refine (setIntegral_Iic_exp_mul_gaussianReal_le_tilt v t a hθ).trans (le_of_eq ?_)
    congr 1
    field_simp
    ring

/-- Upper-truncated exponential moment in the scale parametrization `v = L`, `a = α L` with `t ≤ α`:
`E[e^{tX}; X ≥ α L] ≤ exp (L (t² / 2 - (α - t)² / 2))`. -/
theorem setIntegral_Ici_exp_mul_gaussianReal_le_scale (L : ℝ≥0) {t α : ℝ} (htα : t ≤ α) :
    ∫ x in Set.Ici (α * L), rexp (t * x) ∂(gaussianReal 0 L) ≤
      rexp (L * (t ^ 2 / 2 - (α - t) ^ 2 / 2)) := by
  refine (setIntegral_Ici_exp_mul_gaussianReal_le L
    (mul_le_mul_of_nonneg_right htα L.coe_nonneg)).trans (le_of_eq ?_)
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  · have hL' : (L : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hL
    congr 1
    field_simp

/-- Lower-truncated exponential moment in the scale parametrization `v = L`, `a = α L` with `α ≤ t`:
`E[e^{tX}; X ≤ α L] ≤ exp (L (t² / 2 - (t - α)² / 2))`. -/
theorem setIntegral_Iic_exp_mul_gaussianReal_le_scale (L : ℝ≥0) {t α : ℝ} (hαt : α ≤ t) :
    ∫ x in Set.Iic (α * L), rexp (t * x) ∂(gaussianReal 0 L) ≤
      rexp (L * (t ^ 2 / 2 - (t - α) ^ 2 / 2)) := by
  refine (setIntegral_Iic_exp_mul_gaussianReal_le L
    (mul_le_mul_of_nonneg_right hαt L.coe_nonneg)).trans (le_of_eq ?_)
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  · have hL' : (L : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hL
    congr 1
    field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- Upper-truncated exponential moment of a random variable with law `N(0, v)`. -/
theorem integral_indicator_exp_mul_le_of_hasLaw_Ici {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    {t a : ℝ} (hta : t * v ≤ a) :
    ∫ ω in X ⁻¹' Set.Ici a, rexp (t * X ω) ∂P ≤ rexp (t ^ 2 * v / 2 - (a - t * v) ^ 2 / (2 * v)) := by
  have hmap : ∫ x in Set.Ici a, rexp (t * x) ∂(P.map X) = ∫ ω in X ⁻¹' Set.Ici a, rexp (t * X ω) ∂P :=
    setIntegral_map measurableSet_Ici (by fun_prop) hX.aemeasurable
  rw [← hmap, hX.map_eq]
  exact setIntegral_Ici_exp_mul_gaussianReal_le v hta

/-- Lower-truncated exponential moment of a random variable with law `N(0, v)`. -/
theorem integral_indicator_exp_mul_le_of_hasLaw_Iic {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    {t a : ℝ} (hta : a ≤ t * v) :
    ∫ ω in X ⁻¹' Set.Iic a, rexp (t * X ω) ∂P ≤ rexp (t ^ 2 * v / 2 - (t * v - a) ^ 2 / (2 * v)) := by
  have hmap : ∫ x in Set.Iic a, rexp (t * x) ∂(P.map X) = ∫ ω in X ⁻¹' Set.Iic a, rexp (t * X ω) ∂P :=
    setIntegral_map measurableSet_Iic (by fun_prop) hX.aemeasurable
  rw [← hmap, hX.map_eq]
  exact setIntegral_Iic_exp_mul_gaussianReal_le v hta

end LatticeProb.GaussTail
