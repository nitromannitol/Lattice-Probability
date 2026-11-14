/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTripleHolder at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConditionalHolder

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_triple_holder_at
    {Ω : Type*} [MeasurableSpace Ω] (κ : Measure Ω)
    {f g h : Ω → ℝ≥0∞}
    (hf : AEMeasurable f κ) (hg : AEMeasurable g κ)
    (hh : AEMeasurable h κ) {ζ : ℝ} (hζ : 0 < ζ) :
    (∫⁻ x, (f x * g x) * h x ∂κ) ≤
      (∫⁻ x, f x ^ (2 * ((1 + ζ) / ζ)) ∂κ) ^
        (ζ / (2 * (1 + ζ))) *
      (∫⁻ x, g x ^ (2 * ((1 + ζ) / ζ)) ∂κ) ^
        (ζ / (2 * (1 + ζ))) *
      (∫⁻ x, h x ^ (1 + ζ) ∂κ) ^ (1 / (1 + ζ)) := by
  let r : ℝ := (1 + ζ) / ζ
  have hr : 0 ≤ r := div_nonneg (by linarith) hζ.le
  have houter := laneC_conditional_holder_at κ (hf.mul hg) hh hζ
  have hinner := laneC_conditional_holder_at κ
    (f := fun x => f x ^ r) (g := fun x => g x ^ r)
    (hf.pow_const r) (hg.pow_const r) (show (0 : ℝ) < 1 by norm_num)
  have hfg : (∫⁻ x, (f x * g x) ^ r ∂κ) ≤
      (∫⁻ x, f x ^ (2 * r) ∂κ) ^ (1 / 2 : ℝ) *
        (∫⁻ x, g x ^ (2 * r) ∂κ) ^ (1 / 2 : ℝ) := by
    have hinner' : (∫⁻ x, f x ^ r * g x ^ r ∂κ) ≤
        (∫⁻ x, (f x ^ r) ^ (2 : ℝ) ∂κ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, (g x ^ r) ^ (2 : ℝ) ∂κ) ^ (1 / 2 : ℝ) := by
      simpa only [show (1 + (1 : ℝ)) / 1 = 2 by norm_num,
        show (1 : ℝ) + 1 = 2 by norm_num,
        show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num,
        div_one] using hinner
    calc
      _ = ∫⁻ x, f x ^ r * g x ^ r ∂κ := by
        congr 1
        funext x
        exact ENNReal.mul_rpow_of_nonneg _ _ hr
      _ ≤ (∫⁻ x, (f x ^ r) ^ (2 : ℝ) ∂κ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, (g x ^ r) ^ (2 : ℝ) ∂κ) ^ (1 / 2 : ℝ) := hinner'
      _ = _ := by
        have hfEq (x : Ω) : (f x ^ r) ^ (2 : ℝ) = f x ^ (2 * r) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
        have hgEq (x : Ω) : (g x ^ r) ^ (2 : ℝ) = g x ^ (2 * r) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
        simp only [hfEq, hgEq]
  have hbound := ENNReal.rpow_le_rpow hfg (by positivity : 0 ≤ ζ / (1 + ζ))
  calc
    _ ≤ (∫⁻ x, (f x * g x) ^ r ∂κ) ^ (ζ / (1 + ζ)) *
        (∫⁻ x, h x ^ (1 + ζ) ∂κ) ^ (1 / (1 + ζ)) := by
      simpa only [r, Pi.mul_apply] using houter
    _ ≤ ((∫⁻ x, f x ^ (2 * r) ∂κ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 * r) ∂κ) ^ (1 / 2 : ℝ)) ^
          (ζ / (1 + ζ)) *
        (∫⁻ x, h x ^ (1 + ζ) ∂κ) ^ (1 / (1 + ζ)) :=
      mul_le_mul_of_nonneg_right hbound bot_le
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ ζ / (1 + ζ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      simp only [show (1 / 2 : ℝ) * (ζ / (1 + ζ)) = ζ / (2 * (1 + ζ)) by field_simp]
      dsimp only [r]

end SupercriticalLQGUniqueness.B2.DG20Conc
