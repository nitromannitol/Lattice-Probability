/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppASchur at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic

/-!
# A Schur-test bound for integral operators (task P2-DG3B, Ding–Gwynne App. A)

`lintegral_sq_integral_le`: if `|G(y, w)| ≤ K(y, w)` with `∫ K(y, w) dy ≤ 1` and
`∫ K(y, w) dw ≤ 1`, then `∫ (∫ f(y) G(y, w) dy)² dw ≤ ∫ f²` (Schur's test; e.g. Folland, *Real
Analysis*, 2nd ed., Theorem 6.18, here via Cauchy–Schwarz pointwise and Tonelli). Used for the
heat-kernel operators in the proof of DG Lemma A.2 (start-point regularity of `p − p_D`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- Pointwise Cauchy–Schwarz: `(∫ f G)² ≤ ∫ f² K` when `|G| ≤ K` and `∫ K ≤ 1`. -/
lemma ofReal_sq_integral_le {f G K : ℂ → ℝ} (hf : Measurable f) (hK : Measurable K)
    (hGK : ∀ y, |G y| ≤ K y) (hK1 : ∫⁻ y, ENNReal.ofReal (K y) ≤ 1) :
    ENNReal.ofReal ((∫ y, f y * G y) ^ 2) ≤ ∫⁻ y, ENNReal.ofReal (f y ^ 2 * K y) := by
  have hK0 : ∀ y, 0 ≤ K y := fun y => (abs_nonneg _).trans (hGK y)
  have h1 : ENNReal.ofReal |∫ y, f y * G y| ≤ ∫⁻ y, ENNReal.ofReal (|f y| * K y) := by
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hGK y) (abs_nonneg _))
  set F : ℂ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.sqrt (K y))
  set H : ℂ → ℝ≥0∞ := fun y => ENNReal.ofReal (|f y| * Real.sqrt (K y))
  have hF : AEMeasurable F := (hK.sqrt.ennreal_ofReal).aemeasurable
  have hH : AEMeasurable H := ((continuous_abs.measurable.comp hf).mul hK.sqrt).ennreal_ofReal.aemeasurable
  have hHo := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hF hH
  have eFH : ∀ y, (F * H) y = ENNReal.ofReal (|f y| * K y) := by
    intro y
    simp only [Pi.mul_apply, F, H]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    rw [mul_left_comm, Real.mul_self_sqrt (hK0 y)]
  have eF : ∀ y, F y ^ (2 : ℝ) = ENNReal.ofReal (K y) := by
    intro y
    simp only [F]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hK0 y)]
  have eH : ∀ y, H y ^ (2 : ℝ) = ENNReal.ofReal (f y ^ 2 * K y) := by
    intro y
    simp only [H]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)),
      mul_pow, sq_abs, Real.sq_sqrt (hK0 y)]
  simp_rw [eFH, eF, eH] at hHo
  set A := ∫⁻ y, ENNReal.ofReal (K y)
  set B := ∫⁻ y, ENNReal.ofReal (f y ^ 2 * K y)
  have h2 := pow_le_pow_left₀ zero_le hHo 2
  have e : (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ 2 = A * B := by
    rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    norm_num
  rw [e] at h2
  calc ENNReal.ofReal ((∫ y, f y * G y) ^ 2)
      = ENNReal.ofReal |∫ y, f y * G y| ^ 2 := by
        rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    _ ≤ (∫⁻ y, ENNReal.ofReal (|f y| * K y)) ^ 2 := pow_le_pow_left₀ zero_le h1 2
    _ ≤ A * B := h2
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hK1 zero_le
    _ = B := one_mul B

/-- **Schur's test** (`L²` bound for an integral operator dominated by a sub-Markov kernel that
is sub-Markov in both variables). -/
theorem lintegral_sq_integral_le {f : ℂ → ℝ} {G K : ℂ → ℂ → ℝ} (hf : Measurable f)
    (hK : Measurable (Function.uncurry K)) (hGK : ∀ y w, |G y w| ≤ K y w)
    (hK1 : ∀ w, ∫⁻ y, ENNReal.ofReal (K y w) ≤ 1) (hK2 : ∀ y, ∫⁻ w, ENNReal.ofReal (K y w) ≤ 1) :
    ∫⁻ w, ENNReal.ofReal ((∫ y, f y * G y w) ^ 2) ≤ ∫⁻ y, ENNReal.ofReal (f y ^ 2) := by
  have hKw : ∀ w, Measurable fun y => K y w := fun w =>
    hK.comp (measurable_id.prodMk measurable_const)
  have hm : Measurable (Function.uncurry fun w y => ENNReal.ofReal (f y ^ 2 * K y w)) :=
    ((hf.comp measurable_snd).pow_const 2 |>.mul (hK.comp measurable_swap)).ennreal_ofReal
  calc ∫⁻ w, ENNReal.ofReal ((∫ y, f y * G y w) ^ 2)
      ≤ ∫⁻ w, ∫⁻ y, ENNReal.ofReal (f y ^ 2 * K y w) :=
        lintegral_mono fun w => ofReal_sq_integral_le hf (hKw w) (fun y => hGK y w) (hK1 w)
    _ = ∫⁻ y, ∫⁻ w, ENNReal.ofReal (f y ^ 2 * K y w) :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (f y ^ 2) * ∫⁻ w, ENNReal.ofReal (K y w) := by
        refine lintegral_congr fun y => ?_
        simp_rw [ENNReal.ofReal_mul (sq_nonneg (f y))]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ y, ENNReal.ofReal (f y ^ 2) :=
        lintegral_mono fun y => mul_le_of_le_one_right' (hK2 y)

end DG
end LQGMetric
