/- # Gaussian facts for the Berry-Esseen assembly

Elementary facts about the centred Gaussian law `gaussianReal 0 v` (`v > 0`) used when the
distribution function of a normalised sum is compared with the Gaussian one by Esseen's
inequality: the density is bounded by `1 / √(2 π v)`, so the distribution function is
Lipschitz with that constant; the law has a finite first absolute moment; its characteristic
function is `exp (-(v t² / 2))`; and a numerical Gaussian moment integral
`∫_{-T}^{T} t² exp (-t² / 3) dt ≤ 5`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace LatticeProb

/-- The centred Gaussian density is bounded by its value at the origin, `1 / √(2 π v)`.
The hypothesis `0 < v` is not used (it is kept for a uniform signature). -/
theorem gaussianPDFReal_zero_le {v : ℝ≥0} (_hv : 0 < v) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal_def]
  have hexp : Real.exp (-(x - 0) ^ 2 / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x - 0)]) (by positivity)
  have hinv : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * v))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp hinv
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _

/-- The Gaussian distribution function is Lipschitz with constant `1/√(2π v)`. -/
theorem gaussianReal_Iic_lipschitz {v : ℝ≥0} (hv : 0 < v) (x y : ℝ) :
    |(gaussianReal 0 v (Set.Iic x)).toReal - (gaussianReal 0 v (Set.Iic y)).toReal|
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * |x - y| := by
  have hv' : v ≠ 0 := hv.ne'
  have hG : ∀ a : ℝ, (gaussianReal 0 v (Set.Iic a)).toReal
      = ∫ t in Set.Iic a, gaussianPDFReal 0 v t := by
    intro a
    rw [gaussianReal_apply_eq_integral 0 hv', ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Iic (fun t _ => gaussianPDFReal_nonneg 0 v t)
  have hint : ∀ a : ℝ, IntegrableOn (gaussianPDFReal 0 v) (Set.Iic a) volume :=
    fun a => (integrable_gaussianPDFReal 0 v).integrableOn
  rw [hG x, hG y, abs_sub_comm, intervalIntegral.integral_Iic_sub_Iic (hint x) (hint y)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := gaussianPDFReal 0 v) (a := x) (b := y) (C := (Real.sqrt (2 * Real.pi * v))⁻¹)
    (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 v t)]
      exact gaussianPDFReal_zero_le hv t)
  rwa [Real.norm_eq_abs, abs_sub_comm y x] at h

/-- The centred Gaussian law has a finite first absolute moment.
The hypothesis `0 < v` is not used (it is kept for a uniform signature). -/
theorem integrable_abs_gaussianReal {v : ℝ≥0} (_hv : 0 < v) :
    Integrable (fun x : ℝ => |x|) (gaussianReal 0 v) := by
  have h : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    IsGaussian.integrable_id (μ := gaussianReal 0 v)
  simpa [Real.norm_eq_abs] using h.norm

/-- The characteristic function of the centred Gaussian law of variance `v`.
The hypothesis `0 < v` is not used (it is kept for a uniform signature). -/
theorem charFun_gaussianReal_zero {v : ℝ≥0} (_hv : 0 < v) (t : ℝ) :
    charFun (gaussianReal 0 v) t = Complex.exp (-((v * t ^ 2 / 2 : ℝ) : ℂ)) := by
  rw [charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- A numerical Gaussian moment: `∫_{-T}^{T} t² exp (-t²/3) dt ≤ 5` for every `T`. -/
theorem integral_sq_mul_exp_neg_third_le (T : ℝ) :
    ∫ t in (-T)..T, t ^ 2 * Real.exp (-(t ^ 2) / 3) ≤ 5 := by
  set g : ℝ → ℝ := fun t => t ^ 2 * Real.exp (-(t ^ 2) / 3) with hg
  have hgnn : ∀ t, 0 ≤ g t := fun t => by positivity
  have hrew : ∀ t : ℝ, g t = t ^ (2 : ℝ) * Real.exp (-(1 / 3) * t ^ (2 : ℝ)) := by
    intro t
    simp only [hg, Real.rpow_two]
    congr 2
    ring
  have hint : Integrable g := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 3) (by norm_num) (s := 2) (by norm_num)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [hrew, Real.rpow_two]
  -- the full-line integral
  have hfull : ∫ t, g t ≤ 5 := by
    have habs : ∫ t, g t = ∫ t, g |t| := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hg, sq_abs]
    rw [habs, integral_comp_abs]
    have hI : ∫ t in Ioi (0 : ℝ), g t = (1 / 3 : ℝ) ^ (-((2 : ℝ) + 1) / 2) * (1 / 2) *
        Real.Gamma (((2 : ℝ) + 1) / 2) := by
      rw [← integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := 1 / 3)
        (by norm_num) (by norm_num) (by norm_num)]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => hrew t)
    rw [hI]
    set x : ℝ := (1 / 3 : ℝ) ^ (-((2 : ℝ) + 1) / 2) with hx
    have hxpos : 0 < x := by positivity
    have hx2 : x ^ 2 = 27 := by
      rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hxle : x ≤ 5.2 := by nlinarith
    have hG : Real.Gamma (((2 : ℝ) + 1) / 2) = Real.sqrt Real.pi / 2 := by
      have h := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
      rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, h, Real.Gamma_one_half_eq]
      ring
    rw [hG]
    have hsq : Real.sqrt Real.pi ≤ 1.78 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      have := Real.pi_lt_d2
      nlinarith
    have hsqnn : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
    nlinarith
  by_cases hT : 0 ≤ T
  · rw [intervalIntegral.integral_of_le (by linarith)]
    calc ∫ t in Ioc (-T) T, g t ≤ ∫ t, g t :=
          setIntegral_le_integral hint (Filter.Eventually.of_forall hgnn)
      _ ≤ 5 := hfull
  · have hT' : T < 0 := not_le.mp hT
    rw [intervalIntegral.integral_symm]
    have : 0 ≤ ∫ t in T..(-T), g t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => hgnn t)
    linarith

end LatticeProb
