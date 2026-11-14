/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NormalizerBandScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.Inputs

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private theorem two_rpow_complement (a b : ℝ) (hab : a + b = 1) (k : ℕ) :
    (2 : ℝ) ^ (-a * (k : ℝ)) * (2 : ℝ) ^ (-b * (k : ℝ)) =
      (2 : ℝ)⁻¹ ^ k := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have he : -a * (k : ℝ) + -b * (k : ℝ) = -(k : ℝ) := by
    nlinarith [congrArg (· * (k : ℝ)) hab]
  rw [he, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast, inv_pow]

 


theorem normalizer_band_scale_of_exponentRelation
    (hExp : DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n →
          C⁻¹ * (2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) *
              lambdaN (ξ : ℝ) W P n ≤
            (2 : ℝ)⁻¹ ^ k * lambdaN (ξ : ℝ) W P (n - k) ∧
          (2 : ℝ)⁻¹ ^ k * lambdaN (ξ : ℝ) W P (n - k) ≤
            C * (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
              lambdaN (ξ : ℝ) W P n := by
  obtain ⟨C, hC, hrel⟩ := hExp ξ Q hQ ζ hζ
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ W hW n k hkn
  obtain ⟨hlo, hhi⟩ := hrel P W hW n k hkn
  let p : ℝ := (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (k : ℝ))
  let q : ℝ := (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (k : ℝ))
  let u : ℝ := (2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ))
  let v : ℝ := (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ))
  have hpu : u * q = (2 : ℝ)⁻¹ ^ k := by
    exact two_rpow_complement ((ξ : ℝ) * Q + ζ)
      (1 - (ξ : ℝ) * Q - ζ) (by ring) k
  have hpv : v * p = (2 : ℝ)⁻¹ ^ k := by
    exact two_rpow_complement ((ξ : ℝ) * Q - ζ)
      (1 - (ξ : ℝ) * Q + ζ) (by ring) k
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hhi (mul_nonneg (inv_nonneg.mpr hC.le) hu)
    calc
      C⁻¹ * u * lambdaN (ξ : ℝ) W P n ≤
          (C⁻¹ * u) * (C * q * lambdaN (ξ : ℝ) W P (n - k)) := by
        simpa only [mul_assoc] using hmul
      _ = (2 : ℝ)⁻¹ ^ k * lambdaN (ξ : ℝ) W P (n - k) := by
        rw [show (C⁻¹ * u) * (C * q * lambdaN (ξ : ℝ) W P (n - k)) =
          (u * q) * lambdaN (ξ : ℝ) W P (n - k) by field_simp,
          hpu]
  · have hmul := mul_le_mul_of_nonneg_left hlo (mul_nonneg hC.le hv)
    calc
      (2 : ℝ)⁻¹ ^ k * lambdaN (ξ : ℝ) W P (n - k) =
          (C * v) * (C⁻¹ * p * lambdaN (ξ : ℝ) W P (n - k)) := by
        rw [show (C * v) * (C⁻¹ * p * lambdaN (ξ : ℝ) W P (n - k)) =
          (v * p) * lambdaN (ξ : ℝ) W P (n - k) by field_simp,
          hpv]
      _ ≤ C * v * lambdaN (ξ : ℝ) W P n := by
        simpa only [mul_assoc] using hmul

end SupercriticalLQGUniqueness.B2.DG20Pt
