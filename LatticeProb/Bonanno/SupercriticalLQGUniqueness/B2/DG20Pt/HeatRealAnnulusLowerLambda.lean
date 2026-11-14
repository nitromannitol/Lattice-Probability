/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatRealAnnulusLowerLambda at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatRealAnnulusScaledLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatScaledAnnulusNesting
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicScaleCoupling
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_real_annulus_lower_lambda_small
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (z : ℂ) (d : ℝ) (hd : 0 < d)
    (η : ℝ) (hη : 0 < η) :
    ∃ T : ℝ, 3 < T ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 →
        let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
        P {ω | crossLenIn (ξ : ℝ)
          (fun y => phiVer W P δ 1 y ω)
          (closedBall z d) (sphere z (d / 16))
          (sphere z (3 * d / 4)) <
            ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
          ENNReal.ofReal η := by
  obtain ⟨T, hT, hscaled⟩ :=
    dg20_real_scaled_annulus_lower_small hPerc ξ z d hd η hη
  refine ⟨T, hT, ?_⟩
  intro Ω _ P _ W hW n s hs hs1
  dsimp only
  let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
  let r : ℝ := (2 : ℝ) ^ s
  have hr1 : 1 ≤ r := by
    dsimp [r]
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs.le)
  have hr2 : r ≤ 2 := by
    dsimp [r]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1)
  have hr : 0 < r := by linarith
  let W' := dg20ScaledNoise r hr W
  have hW' : IsWhiteNoise P W' := dg20_isWhiteNoise_scaled P W hW r hr
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  let K : Set ℂ := closedBall z ((3 * d / 4) / r)
  let A : Set ℂ := sphere z ((d / 4) / r)
  let B : Set ℂ := sphere z ((d / 2) / r)
  have hlaw := measure_crossLenIn_phiVer_eq
    (ξ := (ξ : ℝ)) (K := K) (A := A) (B := B)
    (P := P) (P₂ := P) (isCompact_closedBall z ((3 * d / 4) / r)) hW hW'
    hδ hδ1
    (measurableSet_Iio : MeasurableSet
      (Iio (ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n))))
  have htail := hscaled P W hW n s hs hs1
  have hsub :
      {ω | crossLenIn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω)
        (closedBall z d) (sphere z (d / 16)) (sphere z (3 * d / 4)) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ⊆
      {ω | crossLenIn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω)
        K A B < ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} := by
    intro ω hω
    exact (dg20_scaled_annulus_nested_cross_le (ξ : ℝ)
      (fun y => phiVer W P δ 1 y ω) z d r hd hr1 hr2).trans_lt hω
  have hbound := (measure_mono hsub).trans_eq hlaw
  simpa only [K, A, B, W', δ, r, mem_Iio, mem_ofPred_eq] using hbound.trans htail

end SupercriticalLQGUniqueness.B2.DG20Pt
