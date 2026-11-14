/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBAprioriWindow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSqrtAbsorb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneB_apriori_unit_quantile_window
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (p ζ : ℝ) (hp0 : 0 < p) (hp : p < 2⁻¹) (hζ : 0 < ζ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ),
        c * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ)) ≤
          ellN (ξ : ℝ) W P m (ENNReal.ofReal p) ∧
        ellBarN (ξ : ℝ) W P m (ENNReal.ofReal p) ≤
          C * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (m : ℝ)) ∧
        LambdaN (ξ : ℝ) W P m (ENNReal.ofReal p) *
            ellN (ξ : ℝ) W P m (ENNReal.ofReal p) ≤
          C * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (m : ℝ)) := by
  let K : ℝ := Real.sqrt (2 * (ξ : ℝ) ^ 2 * Real.log 2) / p
  obtain ⟨c₀, C₀, hc₀, hC₀, hwin⟩ :=
    laneB_whiteNoise_median_window ξ Q hQ (ζ / 2) (by linarith)
  obtain ⟨A, hA, hAbs⟩ :=
    laneB_exp_sqrt_le_dyadic_power K (ζ / 2) (by linarith)
  refine ⟨c₀ / A, A * C₀, div_pos hc₀ hA, mul_pos hA hC₀, ?_⟩
  intro Ω _ P W hW m
  letI := hW.isProbabilityMeasure
  obtain ⟨hql, hqu, hΛ⟩ := laneB_quantile_sandwich hW (ξ : ℝ) p hp0 hp m
  have hql' : Real.exp (-(K * Real.sqrt m)) * lambdaN (ξ : ℝ) W P m ≤
      ellN (ξ : ℝ) W P m (ENNReal.ofReal p) := by
    simpa only [K, neg_mul] using hql
  change ellBarN (ξ : ℝ) W P m (ENNReal.ofReal p) ≤
    Real.exp (K * Real.sqrt m) * lambdaN (ξ : ℝ) W P m at hqu
  change LambdaN (ξ : ℝ) W P m (ENNReal.ofReal p) ≤
    Real.exp (K * Real.sqrt m) at hΛ
  obtain ⟨hlamlo, hlamhi⟩ := hwin P W hW m
  have hAexp := hAbs m
  have hpowlo :
      (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ)) *
        (2 : ℝ) ^ ((ζ / 2) * (m : ℝ)) =
      (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ / 2) * (m : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hpowhi :
      (2 : ℝ) ^ ((ζ / 2) * (m : ℝ)) *
        (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ / 2) * (m : ℝ)) =
      (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (m : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hlowScale :
      (c₀ / A) * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ)) ≤
        Real.exp (-(K * Real.sqrt m)) *
          (c₀ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ / 2) * (m : ℝ))) := by
    have hcomp :
        ((c₀ / A) * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ))) *
          Real.exp (K * Real.sqrt m) ≤
        c₀ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ / 2) * (m : ℝ)) := by
      calc
        _ ≤ ((c₀ / A) * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ))) *
            (A * (2 : ℝ) ^ ((ζ / 2) * (m : ℝ))) := by
              gcongr
        _ = _ := by
          calc
            _ = ((c₀ / A) * A) *
                ((2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ)) *
                  (2 : ℝ) ^ ((ζ / 2) * (m : ℝ))) := by ring
            _ = _ := by rw [div_mul_cancel₀ _ hA.ne', hpowlo]
    calc
      _ = (((c₀ / A) * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ))) *
          Real.exp (K * Real.sqrt m)) * Real.exp (-(K * Real.sqrt m)) := by
            have he : Real.exp (K * Real.sqrt m) *
                Real.exp (-(K * Real.sqrt m)) = 1 := by
              rw [← Real.exp_add]
              simp
            calc
              _ = ((c₀ / A) * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ))) * 1 := by ring
              _ = ((c₀ / A) * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ))) *
                  (Real.exp (K * Real.sqrt m) * Real.exp (-(K * Real.sqrt m))) := by rw [he]
              _ = _ := by ring
      _ ≤ (c₀ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ / 2) * (m : ℝ))) *
          Real.exp (-(K * Real.sqrt m)) :=
            mul_le_mul_of_nonneg_right hcomp (Real.exp_pos _).le
      _ = _ := by ring
  have huppScale :
      Real.exp (K * Real.sqrt m) *
        (C₀ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ / 2) * (m : ℝ))) ≤
      (A * C₀) * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (m : ℝ)) := by
    calc
      _ ≤ (A * (2 : ℝ) ^ ((ζ / 2) * (m : ℝ))) *
          (C₀ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ / 2) * (m : ℝ))) := by
            gcongr
      _ = _ := by
        calc
          _ = (A * C₀) *
              ((2 : ℝ) ^ ((ζ / 2) * (m : ℝ)) *
                (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ / 2) * (m : ℝ))) := by ring
          _ = _ := by rw [hpowhi]
  refine ⟨?_, ?_, ?_⟩
  · exact hlowScale.trans ((mul_le_mul_of_nonneg_left hlamlo (Real.exp_pos _).le).trans hql')
  · exact hqu.trans ((mul_le_mul_of_nonneg_left hlamhi (Real.exp_pos _).le).trans huppScale)
  · have hmed : ellN (ξ : ℝ) W P m (ENNReal.ofReal p) ≤
        lambdaN (ξ : ℝ) W P m :=
      T20B.ellN_le_lambdaN (ENNReal.ofReal_pos.mpr hp0)
        (by
          have : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
            rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
              ENNReal.ofReal_inv_of_pos (by norm_num)]
            norm_num
          rw [← this]
          exact ENNReal.ofReal_le_ofReal (by norm_num at hp ⊢; linarith)) m
    have hΛ0 : 0 ≤ LambdaN (ξ : ℝ) W P m (ENNReal.ofReal p) :=
      (T20B.LambdaN_pos hW (ENNReal.ofReal_pos.mpr hp0)
        (by
          have : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
            rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
              ENNReal.ofReal_inv_of_pos (by norm_num)]
            norm_num
          rw [← this]
          exact ENNReal.ofReal_le_ofReal (by norm_num at hp ⊢; linarith)) m).le
    have hlam0 : 0 ≤ lambdaN (ξ : ℝ) W P m :=
      (show 0 ≤ c₀ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ / 2) * (m : ℝ))
        by positivity).trans hlamlo
    calc
      LambdaN (ξ : ℝ) W P m (ENNReal.ofReal p) *
          ellN (ξ : ℝ) W P m (ENNReal.ofReal p) ≤
        LambdaN (ξ : ℝ) W P m (ENNReal.ofReal p) *
          lambdaN (ξ : ℝ) W P m := mul_le_mul_of_nonneg_left hmed hΛ0
      _ ≤ Real.exp (K * Real.sqrt m) * lambdaN (ξ : ℝ) W P m :=
        mul_le_mul_of_nonneg_right hΛ hlam0
      _ ≤ Real.exp (K * Real.sqrt m) *
          (C₀ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ / 2) * (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hlamhi (Real.exp_pos _).le
      _ ≤ _ := huppScale

end SupercriticalLQGUniqueness.B2.DG20Conc
