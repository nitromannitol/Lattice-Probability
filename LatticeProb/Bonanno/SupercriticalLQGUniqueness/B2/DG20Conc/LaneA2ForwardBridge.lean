/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ForwardBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Local698
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2QuantileBridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Median.Bridge

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.DDDF.S6 LQGMetric.WhiteNoise

theorem laneA2_forward_step {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ D : ℝ, 1 ≤ D ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
          (B : ℝ) (hB : 1 ≤ B) (j : ℕ),
          LambdaN ξ W P j (ENNReal.ofReal p) ≤ B →
          lambdaN ξ W P (j + 1) ≤ D * B * lambdaN ξ W P j := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ := LQGDimension.ExistAsm.stdP
  obtain ⟨p₀, hp₀, hloc⟩ := laneA2_local_eq698 hW₀ hξ
  refine ⟨p₀, hp₀, ?_⟩
  intro p hp hp₀
  obtain ⟨K₀, hK₀⟩ := hloc p hp hp₀
  let D := max 1 (Real.exp K₀)
  refine ⟨D, le_max_left _ _, ?_⟩
  intro Ω _ P W hW B hB j hΛ
  have hΛ₀ : LambdaN ξ W₀ P₀ j (ENNReal.ofReal p) ≤ B := by
    rwa [← laneA_LambdaN_eq hW hW₀ ξ j (ENNReal.ofReal p)]
  have hstep := (hK₀ B hB j hΛ₀ 1 zero_le_one le_rfl).2
  have eid : lambdaDelta ξ W₀ P₀ ((2 : ℝ) ^ (-((j : ℝ) + 1))) =
      lambdaN ξ W₀ P₀ (j + 1) := by
    rw [← lamT_nat (ξ := ξ) (W := W₀) (P := P₀) (j + 1)]
    simp only [lamT]
    push_cast
    ring_nf
  rw [eid] at hstep
  have hB0 : 0 ≤ B := by linarith
  have he : Real.exp (K₀ + Real.log B) = Real.exp K₀ * B := by
    rw [Real.exp_add, Real.exp_log (by linarith)]
  rw [he] at hstep
  rw [SupercriticalLQGUniqueness.Exponent.Median.lambdaN_eq_of_whiteNoise hW hW₀ ξ j,
    SupercriticalLQGUniqueness.Exponent.Median.lambdaN_eq_of_whiteNoise hW hW₀ ξ (j + 1)]
  exact hstep.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hB0)
    (lambdaN_pos (ξ := ξ) hW₀ j).le)

 

theorem laneA2_forward_three_octave {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ D : ℝ, 1 ≤ D ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
          (B : ℝ) (hB : 1 ≤ B) (m : ℕ) (hm : 3 ≤ m),
          LambdaN ξ W P m (ENNReal.ofReal p) ≤ B →
          ellN ξ W P m (ENNReal.ofReal p) ≤
            D^3 * B^4 * ellN ξ W P (m - 3) (ENNReal.ofReal p) := by
  obtain ⟨pStep, hpStep, hstep⟩ := laneA2_forward_step hξ
  refine ⟨min pStep (1 / 4), lt_min hpStep (by norm_num), ?_⟩
  intro p hp hp₀
  obtain ⟨D, hD, hDstep⟩ := hstep p hp (hp₀.trans (min_le_left _ _))
  refine ⟨D, hD, ?_⟩
  intro Ω _ P W hW B hB m hm hΛ
  exact laneA2_three_octave_of_local_eq698 P hW ξ hp
    (by have := hp₀.trans (min_le_right _ _); linarith)
    hB hD hm hΛ (fun j hj hjΛ => hDstep P W hW B hB j hjΛ)

end SupercriticalLQGUniqueness.B2.DG20Conc
