/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingLowerTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCompactAnnulusTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_moving_lower_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (z w : ℂ) (hzw : z ≠ w) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ r : ℝ, 1 ≤ r →
        ∀ T : ℝ, 3 < T →
          P {ω | lfppDOn (ξ : ℝ)
            (fun x => phiMN W P 0 n x ω) univ
            ((r : ℂ) * z) ((r : ℂ) * w) <
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
            ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  let d : ℝ := dist z w
  have hd : 0 < d := dist_pos.mpr hzw
  obtain ⟨c₀, c₁, hc₀, hc₁, htail⟩ :=
    pt_dist_compact_annulus_lower_tail_of_inputs hPerc ξ d hd
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n r hr T hT
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hdist :
      dist ((r : ℂ) * z) ((r : ℂ) * w) = r * d := by
    dsimp [d]
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hcross (ω : Ω) :
      crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        (closedBall ((r : ℂ) * z) (3 * d / 4))
        (sphere ((r : ℂ) * z) (d / 4))
        (sphere ((r : ℂ) * z) (d / 2)) ≤
      lfppDOn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        univ ((r : ℂ) * z) ((r : ℂ) * w) := by
    apply pt_dist_fixed_annulus_cross_le_point
      (ha := by dsimp [d] at hd ⊢; positivity)
      (hab := by linarith)
      (hbR := by linarith)
      (hbw := by rw [hdist]; nlinarith)
  have hsubset :
      {ω | lfppDOn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        univ ((r : ℂ) * z) ((r : ℂ) * w) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ⊆
      {ω | crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        (closedBall ((r : ℂ) * z) (3 * d / 4))
        (sphere ((r : ℂ) * z) (d / 4))
        (sphere ((r : ℂ) * z) (d / 2)) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} := by
    intro ω hω
    exact (hcross ω).trans_lt hω
  have hlaw := pt_dist_compact_annulus_law_shift
    P W hW (ξ : ℝ) n ((r : ℂ) * z) (3 * d / 4) (d / 4) (d / 2)
    (measurableSet_Iio : MeasurableSet
      (Iio (ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n))))
  have hlaw' :
      P {ω | crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        (closedBall ((r : ℂ) * z) (3 * d / 4))
        (sphere ((r : ℂ) * z) (d / 4))
        (sphere ((r : ℂ) * z) (d / 2)) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} =
      P {ω | crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        (closedBall 0 (3 * d / 4))
        (sphere 0 (d / 4)) (sphere 0 (d / 2)) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} := by
    simpa only [mem_Iio, mem_ofPred_eq] using hlaw
  exact (measure_mono hsubset).trans
    (hlaw'.le.trans (htail P W hW n T hT))

end SupercriticalLQGUniqueness.B2.DG20Pt
