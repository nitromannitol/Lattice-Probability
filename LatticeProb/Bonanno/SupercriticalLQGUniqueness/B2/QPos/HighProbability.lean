/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.HighProbability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.FiniteUpperTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.TailRate

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 



theorem upper_annulus_shifted_quantile_window
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∀ κ κ' : ℝ, 0 < κ → 0 < κ' →
        Tendsto (fun n : ℕ =>
          P {ω | Real.exp (ξ * (κ * (n : ℝ))) *
              ((2 : ℝ)⁻¹ ^ 3 *
                (Real.exp (κ' * (n : ℝ)) *
                  LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
                  ellN ξ W P (n - 3) (ENNReal.ofReal p))) <
              (crossLenIn ξ (fun x => phiMN W P 0 n x ω)
                upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal})
          atTop (𝓝 0) := by
  obtain ⟨p₀, hp₀, hp⟩ := fine_east_mrect_tail hW hξ
  refine ⟨p₀, hp₀, fun p hpos hpp κ κ' hκ hκ' => ?_⟩
  let _ := hW.isProbabilityMeasure
  obtain ⟨C, c, hC, hc, htail⟩ := hp p hpos hpp
  have hcoarse := coarseCorridorSup_linear_tail_zero hW hκ
  have hrate := prop18_rate_nat_tendsto_zero hC.le hc hκ'
  have hsum : Tendsto (fun n : ℕ =>
      P {ω | κ * (n : ℝ) < coarseCorridorSup P W ω} +
        ENNReal.ofReal (C * Real.exp (-c * (κ' * (n : ℝ)) ^ 2 /
          Real.log (κ' * (n : ℝ))))) atTop (𝓝 0) := by
    simpa only [zero_add] using hcoarse.add hrate
  have hκtop : Tendsto (fun n : ℕ => κ' * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hκ'
  apply Filter.Tendsto.squeeze' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    hκtop.eventually (eventually_gt_atTop (2 : ℝ))] with n hn hs
  have hfin := htail n hn (κ' * (n : ℝ)) hs
  exact (full_annulus_tail_le_coarse_add_fine hW hξ hn
      (κ * (n : ℝ))
      ((2 : ℝ)⁻¹ ^ 3 *
        (Real.exp (κ' * (n : ℝ)) *
          LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
          ellN ξ W P (n - 3) (ENNReal.ofReal p)))).trans
    (add_le_add_right hfin _)

end SupercriticalLQGUniqueness.B2.QPos
