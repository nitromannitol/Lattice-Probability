/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingNormalizedTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingTwoSided
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleArithmetic

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_moving_normalized_tails_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧
      ∀ n : ℕ, ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
        let D := fun ω => lfppDOn (ξ : ℝ)
          (fun y => phiMN W P 0 n y ω)
          ((fun x : ℂ => (r : ℂ) * x) '' U)
          ((r : ℂ) * z) ((r : ℂ) * w)
        P {ω | ENNReal.ofReal M <
          ENNReal.ofReal (lambdaN ξ W P n)⁻¹ * D ω} ≤
          ENNReal.ofReal ε ∧
        P {ω | ENNReal.ofReal (lambdaN ξ W P n)⁻¹ * D ω <
          ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal ε := by
  obtain ⟨M, hM, htail⟩ :=
    pt_dist_moving_two_sided_small_of_inputs hPerc hExp hPos
      ξ Q hQ P W hW U hU hUc z w hz hw hzw ε hε
  refine ⟨M, hM, ?_⟩
  intro n r hr1 hr2
  dsimp only
  let lam : ℝ := lambdaN ξ W P n
  have hlam : 0 < lam := lambdaN_pos hW n
  have hupper :
      {ω | ENNReal.ofReal M < ENNReal.ofReal lam⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω)
          ((fun x : ℂ => (r : ℂ) * x) '' U)
          ((r : ℂ) * z) ((r : ℂ) * w)} ⊆
      {ω | ¬ lfppDOn (ξ : ℝ)
        (fun y => phiMN W P 0 n y ω)
        ((fun x : ℂ => (r : ℂ) * x) '' U)
        ((r : ℂ) * z) ((r : ℂ) * w) ≤
          ENNReal.ofReal (M * lam)} := by
    intro ω hω hgood
    exact (not_le_of_gt hω)
      (pt_dist_rescale_upper_bound lam M hlam hM.le _ hgood)
  have hlower :
      {ω | ENNReal.ofReal lam⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω)
          ((fun x : ℂ => (r : ℂ) * x) '' U)
          ((r : ℂ) * z) ((r : ℂ) * w) <
          ENNReal.ofReal M⁻¹} ⊆
      {ω | lfppDOn (ξ : ℝ)
        (fun y => phiMN W P 0 n y ω)
        ((fun x : ℂ => (r : ℂ) * x) '' U)
        ((r : ℂ) * z) ((r : ℂ) * w) <
          ENNReal.ofReal (M⁻¹ * lam)} := by
    intro ω hω
    exact pt_dist_rescale_lower_event lam M hlam hM _ hω
  exact ⟨(measure_mono hupper).trans (htail n r hr1 hr2).1,
    (measure_mono hlower).trans (htail n r hr1 hr2).2⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
