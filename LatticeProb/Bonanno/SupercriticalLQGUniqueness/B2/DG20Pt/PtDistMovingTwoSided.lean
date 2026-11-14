/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingTwoSided at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingUpperAll
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingLowerSmall

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_moving_two_sided_small_of_inputs
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
        P {ω | ¬ lfppDOn (ξ : ℝ)
          (fun y => phiMN W P 0 n y ω)
          ((fun x : ℂ => (r : ℂ) * x) '' U)
          ((r : ℂ) * z) ((r : ℂ) * w) ≤
            ENNReal.ofReal (M * lambdaN ξ W P n)} ≤
          ENNReal.ofReal ε ∧
        P {ω | lfppDOn (ξ : ℝ)
          (fun y => phiMN W P 0 n y ω)
          ((fun x : ℂ => (r : ℂ) * x) '' U)
          ((r : ℂ) * z) ((r : ℂ) * w) <
            ENNReal.ofReal (M⁻¹ * lambdaN ξ W P n)} ≤
          ENNReal.ofReal ε := by
  obtain ⟨Mup, hMup, hup⟩ :=
    pt_dist_moving_upper_tail_all_of_inputs
      hPerc hExp hPos ξ Q hQ P W hW U hU hUc z w hz hw ε hε
  obtain ⟨T, hT, hlow⟩ :=
    pt_dist_moving_lower_tail_small_of_inputs
      hPerc ξ U z w hzw ε hε
  let M : ℝ := max Mup T
  have hM : 0 < M := hMup.trans_le (le_max_left _ _)
  refine ⟨M, hM, ?_⟩
  intro n r hr1 hr2
  have hlam : 0 ≤ lambdaN ξ W P n := (lambdaN_pos hW n).le
  have hupper : P {ω | ¬ lfppDOn (ξ : ℝ)
      (fun y => phiMN W P 0 n y ω)
      ((fun x : ℂ => (r : ℂ) * x) '' U)
      ((r : ℂ) * z) ((r : ℂ) * w) ≤
        ENNReal.ofReal (M * lambdaN ξ W P n)} ≤
      ENNReal.ofReal ε := by
    apply (measure_mono ?_).trans (hup n r hr1 hr2)
    intro ω hbad hgood
    apply hbad
    exact hgood.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left Mup T) hlam))
  have hInv : M⁻¹ ≤ T⁻¹ :=
    inv_anti₀ (by linarith : 0 < T) (le_max_right Mup T)
  have hlower : P {ω | lfppDOn (ξ : ℝ)
      (fun y => phiMN W P 0 n y ω)
      ((fun x : ℂ => (r : ℂ) * x) '' U)
      ((r : ℂ) * z) ((r : ℂ) * w) <
        ENNReal.ofReal (M⁻¹ * lambdaN ξ W P n)} ≤
      ENNReal.ofReal ε := by
    apply (measure_mono ?_).trans
      (hlow (Ω := Ω) P W hW n r hr1)
    intro ω hsmall
    exact hsmall.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hInv hlam))
  exact ⟨hupper, hlower⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
