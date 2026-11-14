/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointScaledTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointNormProb
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingNormalizedTails

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_scaled_point_lambda_tails
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (hUb : Bornology.IsBounded U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 →
      let r : ℝ := (2 : ℝ) ^ s
      let W' := dg20ScaledNoise r (by positivity : 0 < r) W
      let D := fun ω => lfppDOn (ξ : ℝ)
        (fun y => phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω)
        U z w
      P {ω | ENNReal.ofReal M <
        ENNReal.ofReal (lambdaN ξ W P n)⁻¹ * D ω} ≤
        ENNReal.ofReal ε ∧
      P {ω | ENNReal.ofReal (lambdaN ξ W P n)⁻¹ * D ω <
        ENNReal.ofReal M⁻¹} ≤
        ENNReal.ofReal ε := by
  let ε₀ : ℝ := ε / 2
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  obtain ⟨A, hA, hcmp⟩ :=
    dg20_non_dyadic_point_norm_compare_small U hUb ξ ε₀ hε₀
  obtain ⟨M₀, hM₀, hmove⟩ :=
    pt_dist_moving_normalized_tails_of_inputs hPerc hExp hPos
      ξ Q hQ P W hW U hU hUc z w hz hw hzw ε₀ hε₀
  refine ⟨A * M₀, mul_pos hA hM₀, ?_⟩
  intro n s hs hs1
  dsimp only
  let r : ℝ := (2 : ℝ) ^ s
  have hr1 : 1 ≤ r := by
    dsimp [r]
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs.le)
  have hr2 : r ≤ 2 := by
    dsimp [r]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1)
  let W' := dg20ScaledNoise r (by positivity : 0 < r) W
  let lam : ℝ := lambdaN ξ W P n
  let X : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal lam⁻¹ *
      lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω)
        ((fun x : ℂ => (r : ℂ) * x) '' U)
        ((r : ℂ) * z) ((r : ℂ) * w)
  let Y : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal lam⁻¹ *
      lfppDOn (ξ : ℝ)
        (fun y => phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω)
        U z w
  have htail := hmove n r hr1 hr2
  have hcompare := hcmp P W hW z w n s hs hs1
  have htransfer :=
    two_sided_tail_of_probabilistic_compare
      P X Y A M₀ ε₀ hA hM₀ htail.1 htail.2 hcompare
  have hsum : ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hε₀.le hε₀.le]
    congr 1
    dsimp [ε₀]
    ring
  change P {ω | ENNReal.ofReal (A * M₀) < Y ω} ≤
      ENNReal.ofReal ε ∧
    P {ω | Y ω < ENNReal.ofReal (A * M₀)⁻¹} ≤
      ENNReal.ofReal ε
  simpa only [hsum] using htransfer

end SupercriticalLQGUniqueness.B2.DG20Pt
