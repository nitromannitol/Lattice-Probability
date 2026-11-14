/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointLowerScaled at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicCrossCompareSmall
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaledAnnulusLowerBridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistShiftAnnulusTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicLowerTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_scaled_point_lower_small
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (z w : ℂ) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 3 < T ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 →
        let r : ℝ := (2 : ℝ) ^ s
        let W' := dg20ScaledNoise r (by positivity : 0 < r) W
        P {ω | lfppDOn (ξ : ℝ)
          (fun y => phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω)
          univ z w <
            ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
          ENNReal.ofReal ε := by
  let d : ℝ := dist z w
  have hd : 0 < d := dist_pos.mpr hzw
  let K : Set ℂ := closedBall z (3 * d / 4)
  have hK : Bornology.IsBounded K := isBounded_closedBall
  let ε₀ : ℝ := ε / 2
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  obtain ⟨a, ha, hcompare⟩ :=
    dg20_non_dyadic_cross_compare_small K hK ξ ε₀ hε₀
  let C : ℝ := Real.exp (|(ξ : ℝ)| * a)
  have hC : 0 < C := Real.exp_pos _
  have hC1 : 1 ≤ C := by
    dsimp [C]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg (abs_nonneg _) ha)
  let c : ℝ := 2 * C
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨c₀, c₁, hc₀, hc₁, hdyad⟩ :=
    pt_dist_shift_annulus_lower_tail_of_inputs hPerc ξ d hd
  obtain ⟨T₀, hT₀, hsmall⟩ :=
    pt_dist_gaussian_log_tail_small c₀ c₁ ε₀ hc₀ hc₁ hε₀
  let T : ℝ := c * T₀
  have hT : 3 < T := by
    dsimp [T, c]
    nlinarith
  refine ⟨T, hT, ?_⟩
  intro Ω _ P _ W hW n s hs hs1
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
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  let W' := dg20ScaledNoise r hr W
  let U : Set ℂ := closedBall z ((3 * d / 4) / r)
  let A : Set ℂ := sphere z ((d / 4) / r)
  let B : Set ℂ := sphere z ((d / 2) / r)
  have hUK : U ⊆ K := by
    intro y hy
    apply mem_closedBall.mpr
    calc
      dist y z ≤ (3 * d / 4) / r := mem_closedBall.mp hy
      _ ≤ 3 * d / 4 := div_le_self (by positivity) hr1
  let F : ℂ → Ω → ℝ := fun y ω =>
    phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω
  let G : ℂ → Ω → ℝ := fun y ω =>
    phiMN W P 0 n ((r : ℂ) * y) ω
  let E : Ω → ℝ≥0∞ := fun ω =>
    crossLenIn (ξ : ℝ) (fun y => phiMN W P 0 n y ω)
      (closedBall ((r : ℂ) * z) (3 * d / 4))
      (sphere ((r : ℂ) * z) (d / 4))
      (sphere ((r : ℂ) * z) (d / 2))
  let D : Ω → ℝ≥0∞ := fun ω =>
    lfppDOn (ξ : ℝ) (fun y => F y ω) univ z w
  have hcomp := hcompare P W hW U A B hUK n s hs hs1
  have htail := hdyad P W hW n ((r : ℂ) * z) T₀ hT₀
  have hsub :
      {ω | D ω < ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ⊆
      {ω | E ω < ENNReal.ofReal (T₀⁻¹ * lambdaN ξ W P n)} ∪
      {ω | ¬
        (crossLenIn (ξ : ℝ) (fun y => F y ω) U A B ≤
            ENNReal.ofReal C *
              crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ∧
         crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ≤
            ENNReal.ofReal C *
              crossLenIn (ξ : ℝ) (fun y => F y ω) U A B)} := by
    intro ω hω
    by_cases hgood :
        crossLenIn (ξ : ℝ) (fun y => F y ω) U A B ≤
            ENNReal.ofReal C *
              crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ∧
        crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ≤
            ENNReal.ofReal C *
              crossLenIn (ξ : ℝ) (fun y => F y ω) U A B
    · left
      have hbridge : E ω ≤ ENNReal.ofReal c * D ω := by
        exact pt_dist_scaled_annulus_cross_le_point
          (ξ : ℝ) (fun y => F y ω)
          (fun y => phiMN W P 0 n y ω) z w hzw
          r C hr1 hr2 hC.le hgood.2
      exact pt_dist_lower_mul_event c T₀ (lambdaN ξ W P n)
        hc (by linarith) (D ω) (E ω) hbridge hω
    · exact Or.inr hgood
  have hbound : P {ω | D ω <
      ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
      ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ := by
    calc
      _ ≤ P {ω | E ω <
          ENNReal.ofReal (T₀⁻¹ * lambdaN ξ W P n)} +
          P {ω | ¬
            (crossLenIn (ξ : ℝ) (fun y => F y ω) U A B ≤
                ENNReal.ofReal C *
                  crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ∧
             crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ≤
                ENNReal.ofReal C *
                  crossLenIn (ξ : ℝ) (fun y => F y ω) U A B)} :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ :=
        add_le_add (htail.trans (ENNReal.ofReal_le_ofReal hsmall)) hcomp
  have hsum : ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hε₀.le hε₀.le]
    congr 1
    dsimp [ε₀]
    ring
  change P {ω | D ω <
      ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤ ENNReal.ofReal ε
  exact hbound.trans_eq hsum

end SupercriticalLQGUniqueness.B2.DG20Pt
