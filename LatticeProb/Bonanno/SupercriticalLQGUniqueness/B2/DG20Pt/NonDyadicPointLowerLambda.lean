/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointLowerLambda at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointLowerScaled
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointWNLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicScaleCoupling

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_point_lower_lambda_small
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (z w : ℂ) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 3 < T ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ U : Set ℂ, IsOpen U →
        ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 →
          let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
          P {ω | lfppDOn (ξ : ℝ)
            (fun y => phiVer W P δ 1 y ω) U z w <
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
            ENNReal.ofReal ε := by
  obtain ⟨T, hT, hscaled⟩ :=
    dg20_non_dyadic_scaled_point_lower_small hPerc ξ z w hzw ε hε
  refine ⟨T, hT, ?_⟩
  intro Ω _ P _ W hW U hU n s hs hs1
  dsimp only
  let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  let r : ℝ := (2 : ℝ) ^ s
  have hr : 0 < r := by dsimp [r]; positivity
  let W' := dg20ScaledNoise r hr W
  have hW' : IsWhiteNoise P W' :=
    dg20_isWhiteNoise_scaled P W hW r hr
  let a : ℝ≥0∞ := ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)
  have hsub :
      {ω | lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω)
        U z w < a} ⊆
      {ω | lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω)
        univ z w < a} := by
    intro ω hω
    exact (pt_dist_univ_le_internal (ξ : ℝ)
      (fun y => phiVer W P δ 1 y ω) U z w).trans_lt hω
  have hlaw := dg20_measure_lfppDOn_phiVer_eq
    P P W W' hW hW' (ξ : ℝ) δ 1 hδ0 hδ1 univ isOpen_univ z w
    (measurableSet_Iio : MeasurableSet (Iio a))
  have hlaw' :
      P {ω | lfppDOn (ξ : ℝ)
        (fun y => phiVer W P δ 1 y ω) univ z w < a} =
      P {ω | lfppDOn (ξ : ℝ)
        (fun y => phiVer W' P δ 1 y ω) univ z w < a} := by
    simpa only [mem_Iio, mem_ofPred_eq] using hlaw
  have htail := hscaled P W hW n s hs hs1
  change P {ω | lfppDOn (ξ : ℝ)
      (fun y => phiVer W P δ 1 y ω) U z w < a} ≤
      ENNReal.ofReal ε
  exact (measure_mono hsub).trans (hlaw'.le.trans htail)

end SupercriticalLQGUniqueness.B2.DG20Pt
