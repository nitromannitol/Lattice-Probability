/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointLambdaTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointScaledTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointWNLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicScaleCoupling

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_point_lambda_tails
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
      let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
      let D := fun ω => lfppDOn (ξ : ℝ)
        (fun y => phiVer W P δ 1 y ω) U z w
      P {ω | ENNReal.ofReal M <
        ENNReal.ofReal (lambdaN ξ W P n)⁻¹ * D ω} ≤
        ENNReal.ofReal ε ∧
      P {ω | ENNReal.ofReal (lambdaN ξ W P n)⁻¹ * D ω <
        ENNReal.ofReal M⁻¹} ≤
        ENNReal.ofReal ε := by
  obtain ⟨M, hM, hscaled⟩ :=
    dg20_non_dyadic_scaled_point_lambda_tails
      hPerc hExp hPos ξ Q hQ P W hW U hU hUc hUb
      z w hz hw hzw ε hε
  refine ⟨M, hM, ?_⟩
  intro n s hs hs1
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
  let lam : ℝ := lambdaN ξ W P n
  have hSup : MeasurableSet
      {d : ℝ≥0∞ | ENNReal.ofReal M < ENNReal.ofReal lam⁻¹ * d} :=
    (measurable_const.mul measurable_id) measurableSet_Ioi
  have hInf : MeasurableSet
      {d : ℝ≥0∞ | ENNReal.ofReal lam⁻¹ * d < ENNReal.ofReal M⁻¹} :=
    (measurable_const.mul measurable_id) measurableSet_Iio
  have hLawSup := dg20_measure_lfppDOn_phiVer_eq
    P P W W' hW hW' (ξ : ℝ) δ 1 hδ0 hδ1 U hU z w hSup
  have hLawInf := dg20_measure_lfppDOn_phiVer_eq
    P P W W' hW hW' (ξ : ℝ) δ 1 hδ0 hδ1 U hU z w hInf
  have hLawSup' :
      P {ω | ENNReal.ofReal M < ENNReal.ofReal lam⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω) U z w} =
      P {ω | ENNReal.ofReal M < ENNReal.ofReal lam⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiVer W' P δ 1 y ω) U z w} := by
    simpa only [mem_setOf_eq] using hLawSup
  have hLawInf' :
      P {ω | ENNReal.ofReal lam⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω) U z w <
          ENNReal.ofReal M⁻¹} =
      P {ω | ENNReal.ofReal lam⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiVer W' P δ 1 y ω) U z w <
          ENNReal.ofReal M⁻¹} := by
    simpa only [mem_setOf_eq] using hLawInf
  have htail := hscaled n s hs hs1
  change P {ω | ENNReal.ofReal M <
      ENNReal.ofReal lam⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω) U z w} ≤
      ENNReal.ofReal ε ∧
    P {ω | ENNReal.ofReal lam⁻¹ *
        lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω) U z w <
        ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal ε
  constructor
  · rw [hLawSup']
    exact htail.1
  · rw [hLawInf']
    exact htail.2

end SupercriticalLQGUniqueness.B2.DG20Pt
