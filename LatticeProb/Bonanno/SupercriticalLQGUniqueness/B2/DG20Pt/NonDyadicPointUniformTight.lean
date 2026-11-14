/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointUniformTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointTight
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointWNLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_white_noise_point_tails_uniform_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
        (hW : IsWhiteNoise P W) (δ : Ioo (0 : ℝ) 1),
        let D := fun ω => lfppDOn (ξ : ℝ)
          (fun y => phiVer W P δ 1 y ω) U z w
        P {ω | ENNReal.ofReal M <
          ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * D ω} ≤
          ENNReal.ofReal ε ∧
        P {ω | ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * D ω <
          ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal ε := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP
  have htight := dg20_white_noise_point_two_sided_tight_of_inputs
    hPerc hExp hPos ξ Q hQ P₀ W₀ hW₀ U hU hUc z w hz hw hzw
  obtain ⟨M, hM, htail⟩ := htight.2 ε hε
  refine ⟨M, hM, ?_⟩
  intro Ω _ P _ W hW δ
  dsimp only
  have hLam := lambdaDelta_eq_of_whiteNoise hW hW₀
    (ξ : ℝ) (δ : ℝ) δ.property.1 δ.property.2.le
  let S₁ : Set ℝ≥0∞ :=
    {d | ENNReal.ofReal M < ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * d}
  let S₂ : Set ℝ≥0∞ :=
    {d | ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * d < ENNReal.ofReal M⁻¹}
  have hS₁ : MeasurableSet S₁ := by
    exact (measurable_const.mul measurable_id) measurableSet_Ioi
  have hS₂ : MeasurableSet S₂ := by
    exact (measurable_const.mul measurable_id) measurableSet_Iio
  have hLaw₁ := dg20_measure_lfppDOn_phiVer_eq
    P P₀ W W₀ hW hW₀ (ξ : ℝ) δ 1 δ.property.1 δ.property.2.le
    U hU z w hS₁
  have hLaw₂ := dg20_measure_lfppDOn_phiVer_eq
    P P₀ W W₀ hW hW₀ (ξ : ℝ) δ 1 δ.property.1 δ.property.2.le
    U hU z w hS₂
  have hb := htail δ
  change P {ω | lfppDOn (ξ : ℝ)
      (fun y => phiVer W P δ 1 y ω) U z w ∈ S₁} ≤
      ENNReal.ofReal ε ∧
    P {ω | lfppDOn (ξ : ℝ)
      (fun y => phiVer W P δ 1 y ω) U z w ∈ S₂} ≤
      ENNReal.ofReal ε
  rw [hLaw₁, hLaw₂]
  dsimp only [S₁, S₂]
  rw [hLam]
  exact hb

end SupercriticalLQGUniqueness.B2.DG20Pt
