/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PhiPointTailLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointSquareNormalizedCoupling
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointUniformTight
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenMeasurable
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF LQGMetric.DFGPS
  LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_phi_normalized_point_tail_law
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise Q W) (ξ : Ioi (0 : ℝ))
    (δ : Ioo (0 : ℝ) 1) (φ : Ω → C(ℂ, ℝ))
    (hφ : ∀ ω z, φ ω z = phiVer W Q δ 1 z ω)
    (U : Set ℂ) (hU : IsOpen U) (z w : ℂ)
    (M η : ℝ)
    (htail : Q {ω | ENNReal.ofReal M <
        ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
          lfppDOn ξ (fun y => phiVer W Q δ 1 y ω) U z w} ≤ ENNReal.ofReal η ∧
      Q {ω | ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
          lfppDOn ξ (fun y => phiVer W Q δ 1 y ω) U z w <
            ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal η) :
    (Q.map φ) {ψ | ENNReal.ofReal M <
      ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
        crossLenIn ξ ψ U {z} {w}} ≤ ENNReal.ofReal η ∧
    (Q.map φ) {ψ | ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
        crossLenIn ξ ψ U {z} {w} < ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal η := by
  have hv := isPhiVersion_phiVer hW δ.property.1 δ.property.2.le
  have hφm : Measurable φ := by
    have hm : Measurable (pathC (phiVer W Q δ 1) hv.cont) :=
      measurable_pathC hv.cont hv.meas
    convert hm using 1
    funext ω
    exact ContinuousMap.ext (hφ ω)
  have hcostm : Measurable (fun ψ : C(ℂ, ℝ) =>
      ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
        crossLenIn ξ ψ U {z} {w}) :=
    measurable_const.mul (pt_dist_measurable_crossLenIn_open ξ
      U {z} {w} hU (fun ψ => ψ.continuous)
      (fun y => (continuous_eval_const y).measurable))
  have heq : ∀ ω, ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
      crossLenIn ξ (φ ω) U {z} {w} =
      ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
        lfppDOn ξ (fun y => phiVer W Q δ 1 y ω) U z w := by
    intro ω
    congr 1
    simp only [crossLenIn_singleton]
    congr 1
    funext y
    exact hφ ω y
  constructor
  · rw [Measure.map_apply hφm (measurableSet_lt measurable_const hcostm)]
    change Q {ω | ENNReal.ofReal M <
      ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
        crossLenIn ξ (φ ω) U {z} {w}} ≤ ENNReal.ofReal η
    simpa only [heq] using htail.1
  · rw [Measure.map_apply hφm (measurableSet_lt hcostm measurable_const)]
    change Q {ω | ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
      crossLenIn ξ (φ ω) U {z} {w} < ENNReal.ofReal M⁻¹} ≤
      ENNReal.ofReal η
    simpa only [heq] using htail.2

end SupercriticalLQGUniqueness.B2.DG20Pt
