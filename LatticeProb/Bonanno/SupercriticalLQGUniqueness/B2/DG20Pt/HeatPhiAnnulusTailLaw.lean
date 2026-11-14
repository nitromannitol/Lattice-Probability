/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiAnnulusTailLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatRealAnnulusUniformLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleArithmetic
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DFGPS LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_phi_annulus_normalized_lower_tail_law
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise Q W) (ξ : Ioi (0 : ℝ))
    (δ : Ioo (0 : ℝ) 1) (φ : Ω → C(ℂ, ℝ))
    (hφ : ∀ ω z, φ ω z = phiVer W Q δ 1 z ω)
    (z : ℂ) (d : ℝ) (hd : 0 < d)
    (T η : ℝ) (hT : 3 < T)
    (htail : Q {ω | crossLenIn (ξ : ℝ)
      (fun y => phiVer W Q δ 1 y ω)
      (closedBall z d) (sphere z (d / 16))
      (sphere z (3 * d / 4)) <
        ENNReal.ofReal (T⁻¹ * lambdaDelta ξ W Q δ)} ≤
      ENNReal.ofReal η) :
    (Q.map φ) {ψ | ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
      crossLenIn ξ ψ (closedBall z d)
        (sphere z (d / 16)) (sphere z (3 * d / 4)) ≤
          ENNReal.ofReal ((2 * T)⁻¹)} ≤ ENNReal.ofReal η := by
  have hv := isPhiVersion_phiVer hW δ.property.1 δ.property.2.le
  have hφm : Measurable φ := by
    have hm : Measurable (pathC (phiVer W Q δ 1) hv.cont) :=
      measurable_pathC hv.cont hv.meas
    convert hm using 1
    funext ω
    exact ContinuousMap.ext (hφ ω)
  let K : Set ℂ := closedBall z d
  let A : Set ℂ := sphere z (d / 16)
  let B : Set ℂ := sphere z (3 * d / 4)
  have hcostm : Measurable (fun ψ : C(ℂ, ℝ) =>
      ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ * crossLenIn ξ ψ K A B) :=
    measurable_const.mul (measurable_crossLenIn
      (Y := fun y (ψ : C(ℂ, ℝ)) => ψ y)
      (isCompact_closedBall z d) (fun ψ => ψ.continuous)
      (fun y => ContinuousMap.measurable_eval y))
  have hLam : 0 < lambdaDelta ξ W Q δ :=
    S6Thm.lambdaDelta_pos_of_698 hW
      (dg20_non_dyadic_median_compare_of_perc hPerc ξ Q W hW) δ.property
  have hTpos : 0 < T := by linarith
  have hsmall : (2 * T)⁻¹ < T⁻¹ := by
    have h := one_div_lt_one_div_of_lt hTpos (by linarith : T < 2 * T)
    simpa only [one_div] using h
  have hsmallE : ENNReal.ofReal ((2 * T)⁻¹) < ENNReal.ofReal T⁻¹ :=
    (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hTpos)).2 hsmall
  rw [Measure.map_apply hφm (measurableSet_le hcostm measurable_const)]
  change Q {ω | ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
      crossLenIn ξ (φ ω) K A B ≤ ENNReal.ofReal ((2 * T)⁻¹)} ≤
    ENNReal.ofReal η
  have hsub : {ω | ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
      crossLenIn ξ (φ ω) K A B ≤ ENNReal.ofReal ((2 * T)⁻¹)} ⊆
    {ω | crossLenIn (ξ : ℝ) (fun y => phiVer W Q δ 1 y ω)
      K A B < ENNReal.ofReal (T⁻¹ * lambdaDelta ξ W Q δ)} := by
    intro ω hω
    have heq : crossLenIn ξ (φ ω) K A B =
        crossLenIn ξ (fun y => phiVer W Q δ 1 y ω) K A B := by
      congr 1
      funext y
      exact hφ ω y
    change ENNReal.ofReal (lambdaDelta ξ W Q δ)⁻¹ *
      crossLenIn ξ (φ ω) K A B ≤ ENNReal.ofReal ((2 * T)⁻¹) at hω
    rw [heq] at hω
    exact pt_dist_rescale_lower_event
      (lambdaDelta ξ W Q δ) T hLam hTpos _ (hω.trans_lt hsmallE)
  exact (measure_mono hsub).trans htail

end SupercriticalLQGUniqueness.B2.DG20Pt
