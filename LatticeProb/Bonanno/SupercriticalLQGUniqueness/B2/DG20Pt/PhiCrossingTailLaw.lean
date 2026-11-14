/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PhiCrossingTailLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.RealSquareCrossSmall
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingMeasurable
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_phi_square_crossing_tail_law
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise Q W) (ξ : Ioi (0 : ℝ))
    (δ : Ioo (0 : ℝ) 1) (φ : Ω → C(ℂ, ℝ))
    (hφ : ∀ ω z, φ ω z = phiVer W Q δ 1 z ω)
    (s η : ℝ)
    (htail : Q {ω | Real.exp s * lambdaDelta ξ W Q δ ≤
      lenObs ξ (phiVer W Q δ 1) (rectAB 1 1) ω} ≤ ENNReal.ofReal η ∧
      Q {ω | lenObs ξ (phiVer W Q δ 1) (rectAB 1 1) ω ≤
        Real.exp (-s) * lambdaDelta ξ W Q δ} ≤ ENNReal.ofReal η) :
    (Q.map φ) {ψ | lfppCrossingLength ξ ψ ≤
      ENNReal.ofReal (Real.exp (-s) * lambdaDelta ξ W Q δ)} ≤
      ENNReal.ofReal η ∧
    (Q.map φ) {ψ | ENNReal.ofReal (Real.exp s * lambdaDelta ξ W Q δ) <
      lfppCrossingLength ξ ψ} ≤ ENNReal.ofReal η := by
  have hv := isPhiVersion_phiVer hW δ.property.1 δ.property.2.le
  have hφm : Measurable φ := by
    have hm : Measurable (pathC (phiVer W Q δ 1) hv.cont) :=
      measurable_pathC hv.cont hv.meas
    convert hm using 1
    funext ω
    exact ContinuousMap.ext (hφ ω)
  have hpos : ∀ ω, 0 < lenObs ξ (phiVer W Q δ 1) (rectAB 1 1) ω := by
    intro ω
    exact lenObs_pos hv.cont _ (by simp [rectAB]) (by simp [rectAB])
      (by simp [rectAB, MarkedRect.crossWidth]) ω
  constructor
  · rw [Measure.map_apply hφm
      (measurableSet_le (dg20_measurable_lfppCrossingLength ξ) measurable_const)]
    have hsub : {ω | lfppCrossingLength ξ (φ ω) ≤
      ENNReal.ofReal (Real.exp (-s) * lambdaDelta ξ W Q δ)} ⊆
      {ω | lenObs ξ (phiVer W Q δ 1) (rectAB 1 1) ω ≤
        Real.exp (-s) * lambdaDelta ξ W Q δ} := by
      intro ω hω
      change lfppCrossingLength ξ (φ ω) ≤
        ENNReal.ofReal (Real.exp (-s) * lambdaDelta ξ W Q δ) at hω
      rw [dg20_lfppCrossingLength_eq_ofReal_lenObs ξ φ ω] at hω
      have heq : lenObs ξ (fun z ω => φ ω z) (rectAB 1 1) ω =
          lenObs ξ (phiVer W Q δ 1) (rectAB 1 1) ω := by
        congr 1
        funext z ω'
        exact hφ ω' z
      rw [heq] at hω
      exact ((ENNReal.ofReal_le_ofReal_iff' ).1 hω).resolve_right
        (not_le_of_gt (hpos ω))
    exact (measure_mono hsub).trans htail.2
  · rw [Measure.map_apply hφm
      (measurableSet_lt measurable_const (dg20_measurable_lfppCrossingLength ξ))]
    have hsub : {ω | ENNReal.ofReal (Real.exp s * lambdaDelta ξ W Q δ) <
      lfppCrossingLength ξ (φ ω)} ⊆
      {ω | Real.exp s * lambdaDelta ξ W Q δ ≤
        lenObs ξ (phiVer W Q δ 1) (rectAB 1 1) ω} := by
      intro ω hω
      change ENNReal.ofReal (Real.exp s * lambdaDelta ξ W Q δ) <
        lfppCrossingLength ξ (φ ω) at hω
      rw [dg20_lfppCrossingLength_eq_ofReal_lenObs ξ φ ω] at hω
      have heq : lenObs ξ (fun z ω => φ ω z) (rectAB 1 1) ω =
          lenObs ξ (phiVer W Q δ 1) (rectAB 1 1) ω := by
        congr 1
        funext z ω'
        exact hφ ω' z
      rw [heq] at hω
      have hle : ENNReal.ofReal (Real.exp s * lambdaDelta ξ W Q δ) ≤
          ENNReal.ofReal (lenObs ξ (phiVer W Q δ 1) (rectAB 1 1) ω) := hω.le
      exact (ENNReal.ofReal_le_ofReal_iff (hpos ω).le).1 hle
    exact (measure_mono hsub).trans htail.1

end SupercriticalLQGUniqueness.B2.DG20Pt
