/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneALaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
  {P : Measure Ω} {P₂ : Measure Ω₂}

 

theorem laneA_law_lenObs_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (m : ℕ)
    (R : MarkedRect) :
    P.map (lenObs ξ (phiMN W P 0 m) R) =
      P₂.map (lenObs ξ (phiMN V P₂ 0 m) R) := by
  have hφW := isPhiVersion_phiMN hW (Nat.zero_le m)
  have hφV := isPhiVersion_phiMN hV (Nat.zero_le m)
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_lenObs hφW.cont hφW.meas R) hS,
    Measure.map_apply (measurable_lenObs hφV.cont hφV.meas R) hS]
  have hlaw := map_phi_eq hW hV _ _ hφW.meas hφV.meas hφW.ae_eq hφV.ae_eq
  have h := measure_crossLenIn_eq (ξ := ξ) (K := R.toSet) (A := R.side₁)
    (B := R.side₂) R.isCompact_toSet hφW.cont hφW.meas
    hφV.cont hφV.meas hlaw (ENNReal.measurable_toReal hS)
  exact h

 
theorem laneA_ellN_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (m : ℕ)
    (p : ℝ≥0∞) : ellN ξ W P m p = ellN ξ V P₂ m p := by
  unfold ellN ellQ
  rw [laneA_law_lenObs_eq hW hV ξ m (rectAB 1 1)]

 
theorem laneA_ellBarN_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (m : ℕ)
    (p : ℝ≥0∞) : ellBarN ξ W P m p = ellBarN ξ V P₂ m p := by
  unfold ellBarN ellBarQ
  exact laneA_ellN_eq hW hV ξ m (1 - p)

 
theorem laneA_LambdaN_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (m : ℕ)
    (p : ℝ≥0∞) : LambdaN ξ W P m p = LambdaN ξ V P₂ m p := by
  unfold LambdaN
  congr 1
  funext k
  rw [laneA_ellBarN_eq hW hV ξ k p, laneA_ellN_eq hW hV ξ k p]

end SupercriticalLQGUniqueness.B2.DG20Conc
