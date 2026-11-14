/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiZeroBoundaryReal at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Inc3
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiPathComparison

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DDDF.P29WN
  LQGMetric.WhiteNoise LQGMetric.HeatSq LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem dg20_zero_boundary_heat_phi_real_sup_tail
    (U : Set ℂ) (hU : IsOpen U) (hcl : IsCompact (closure U))
    (hsub : closure U ⊆ ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ^ 2 < 1 / 2 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (Xh : BddOn ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) → Ω → ℝ)
        (W : WNSpace → Ω → ℝ) (Y : ℂ → Ω → ℝ),
        IsProbabilityMeasure P ∧
        IsZBGFFProcessExt (sqOpens (-1) 3) Xh P ∧
        IsWhiteNoise P W ∧
        IsContVersion (fun z => Xh (heatBdd (sqOpens (-1) 3) (ε ^ 2 / 2) z)) Y P ∧
        ∀ a : ℝ, 0 ≤ a →
          P {ω | ENNReal.ofReal a ≤ ⨆ z ∈ U,
            ENNReal.ofReal |phiVer W P ε 1 z ω - Y z ω|} ≤
            ENNReal.ofReal (C * Real.exp (-c * a ^ 2)) := by
  obtain ⟨C, c, hC, hc, h29⟩ := dddfProp29Sq U hU hcl hsub
  refine ⟨C, c, hC, hc, ?_⟩
  intro ε hε hε2
  obtain ⟨Ω, iΩ, P, Xh, W, Y, hP, hG, hW, hY, htail⟩ :=
    h29 (ε ^ 2) ⟨sq_pos_of_pos hε, hε2⟩
  refine ⟨Ω, iΩ, P, Xh, W, Y, hP, hG, hW, ?_, ?_⟩
  · exact hY
  · intro a ha
    have heq : Real.sqrt (ε ^ 2) = ε := Real.sqrt_sq_eq_abs ε |>.trans (abs_of_pos hε)
    simpa only [heq] using htail a ha

end SupercriticalLQGUniqueness.B2.DG20Pt
