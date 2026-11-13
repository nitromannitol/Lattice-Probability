/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGradShift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldOsc
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Rigid

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem pt_dist_grad_shift_tail :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ (k : ℕ) (Y : ℂ → Ω → ℝ),
          (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ k)⁻¹ 1 x) →
          (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
          ∀ c : ℂ, ∀ t : ℝ, 0 ≤ t →
          P.real {ω | t ≤ ((2 : ℝ) ^ k)⁻¹ *
            ⨆ z : ferniqueBox 0 1,
              ‖fderiv ℝ (fun x => Y (x + c) ω) z‖} ≤
            C * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ := prop3_tail
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW k Y hY hYc c t ht
  let W' : WNSpace → Ω → ℝ := fun f => W (motionL2 1 c f)
  have hW' : IsWhiteNoise P W' := isWhiteNoise_isometry hW _
  let Y' : ℂ → Ω → ℝ := fun x ω => Y (x + c) ω
  have hY' : ∀ x, (fun ω => Y' x ω) =ᵐ[P] phi W' ((2 : ℝ) ^ k)⁻¹ 1 x := by
    intro x
    have e := phi_motion W (a := ((2 : ℝ) ^ k)⁻¹) (by positivity) 1 1 x c
    simp only [Circle.coe_one, one_mul] at e
    have hx := hY (x + c)
    rw [e] at hx
    simpa [Y', W'] using hx
  have hYc' : ∀ ω, ContDiff ℝ 1 fun x => Y' x ω := by
    intro ω
    exact (hYc ω).comp (contDiff_id.add contDiff_const)
  simpa only [Y'] using htail hW' k Y' hY' hYc' t ht

end SupercriticalLQGUniqueness.B2.DG20Pt
