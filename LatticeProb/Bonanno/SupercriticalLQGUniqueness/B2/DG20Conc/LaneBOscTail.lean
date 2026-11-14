/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBOscTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CMom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CDefs

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.SupTail LQGMetric.WhiteNoise

 


theorem laneB_prop3_tail_shift : ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
      IsWhiteNoise P W →
    ∀ (n : ℕ) (Y : ℂ → Ω → ℝ),
      (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
      (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
      ∀ c₁ : ℂ, ∀ x : ℝ, 0 ≤ x →
    P.real {ω | x ≤ ((2 : ℝ) ^ n)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun y => Y (y + c₁) ω) z‖} ≤
      C * 4 ^ n * Real.exp (-x ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ := prop3_tail
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW n Y hY hYc c₁ x hx
  let W' : WNSpace → Ω → ℝ := fun g => W (motionL2 1 c₁ g)
  have hW' : IsWhiteNoise P W' := isWhiteNoise_isometry hW _
  have hY' : ∀ y, (fun ω => Y (y + c₁) ω) =ᵐ[P]
      phi W' ((2 : ℝ) ^ n)⁻¹ 1 y := by
    intro y
    have e := phi_motion W (a := ((2 : ℝ) ^ n)⁻¹) (by positivity) 1 1 y c₁
    simp only [Circle.coe_one, one_mul] at e
    rw [← e]
    exact hY (y + c₁)
  have hYc' : ∀ ω, ContDiff ℝ 1 fun y => Y (y + c₁) ω := fun ω =>
    (hYc ω).comp (contDiff_id.add contDiff_const)
  exact htail hW' n (fun y ω => Y (y + c₁) ω) hY' hYc' x hx

end SupercriticalLQGUniqueness.B2.DG20Conc
