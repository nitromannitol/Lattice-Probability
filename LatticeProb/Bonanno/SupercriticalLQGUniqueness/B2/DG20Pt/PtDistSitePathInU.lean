/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSitePathInU at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSitePath
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCollar

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem pt_dist_site_crossing_path_in_U {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ)
    (x : ℂ) (U : Set ℂ) (T : ℝ) (hT : 0 < T) (ω : Ω)
    (hgood : ω ∈ ptDistSiteGood P W ξ Q ζ C n k x T)
    (hball : ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ k
    let a : ℝ := Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω) *
      (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n))
    ∃ γ : ℝ → ℂ,
      AdmPath U (sphere x (r / 4)) (sphere x (16 * r)) γ ∧
      lfppLen (ξ : ℝ) (fun z => phiMN W P 0 n z ω) γ < ENNReal.ofReal (2 * a) := by
  obtain ⟨γ, hγ, hlen⟩ :=
    pt_dist_site_crossing_path P W hW ξ Q ζ C n k x T hT ω hgood
  refine ⟨γ, ?_, hlen⟩
  obtain ⟨z, hz, w, hw, hp, hinside⟩ := hγ
  exact ⟨z, hz, w, hw, hp, fun s hs => hball (hinside s hs)⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
