/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCompactAnnulusTail at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistShiftAnnulus
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.FieldComparison
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLoopMeet
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAcrossGeometry

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_compact_annulus_lower_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (d : ℝ) (hd : 0 < d) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ T : ℝ, 3 < T →
          P {ω | crossLenIn (ξ : ℝ)
            (fun x => phiMN W P 0 n x ω)
            (closedBall (0 : ℂ) (3 * d / 4))
            (sphere 0 (d / 4)) (sphere 0 (d / 2)) <
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
            ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  let U : Opens ℂ := ⟨ball (0 : ℂ) d, isOpen_ball⟩
  let K₁ : Set ℂ := sphere 0 (d / 4)
  let K₂ : Set ℂ := sphere 0 (d / 2)
  have hnt₁ : K₁.Nontrivial := Strong.nontrivial_sphere 0 (by positivity)
  have hnt₂ : K₂.Nontrivial := Strong.nontrivial_sphere 0 (by positivity)
  have hc₁ : IsConnected K₁ :=
    ⟨hnt₁.nonempty, LQGMetric.TopoCircle.isPreconnected_sphere_complex _ (by positivity)⟩
  have hc₂ : IsConnected K₂ :=
    ⟨hnt₂.nonempty, LQGMetric.TopoCircle.isPreconnected_sphere_complex _ (by positivity)⟩
  have hs₁ : K₁ ⊆ U := by
    intro u hu
    change u ∈ ball (0 : ℂ) d
    have h := mem_sphere.mp hu
    apply mem_ball.mpr
    rw [h]
    linarith
  have hs₂ : K₂ ⊆ U := by
    intro u hu
    change u ∈ ball (0 : ℂ) d
    have h := mem_sphere.mp hu
    apply mem_ball.mpr
    rw [h]
    linarith
  have hdis : Disjoint K₁ K₂ := by
    apply Set.disjoint_left.mpr
    intro u hu₁ hu₂
    have h₁ := mem_sphere.mp hu₁
    have h₂ := mem_sphere.mp hu₂
    linarith
  have hUc : IsConnected (U : Set ℂ) :=
    (convex_ball (0 : ℂ) d).isConnected (nonempty_ball.mpr hd)
  obtain ⟨c₀, c₁, hc₀, hc₁', htail⟩ := hPerc ξ U K₁ K₂
    (isCompact_sphere _ _) (isCompact_sphere _ _) hc₁ hc₂ hnt₁ hnt₂
    hs₁ hs₂ hdis hUc
  have houter : closedBall (0 : ℂ) (3 * d / 4) ⊆ U := by
    intro u hu
    change u ∈ ball (0 : ℂ) d
    apply mem_ball.mpr
    have h := mem_closedBall.mp hu
    linarith
  refine ⟨c₀, c₁, hc₀, hc₁', ?_⟩
  intro Ω _ P _ W hW n T hT
  have hsubset :
      {ω | crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        (closedBall (0 : ℂ) (3 * d / 4)) K₁ K₂ <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ⊆
      {ω | crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        U K₁ K₂ < ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} := by
    intro ω hω
    exact (crossLenIn_mono_domain (ξ : ℝ)
      (fun x => phiMN W P 0 n x ω) houter).trans_lt hω
  exact (measure_mono hsubset).trans ((htail P W hW n T hT).1)

end SupercriticalLQGUniqueness.B2.DG20Pt
