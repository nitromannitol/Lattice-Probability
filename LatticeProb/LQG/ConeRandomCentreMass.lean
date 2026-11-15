import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma28

/-! # Small-ball mass at a random centre for a quantum cone -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort MatedCRTHarmonic.CellScaling
open scoped NNReal ENNReal

namespace LatticeProb.LQG

/-- A constructive quantum-cone area measure has the uniform small-ball
lower-tail bound at an arbitrary, possibly dependent random centre. -/
theorem measure_cone_randomCentre_ball_mass_le
    {γ : ℝ} (M : MatedCRTHarmonic.GMSLemma27.CellModel γ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {X : M.Ω → DistC} {B B' : ℝ≥0 → M.Ω → ℝ}
    (hX : IsWholePlaneGFF X M.P)
    (hB : IsBrownianReal B M.P) (hB' : IsBrownianReal B' M.P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) M.P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) M.P)
    (harea : ∀ᵐ ω ∂M.P,
      M.area ω = lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)))
    (z : M.Ω → ℂ) {p ρ e : ℝ} (hp : 0 < p) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
      M.P {ω | z ω ∈ ball (0 : ℂ) ρ ∧
        M.area ω (ball (z ω) δ) ≤ ENNReal.ofReal (δ ^ (2 + γ ^ 2 / 2 + p))} ≤
        ENNReal.ofReal (C * δ ^ e) := by
  have hdom := MatedCRTHarmonic.GMCFacts.areaDominates_of_cone M hγ hγ2 hX hB hB' hind harea
  obtain ⟨C, hC⟩ := MatedCRTHarmonic.GMSLemma27.lemma28_strict M
    (MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds hγ hγ2) hdom hγ hp hρ0 hρ1 he
  refine ⟨C, fun δ hδ => (measure_mono ?_).trans (hC δ hδ)⟩
  intro ω hω
  exact ⟨z ω, hω.1, hω.2⟩

end LatticeProb.LQG
