import LatticeProb.LQG.CoupledCurveExitAnchors
import LatticeProb.Topology.RealPrefixExitTrace

/-! # Real prefix exits of a coupled curve -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric LQGMetric LQGMetric.Blueprint LQGMetric.LocalEvent
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- The finite forward ball-exit clock of the Lebesgue-parametrized curve is
its real prefix-exit infimum, and its stopped compact prefix is the real trace
up to that infimum, simultaneously for all radii. -/
theorem ae_coupled_real_prefix_exit
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ r : ℝ,
      let w : C(ℝ≥0, ℂ) := ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
      let T := openExitTime (fun t (_ : Unit) => w t) (ball 0 r) ()
      let τ := sInf {t : ℝ | 0 ≤ t ∧ ¬ ηL ω '' Icc 0 t ⊆ ball 0 r}
      T ≠ ∞ ∧ τ = (T.toNNReal : ℝ) ∧
        (compactPathPrefix (stoppedPath T w) T.toNNReal : Set ℂ) = ηL ω '' Icc 0 τ := by
  filter_upwards [D.spaceFilling] with ω hω r
  dsimp only
  have hfin := (openExitTime_ball_ne_top_of_tendsto_cocompact (ηL ω) hω.2.1 0 0 r).1
  simp only [zero_add] at hfin
  refine ⟨hfin, ?_, ?_⟩
  · exact sInf_prefix_exit_eq_openExitTime (ηL ω) (ball 0 r) (ηL ω).continuous isOpen_ball hfin
  · rw [sInf_prefix_exit_eq_openExitTime (ηL ω) (ball 0 r) (ηL ω).continuous isOpen_ball hfin]
    exact coe_compactPathPrefix_stopped_real (ηL ω) _ hfin

end LatticeProb.LQG
