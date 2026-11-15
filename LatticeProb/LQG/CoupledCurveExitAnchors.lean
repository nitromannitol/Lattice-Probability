import LatticeProb.LQG.StoppedPrefixAnchors
import LatticeProb.LQG.ConeExitWitnessTail
import LatticeProb.Topology.ProperCurveFiniteExit

/-! # Anchors for stopped Lebesgue-parametrized curves -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric LQGMetric LQGMetric.Blueprint LQGMetric.LocalEvent
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- One deterministic sequence of normalized tests works for all ball-exit
prefixes of the Lebesgue-parametrized curve in the coupling, almost surely. -/
theorem exists_dyadicHull_anchors_coupled_exit
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ ψ : ℕ → TestC, (∀ n, ∫ z, ψ n z = 1) ∧
      ∀ᵐ ω ∂P, ∀ r : ℝ,
        let w : C(ℝ≥0, ℂ) := ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
        let T := openExitTime (fun t (_ : Unit) => w t) (ball 0 r) ()
        T ≠ ∞ ∧ ∀ n,
          tsupport (ψ n : ℂ → ℝ) ⊆ interior (dyadicHull n (w '' Icc 0 T.toNNReal)) ∧
          tsupport (ψ n : ℂ → ℝ) ⊆ interior
            (dyadicHull n (compactPathPrefix (stoppedPath T w) T.toNNReal : Set ℂ)) := by
  obtain ⟨ψ, hint, hψ⟩ := exists_dyadicHull_stoppedPrefix_anchors 0
  refine ⟨ψ, hint, ?_⟩
  filter_upwards [D.spaceFilling] with ω hω r
  dsimp only
  have hfin := (openExitTime_ball_ne_top_of_tendsto_cocompact (ηL ω) hω.2.1 0 0 r).1
  simp only [zero_add] at hfin
  refine ⟨hfin, ?_⟩
  exact hψ _ _ hfin hω.2.2.1

end LatticeProb.LQG
