import LatticeProb.LQG.NormalizedSpliceArea
import LatticeProb.LQG.LocalAreaFullTrace

/-! # Independent traces for cone area via a radial splice -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic MatedCRTHarmonic.GMCFacts
open MatedCRTHarmonic.MoTPort MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open LatticeProb.Gauss LatticeProb.LQG.LQGMeasureNonatomicMass
open QuantumZipper

namespace LatticeProb.LQG

/-- The cone area does not charge the unit-disk portion of a null trace
independent of the replacement field and its radial path, when the specified
circle coordinates belong to that replacement field. -/
theorem ae_coneArea_range_eq_zero_of_indep_splice
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (hXB : IndepFun X (fun ω => (pathOf B ω, pathOf B' ω)) P)
    {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hWm : Measurable W)
    (hWp : IsPreBrownianReal (fun t ω => W ω t) P) (hXW : IndepFun X W P)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (hcircle : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᵐ z ∂volume,
      hcirc ω (dyadicScale k) z = circleAvg
        (replField X (fun ω => twoSided (W ω)
          ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω)
        (dyadicScale k) z)
    {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g)
    (hind : IndepFun (fun ω => (replField X
      (fun ω => twoSided (W ω)
        ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω,
      W ω)) g P)
    (hnull : ∀ᵐ ω ∂P, volume (range (g ω)) = 0) :
    ∀ᵐ ω ∂P, lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω)
      (fun t => B' t ω)) (range (g ω) ∩ ball (0 : ℂ) 1) = 0 := by
  let : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  have hY := (IsWholePlaneGFF.normalized_replField_twoSided hX hRm hR hWm hWp hXW).1
  have hi := (hind.comp measurable_fst measurable_id).symm
  have hl := ae_normalized_splice_area_and_cone_restrict hγ hγ2 hX hB hB' hBB' hXB
    hRm hR hWm hWp hXW hW
  have hloc := hl.mono fun ω hω => hω.2 (ballO (0 : ℂ) 1) (Subset.rfl)
  exact ae_localArea_range_eq_zero_of_indep_field hY hh hcircle hγ hγ2
    (lt_lqgQ hγ hγ2) hgm hi hnull hloc

end LatticeProb.LQG
