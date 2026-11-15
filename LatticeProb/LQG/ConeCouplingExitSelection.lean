import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOMain
import LatticeProb.LQG.ConeScaleSelectionMeasurable
import LatticeProb.Prob.IndependentFiniteSelection
import LatticeProb.Topology.FirstExitBallDirectional

/-! # Exit failures at cone-dependent scales -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- For a cone coupling, directional exit-failure bounds for a measurable transform of the
Lebesgue-time curve control failures at the cone's random padded scales. -/
theorem measure_exists_mem_conePaddedScales_firstExitBallFailure_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {d : ℕ}
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin d))) (hF : Measurable F)
    (b₁ b₂ ε : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (hp : ∀ k, P (forwardExitBallFailure (F ∘ ηL) ε k) ≤ p)
    (hq : ∀ k, P (backwardExitBallFailure (F ∘ ηL) ε k) ≤ q) :
    P {ω | ∃ k ∈ conePaddedScales γ γ B B' b₁ b₂ ω,
      F (ηL ω) ∈ firstExitBallFailure id ε k} ≤
      P {ω | N < (conePaddedScales γ γ B B' b₁ b₂ ω).card} +
        (N : ℝ≥0∞) * (p + q) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨W, hWm, _, hWη, hW⟩ :=
    CellScaling.JointScalingO.exists_radialPath_indepFun_curve D hγ0 hγ2
  have hKm := measurable_radialPaddedScales γ b₁ b₂ hWm
  have hsel : IndepFun (radialPaddedScales γ W b₁ b₂) (F ∘ ηL) P := by
    have hproj := hWη.comp measurable_snd hF
    exact hproj.comp (measurable_radialPaddedScales γ b₁ b₂ measurable_id) measurable_id
  have heq := ae_conePaddedScales_eq_radialPaddedScales hW b₁ b₂
  have hbad : ∀ k, P {ω | (F ∘ ηL) ω ∈ firstExitBallFailure id ε k} ≤ p + q := by
    intro k
    exact measure_firstExitBallFailure_le_of_directional P (F ∘ ηL) ε k p q (hp k) (hq k)
  have hbound := measure_exists_mem_finset_le_of_indepFun hKm
    (hF.comp D.measurable_curves.1) hsel (firstExitBallFailure id ε)
    (measurableSet_firstExitBallFailure measurable_id ε) (p + q) N hbad
  calc
    _ ≤ P {ω | ∃ k ∈ radialPaddedScales γ W b₁ b₂ ω,
        F (ηL ω) ∈ firstExitBallFailure id ε k} := by
      apply measure_mono_ae
      filter_upwards [heq] with ω hω hmem
      simpa only [hω] using hmem
    _ ≤ P {ω | N < (radialPaddedScales γ W b₁ b₂ ω).card} +
        (N : ℝ≥0∞) * (p + q) := hbound
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply measure_mono_ae
      filter_upwards [heq] with ω hω hmem
      simpa only [hω] using hmem

end LatticeProb
