import LatticeProb.LQG.ConeCouplingExitSelection
import LatticeProb.LQG.AreaTimePlanarExitTail

/-! # Joint exit failures at cone-dependent scales -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- A uniform joint exit-failure bound controls failures at the random padded scales. -/
theorem measure_exists_mem_conePaddedScales_joint_firstExitBallFailure_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {d : ℕ}
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin d))) (hF : Measurable F)
    (b₁ b₂ ε : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (hp : ∀ k, P (firstExitBallFailure (F ∘ ηL) ε k) ≤ p) :
    P {ω | ∃ k ∈ conePaddedScales γ γ B B' b₁ b₂ ω,
      F (ηL ω) ∈ firstExitBallFailure id ε k} ≤
      P {ω | N < (conePaddedScales γ γ B B' b₁ b₂ ω).card} + (N : ℝ≥0∞) * p := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨W, hWm, _, hWη, hW⟩ :=
    CellScaling.JointScalingO.exists_radialPath_indepFun_curve D hγ0 hγ2
  have hKm := measurable_radialPaddedScales γ b₁ b₂ hWm
  have hsel : IndepFun (radialPaddedScales γ W b₁ b₂) (F ∘ ηL) P := by
    have hproj := hWη.comp measurable_snd hF
    exact hproj.comp (measurable_radialPaddedScales γ b₁ b₂ measurable_id) measurable_id
  have heq := ae_conePaddedScales_eq_radialPaddedScales hW b₁ b₂
  have hbound := measure_exists_mem_finset_le_of_indepFun hKm
    (hF.comp D.measurable_curves.1) hsel (firstExitBallFailure id ε)
    (measurableSet_firstExitBallFailure measurable_id ε) p N hp
  calc
    _ ≤ P {ω | ∃ k ∈ radialPaddedScales γ W b₁ b₂ ω,
        F (ηL ω) ∈ firstExitBallFailure id ε k} := by
      apply measure_mono_ae
      filter_upwards [heq] with ω hω hmem
      simpa only [hω] using hmem
    _ ≤ P {ω | N < (radialPaddedScales γ W b₁ b₂ ω).card} +
        (N : ℝ≥0∞) * p := hbound
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply measure_mono_ae
      filter_upwards [heq] with ω hω hmem
      simpa only [hω] using hmem

/-- Polynomial joint exit-failure bounds hold at the cone's padded scales, up to
    the probability that their number exceeds the chosen threshold. -/
theorem measure_conePaddedScales_planar_exit_failure_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hFm : Measurable F)
    (hF : ∀ v t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    {q ρ r : ℝ} (hq : 0 < q) (hqρ : q < ρ) (hρ : ρ < 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (b₁ b₂ : ℝ) (n N : ℕ) :
    ∃ C : ℝ, ∀ {δ : ℝ}, δ ∈ Set.Ioo (0 : ℝ) 1 → δ ^ (1 - r) ≤ q →
      P {ω | ∃ k ∈ conePaddedScales γ γ B B' b₁ b₂ ω,
        F (ηL ω) ∈ firstExitBallFailure id δ k} ≤
        P {ω | N < (conePaddedScales γ γ B B' b₁ b₂ ω).card} +
          (N : ℝ≥0∞) * ENNReal.ofReal (C * δ ^ n) := by
  obtain ⟨C, hC⟩ := LQG.measure_areaTime_planar_exit_failure_uniform_le D F hF hq hqρ hρ hr n
  refine ⟨C, ?_⟩
  intro δ hδ hδq
  exact measure_exists_mem_conePaddedScales_joint_firstExitBallFailure_le
    D hγ0 hγ2 F hFm b₁ b₂ δ _ N (hC hδ hδq)

end LatticeProb
