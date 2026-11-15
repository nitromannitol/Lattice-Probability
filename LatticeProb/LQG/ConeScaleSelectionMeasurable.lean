import LatticeProb.LQG.ConeScaleProductUnion
import LatticeProb.Prob.RandomFiniteSelectionMeasurable
import Mathlib.MeasureTheory.Function.Floor

/-! # Measurable representatives of cone scale selections -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- Padded logarithmic scales read from a continuous radial path. -/
noncomputable def radialPaddedScales {Ω : Type} (γ : ℝ)
    (W : Ω → C(ℝ, ℝ)) (b₁ b₂ : ℝ) (ω : Ω) : Finset ℤ :=
  Finset.Icc
    (⌈ConeScaling.lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b₁) (W ω) - 1⌉ : ℤ)
    (⌊ConeScaling.lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b₂) (W ω) + 1⌋ : ℤ)

/-- Radial padded scales are a measurable finite selection. -/
theorem measurable_radialPaddedScales {Ω : Type} [MeasurableSpace Ω]
    (γ b₁ b₂ : ℝ) {W : Ω → C(ℝ, ℝ)} (hW : Measurable W) :
    Measurable (radialPaddedScales γ W b₁ b₂) := by
  apply measurable_finset_Icc_int
  · exact (((ConeScaling.measurable_lastLevel _ _).comp hW).sub_const 1).ceil
  · exact (((ConeScaling.measurable_lastLevel _ _).comp hW).add_const 1).floor

/-- A radial representative gives the cone's padded selection almost surely. -/
theorem ae_conePaddedScales_eq_radialPaddedScales
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {B B' : ℝ≥0 → Ω → ℝ} {W : Ω → C(ℝ, ℝ)}
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t) (b₁ b₂ : ℝ) :
    conePaddedScales γ α B B' b₁ b₂ =ᵐ[P] radialPaddedScales γ W b₁ b₂ := by
  filter_upwards [hW] with ω hω
  simp only [conePaddedScales, radialPaddedScales,
    IGLaw.coneScale_eq_exp_lastLevel_alpha γ α b₁ hω,
    IGLaw.coneScale_eq_exp_lastLevel_alpha γ α b₂ hω, Real.log_exp]

/-- A measurable radial representative removes the selection measurability
assumptions from the product-law cone scale union estimate. -/
theorem prod_measure_exists_mem_conePaddedScales_le_of_radial
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < CellScaling.lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    {W : Ω → C(ℝ, ℝ)} (hWm : Measurable W)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t)
    {b₁ b₂ u : ℝ} (hb₁ : 0 < b₁) (hb : b₁ < b₂) (hu : 0 < u)
    {T : ℝ≥0} (hTpos : 0 < T)
    (hT : (T : ℝ) = (γ⁻¹ * Real.log b₂ - γ⁻¹ * Real.log b₁) /
      (CellScaling.lqgQ γ - α) + u)
    (N : ℕ) (hN : (T : ℝ) + 3 ≤ (N : ℝ))
    (Bad : ℤ → Set β) (p : ℝ≥0∞) (hBm : ∀ i, MeasurableSet (Bad i))
    (hBad : ∀ i, ν (Bad i) ≤ p) :
    (P.prod ν) {z : Ω × β | ∃ i ∈ conePaddedScales γ α B B' b₁ b₂ z.1,
      z.2 ∈ Bad i} ≤
    ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - α) * u) ^ 2 / (2 * T)))) +
      (N : ℝ≥0∞) * p := by
  have heq := ae_conePaddedScales_eq_radialPaddedScales hW b₁ b₂
  have hprod := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae_eq_comp heq
  have hunion := prod_measure_exists_mem_finset_le_of_measurable P ν
    (radialPaddedScales γ W b₁ b₂) Bad p N
    (measurable_radialPaddedScales γ b₁ b₂ hWm) hBm hBad
  have htail := ConeScaling.measure_cone_scale_count_gt_le_exp
    hγ hαQ hB hB' hm hcont hBB' hWm hW hb₁ hb hu hTpos hT N hN
  calc
    _ ≤ (P.prod ν) {z : Ω × β | ∃ i ∈ radialPaddedScales γ W b₁ b₂ z.1,
        z.2 ∈ Bad i} := by
      apply measure_mono_ae
      filter_upwards [hprod] with z hz hzmem
      change conePaddedScales γ α B B' b₁ b₂ z.1 =
        radialPaddedScales γ W b₁ b₂ z.1 at hz
      rw [hz] at hzmem
      exact hzmem
    _ ≤ P {ω | N < (radialPaddedScales γ W b₁ b₂ ω).card} + (N : ℝ≥0∞) * p := hunion
    _ ≤ P {ω | N < (conePaddedScales γ α B B' b₁ b₂ ω).card} + (N : ℝ≥0∞) * p := by
      apply add_le_add _ le_rfl
      apply measure_mono_ae
      filter_upwards [heq] with ω hω hmem
      simpa only [hω] using hmem
    _ ≤ _ := add_le_add (by simpa only [conePaddedScales] using htail) le_rfl

end LatticeProb
