import LatticeProb.LQG.ConeScaleCountTail
import LatticeProb.Prob.RandomScaleProductUnion

/-! # Product-law union bound over cone scales -/

open MeasureTheory ProbabilityTheory MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- The padded logarithmic integer scales between two cone radii. -/
noncomputable def conePaddedScales {Ω : Type} (γ α : ℝ)
    (B B' : ℝ≥0 → Ω → ℝ) (b₁ b₂ : ℝ) (ω : Ω) : Finset ℤ :=
  Finset.Icc
    (⌈Real.log (CellScaling.coneScale γ α (fun s => B s ω) (fun s => B' s ω) b₁) - 1⌉ : ℤ)
    (⌊Real.log (CellScaling.coneScale γ α (fun s => B s ω) (fun s => B' s ω) b₂) + 1⌋ : ℤ)

/-- A centered cone-scale count tail and a uniform bound on bad events on an
    independent factor bound their union over the random scale interval. -/
theorem prod_measure_exists_mem_conePaddedScales_le
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
    (Bad : ℤ → Set β) (p : ℝ≥0∞) (hBad : ∀ i, ν (Bad i) ≤ p)
    (hE : MeasurableSet {z : Ω × β | ∃ i ∈ conePaddedScales γ α B B' b₁ b₂ z.1,
      z.2 ∈ Bad i})
    (hgood : MeasurableSet {ω | (conePaddedScales γ α B B' b₁ b₂ ω).card ≤ N}) :
    (P.prod ν) {z : Ω × β | ∃ i ∈ conePaddedScales γ α B B' b₁ b₂ z.1,
      z.2 ∈ Bad i} ≤
    ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - α) * u) ^ 2 / (2 * T)))) +
      (N : ℝ≥0∞) * p := by
  have htail := MatedCRTHarmonic.ConeScaling.measure_cone_scale_count_gt_le_exp
    hγ hαQ hB hB' hm hcont hBB' hWm hW hb₁ hb hu hTpos hT N hN
  have hunion := prod_measure_exists_mem_finset_le P ν
    (conePaddedScales γ α B B' b₁ b₂) Bad p N hBad hE hgood
  have htail' : P {ω | N < (conePaddedScales γ α B B' b₁ b₂ ω).card} ≤
      ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - α) * u) ^ 2 / (2 * T)))) := by
    simpa only [conePaddedScales] using htail
  exact hunion.trans (add_le_add htail' le_rfl)

end LatticeProb
