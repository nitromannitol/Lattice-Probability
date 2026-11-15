import LatticeProb.Prob.BrownianDriftHitCentered
import LatticeProb.Prob.LogScaleCardinality

/-! # Hitting-time laws and logarithmic scale counts -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- A variable with the same law as a drifted Brownian hitting time inherits
its two centered tail bounds. -/
theorem measure_hitLaw_outside_centered_le {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {μ a u : ℝ} {Tlo Thi : ℝ≥0} (hμ : 0 < μ) (hu : 0 < u)
    (hmpos : 0 < Tlo) (hmval : (Tlo : ℝ) = a / μ - u)
    (hppos : 0 < Thi) (hpval : (Thi : ℝ) = a / μ + u)
    (X : Ω' → ℝ≥0∞)
    (hlaw : ∀ s : Set ℝ≥0∞, MeasurableSet s → P' {ω | X ω ∈ s} =
      P {ω | hitDrift B μ a ω ∈ s}) :
    P' {ω | X ω < (Tlo : ℝ≥0∞) ∨ (Thi : ℝ≥0∞) < X ω} ≤
      ENNReal.ofReal (Real.exp (-((μ * u) ^ 2 / (2 * Tlo)))) +
      ENNReal.ofReal (Real.exp (-((μ * u) ^ 2 / (2 * Thi)))) := by
  calc
    P' {ω | X ω < (Tlo : ℝ≥0∞) ∨ (Thi : ℝ≥0∞) < X ω} ≤
        P' {ω | X ω ≤ (Tlo : ℝ≥0∞)} + P' {ω | (Thi : ℝ≥0∞) < X ω} := by
      calc
        _ ≤ P' ({ω | X ω ≤ (Tlo : ℝ≥0∞)} ∪ {ω | (Thi : ℝ≥0∞) < X ω}) := by
          apply measure_mono
          intro ω hω
          rcases hω with h | h
          · exact Or.inl h.le
          · exact Or.inr h
        _ ≤ _ := measure_union_le _ _
    _ = P {ω | hitDrift B μ a ω ≤ (Tlo : ℝ≥0∞)} +
        P {ω | (Thi : ℝ≥0∞) < hitDrift B μ a ω} := by
      have hlo := hlaw (Set.Iic (Tlo : ℝ≥0∞)) measurableSet_Iic
      have hhi := hlaw (Set.Ioi (Thi : ℝ≥0∞)) measurableSet_Ioi
      simp only [Set.mem_Iic] at hlo
      simp only [Set.mem_Ioi] at hhi
      rw [hlo, hhi]
    _ ≤ _ := add_le_add
      (measure_hitDrift_le_centered_le_exp hB.toIsPreBrownianReal hm hcont hμ hu hmpos hmval)
      (measure_hitDrift_gt_centered_le_exp hB hcont hμ hu hppos hpval)

/-- The strict lower tail is empty at nonpositive real thresholds. -/
theorem measure_hitLaw_lt_ofReal_of_nonpos {Ω' : Type*} [MeasurableSpace Ω']
    (P' : Measure Ω') (X : Ω' → ℝ≥0∞) {t : ℝ} (ht : t ≤ 0) :
    P' {ω | X ω < ENNReal.ofReal t} = 0 := by
  rw [ENNReal.ofReal_of_nonpos ht]
  simp

/-- A centered drift-hit upper tail transfers to the number of padded
logarithmic scales when the radius-ratio event has that hitting law. -/
theorem measure_log_scale_card_gt_le_hit_exp {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    {μ a u : ℝ} {T : ℝ≥0} (hμ : 0 < μ) (hu : 0 < u)
    (hTpos : 0 < T) (hT : (T : ℝ) = a / μ + u)
    (r s : Ω' → ℝ) (N : ℕ)
    (hr : ∀ᵐ ω ∂P', 0 < r ω) (hrs : ∀ᵐ ω ∂P', r ω ≤ s ω)
    (hN : (N : ℝ) = (T : ℝ) + 3)
    (hlaw : P' {ω | (T : ℝ) < Real.log (s ω / r ω)} =
      P {ω | (T : ℝ≥0∞) < hitDrift B μ a ω}) :
    P' {ω | N < (Finset.Icc (⌈Real.log (r ω) - 1⌉ : ℤ)
      (⌊Real.log (s ω) + 1⌋ : ℤ)).card} ≤
      ENNReal.ofReal (Real.exp (-((μ * u) ^ 2 / (2 * T)))) := by
  calc
    _ ≤ P' {ω | (N : ℝ) < Real.log (s ω / r ω) + 3} :=
      measure_log_scale_card_gt_le_of_ae P' r s N hr hrs
    _ = P' {ω | (T : ℝ) < Real.log (s ω / r ω)} := by
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [hN]
      constructor <;> intro h <;> linarith
    _ = P {ω | (T : ℝ≥0∞) < hitDrift B μ a ω} := hlaw
    _ ≤ _ := measure_hitDrift_gt_centered_le_exp hB hcont hμ hu hTpos hT

end LatticeProb
