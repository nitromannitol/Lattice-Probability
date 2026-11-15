import LatticeProb.LQG.ConeAllLevelHitTail
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeScale

/-! # Hitting-time law for cone scale ratios -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.ConeScaling

/-- The logarithmic ratio of two cone scales is the increment of their radial
last-level times, on the event representing the cone by its radial path. -/
theorem ae_log_coneScale_ratio_eq {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α : ℝ} {B B' : ℝ≥0 → Ω → ℝ} {W : Ω → C(ℝ, ℝ)}
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t) (b₁ b₂ : ℝ) :
    ∀ᵐ ω ∂P, Real.log (CellScaling.coneScale γ α (fun s => B s ω)
        (fun s => B' s ω) b₂ / CellScaling.coneScale γ α (fun s => B s ω)
        (fun s => B' s ω) b₁) =
      lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b₂) (W ω) -
      lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b₁) (W ω) := by
  filter_upwards [hW] with ω hω
  rw [IGLaw.coneScale_eq_exp_lastLevel_alpha γ α b₂ hω,
    IGLaw.coneScale_eq_exp_lastLevel_alpha γ α b₁ hω,
    Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]

/-- The logarithmic ratio of cone scales at positive ordered parameters has
the law of a drifted Brownian first-passage time. -/
theorem map_ofReal_log_coneScale_ratio_eq_hitDrift
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < CellScaling.lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    {W : Ω → C(ℝ, ℝ)} (hWm : Measurable W)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t)
    {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb : b₁ < b₂) :
    P.map (fun ω => ENNReal.ofReal (Real.log (CellScaling.coneScale γ α
        (fun s => B s ω) (fun s => B' s ω) b₂ / CellScaling.coneScale γ α
        (fun s => B s ω) (fun s => B' s ω) b₁))) =
      P.map (LatticeProb.hitDrift (fun t ω => -B t ω) (CellScaling.lqgQ γ - α)
        (γ⁻¹ * Real.log b₂ - γ⁻¹ * Real.log b₁)) := by
  have hlevels : γ⁻¹ * Real.log b₁ < γ⁻¹ * Real.log b₂ :=
    mul_lt_mul_of_pos_left (Real.log_lt_log hb₁ hb) (inv_pos.mpr hγ)
  calc
    _ = P.map (fun ω => ENNReal.ofReal (lastLevel (CellScaling.lqgQ γ)
        (γ⁻¹ * Real.log b₂) (W ω) - lastLevel (CellScaling.lqgQ γ)
        (γ⁻¹ * Real.log b₁) (W ω))) := by
      apply Measure.map_congr
      filter_upwards [ae_log_coneScale_ratio_eq hW b₁ b₂] with ω hω
      rw [hω]
    _ = _ := map_ofReal_cone_lastLevel_increment_all_levels_eq_hitDrift
      hαQ hB hB' hBB' hWm hW hlevels

/-- The cone scale ratio inherits the centered two-sided first-passage bound. -/
theorem measure_log_coneScale_ratio_outside_centered_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < CellScaling.lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    {W : Ω → C(ℝ, ℝ)} (hWm : Measurable W)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t)
    {b₁ b₂ u : ℝ} (hb₁ : 0 < b₁) (hb : b₁ < b₂) (hu : 0 < u)
    {Tlo Thi : ℝ≥0} (hlo : 0 < Tlo)
    (hloval : (Tlo : ℝ) = (γ⁻¹ * Real.log b₂ - γ⁻¹ * Real.log b₁) /
      (CellScaling.lqgQ γ - α) - u)
    (hhi : 0 < Thi)
    (hhival : (Thi : ℝ) = (γ⁻¹ * Real.log b₂ - γ⁻¹ * Real.log b₁) /
      (CellScaling.lqgQ γ - α) + u) :
    P {ω | ENNReal.ofReal (Real.log (CellScaling.coneScale γ α
          (fun s => B s ω) (fun s => B' s ω) b₂ / CellScaling.coneScale γ α
          (fun s => B s ω) (fun s => B' s ω) b₁)) < (Tlo : ℝ≥0∞) ∨
        (Thi : ℝ≥0∞) < ENNReal.ofReal (Real.log (CellScaling.coneScale γ α
          (fun s => B s ω) (fun s => B' s ω) b₂ / CellScaling.coneScale γ α
          (fun s => B s ω) (fun s => B' s ω) b₁))} ≤
      ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - α) * u) ^ 2 / (2 * Tlo)))) +
      ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - α) * u) ^ 2 / (2 * Thi)))) := by
  have hlevels : γ⁻¹ * Real.log b₁ < γ⁻¹ * Real.log b₂ :=
    mul_lt_mul_of_pos_left (Real.log_lt_log hb₁ hb) (inv_pos.mpr hγ)
  calc
    _ ≤ P {ω | ENNReal.ofReal (lastLevel (CellScaling.lqgQ γ)
          (γ⁻¹ * Real.log b₂) (W ω) - lastLevel (CellScaling.lqgQ γ)
          (γ⁻¹ * Real.log b₁) (W ω)) < (Tlo : ℝ≥0∞) ∨
        (Thi : ℝ≥0∞) < ENNReal.ofReal (lastLevel (CellScaling.lqgQ γ)
          (γ⁻¹ * Real.log b₂) (W ω) - lastLevel (CellScaling.lqgQ γ)
          (γ⁻¹ * Real.log b₁) (W ω))} := by
      apply measure_mono_ae
      filter_upwards [ae_log_coneScale_ratio_eq hW b₁ b₂] with ω hω hevent
      simpa only [hω] using hevent
    _ ≤ _ := measure_cone_lastLevel_increment_all_levels_outside_centered_le
      hαQ hB hB' hm hcont hBB' hWm hW hlevels hu hlo hloval hhi hhival

end MatedCRTHarmonic.ConeScaling
