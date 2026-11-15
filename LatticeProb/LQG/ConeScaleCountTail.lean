import LatticeProb.LQG.ConeRadiusRatioHit
import LatticeProb.LQG.ConeScaleOrder
import LatticeProb.Prob.BrownianDriftHitScaleTransfer

/-! # Upper tail for the number of cone logarithmic scales -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.ConeScaling

/-- A centered hitting-time bound controls the number of padded integer scales
between two positive-parameter alpha-cone radii. -/
theorem measure_cone_scale_count_gt_le_exp
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
    (N : ℕ) (hN : (T : ℝ) + 3 ≤ (N : ℝ)) :
    P {ω | N < (Finset.Icc
      (⌈Real.log (CellScaling.coneScale γ α (fun s => B s ω) (fun s => B' s ω) b₁) - 1⌉ : ℤ)
      (⌊Real.log (CellScaling.coneScale γ α (fun s => B s ω) (fun s => B' s ω) b₂) + 1⌋ : ℤ)).card} ≤
    ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - α) * u) ^ 2 / (2 * T)))) := by
  let r : Ω → ℝ := fun ω => CellScaling.coneScale γ α (fun s => B s ω) (fun s => B' s ω) b₁
  let s : Ω → ℝ := fun ω => CellScaling.coneScale γ α (fun s => B s ω) (fun s => B' s ω) b₂
  let X : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.log (s ω / r ω))
  let Y : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b₂) (W ω) -
      lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b₁) (W ω))
  let Z : Ω → ℝ≥0∞ := LatticeProb.hitDrift (fun t ω => -B t ω)
    (CellScaling.lqgQ γ - α) (γ⁻¹ * Real.log b₂ - γ⁻¹ * Real.log b₁)
  have hr : ∀ᵐ ω ∂P, 0 < r ω := by
    filter_upwards [hW] with ω hω
    dsimp [r]
    rw [IGLaw.coneScale_eq_exp_lastLevel_alpha γ α b₁ hω]
    exact Real.exp_pos _
  have hrs : ∀ᵐ ω ∂P, r ω ≤ s ω := by
    filter_upwards [ae_coneScale_strictMono hγ hαQ hB hB' hW] with ω hω
    exact (hω b₁ b₂ hb₁ hb).le
  have hXY : X =ᵐ[P] Y := by
    filter_upwards [ae_log_coneScale_ratio_eq hW b₁ b₂] with ω hω
    dsimp [X, Y, r, s]
    rw [hω]
  have hYm : Measurable Y := ENNReal.measurable_ofReal.comp
    (((measurable_lastLevel _ _).comp hWm).sub ((measurable_lastLevel _ _).comp hWm))
  have hZm : Measurable Z := LatticeProb.measurable_of_isStoppingTime_enn
    (LatticeProb.isStoppingTime_hitDrift_brownian (fun t => (hm t).neg)
      (fun ω => (hcont ω).neg) _ _)
  have hmap : P.map Y = P.map Z := by
    calc
      P.map Y = P.map X := (Measure.map_congr hXY).symm
      _ = P.map Z := map_ofReal_log_coneScale_ratio_eq_hitDrift hγ hαQ hB hB' hBB' hWm hW hb₁ hb
  have hlaw : P {ω | (T : ℝ≥0∞) < Y ω} = P {ω | (T : ℝ≥0∞) < Z ω} := by
    change P (Y ⁻¹' Set.Ioi (T : ℝ≥0∞)) = P (Z ⁻¹' Set.Ioi (T : ℝ≥0∞))
    rw [← Measure.map_apply hYm measurableSet_Ioi, ← Measure.map_apply hZm measurableSet_Ioi, hmap]
  calc
    _ ≤ P {ω | (N : ℝ) < Real.log (s ω / r ω) + 3} :=
      LatticeProb.measure_log_scale_card_gt_le_of_ae P r s N hr hrs
    _ ≤ P {ω | (T : ℝ≥0∞) < Y ω} := by
      apply measure_mono_ae
      filter_upwards [hXY] with ω hω he
      have hlog : (T : ℝ) < Real.log (s ω / r ω) := by linarith
      have hX : (T : ℝ≥0∞) < X ω := by
        dsimp only [X]
        rw [← ENNReal.ofReal_coe_nnreal]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hlog
      simpa only [hω] using hX
    _ = P {ω | (T : ℝ≥0∞) < Z ω} := hlaw
    _ ≤ _ := LatticeProb.measure_hitDrift_gt_centered_le_exp hB.neg
      (fun ω => (hcont ω).neg) (sub_pos.mpr hαQ) hu hTpos hT

end MatedCRTHarmonic.ConeScaling
