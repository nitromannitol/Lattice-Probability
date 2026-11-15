import LatticeProb.LQG.ConeInnerWindowScaling
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeMoment

/-! # Cone mass and inner-window power tails -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal

namespace LatticeProb

/-- Positive moments give a power-law upper bound for the cone unit-ball mass. -/
theorem cone_unit_ball_mass_power_tail
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (p : ℝ) (hp : 0 < p) (hpγ : p < 4 / γ ^ 2 - 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t : ℝ, 0 < t →
      P {ω | ENNReal.ofReal t ≤ CellScaling.lqgArea γ
        (CellScaling.coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω))
        (ball 0 1)} ≤ C * ENNReal.ofReal (t ^ (-p)) := by
  let R := MoTInput.coneRealizationOfCoupling D hstd hγ
  have hM := GMCFacts.areaBallMoment_holds R
  change AEMeasurable (fun ω => CellScaling.lqgArea γ
    (CellScaling.coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω))
      (ball 0 1)) P ∧ _ at hM
  let Z : Ω → ℝ≥0∞ := fun ω => CellScaling.lqgArea γ
    (CellScaling.coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω)) (ball 0 1)
  have hZm : AEMeasurable Z P := hM.1
  have hmoment : ∫⁻ ω, Z ω ^ p ∂P < ⊤ := hM.2 p hp hpγ
  refine ⟨∫⁻ ω, Z ω ^ p ∂P, hmoment, fun t ht => ?_⟩
  have htpos : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hsub : {ω | ENNReal.ofReal t ≤ Z ω} ⊆
      {ω | ENNReal.ofReal (t ^ p) ≤ Z ω ^ p} := by
    intro ω hω
    have h := ENNReal.rpow_le_rpow hω hp.le
    rwa [ENNReal.ofReal_rpow_of_nonneg ht.le hp.le] at h
  calc
    _ ≤ P {ω | ENNReal.ofReal (t ^ p) ≤ Z ω ^ p} := measure_mono hsub
    _ ≤ (∫⁻ ω, Z ω ^ p ∂P) / ENNReal.ofReal (t ^ p) :=
      meas_ge_le_lintegral_div (hZm.pow_const p) (ENNReal.ofReal_pos.mpr htpos).ne'
        ENNReal.ofReal_ne_top
    _ = _ := by
      rw [div_eq_mul_inv, Real.rpow_neg ht.le, ENNReal.ofReal_inv_of_pos htpos]

/-- A cone-scale inner-window containment probability has a positive-power bound. -/
theorem cone_inner_window_containment_power_tail
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    (p : ℝ) (hp : 0 < p) (hpγ : p < 4 / γ ^ 2 - 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ b w : ℝ, 0 < b → 0 < w →
      P {ω | let L := CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b
        η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∨
          η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L} ≤
      C * ENNReal.ofReal ((b⁻¹ * (w / 2)) ^ (-p)) := by
  obtain ⟨C, hC, htail⟩ := cone_unit_ball_mass_power_tail D hstd hγ p hp hpγ
  refine ⟨C, hC, fun b w hb hw => ?_⟩
  have ht : 0 < b⁻¹ * (w / 2) := mul_pos (inv_pos.mpr hb) (by positivity)
  have hbound := measure_cone_inner_window_containment_le_unit_mass_tail D hstd hγ μ hμ b w hb hw.le
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hb.le)] at hbound
  exact hbound.trans (htail _ ht)

end LatticeProb
