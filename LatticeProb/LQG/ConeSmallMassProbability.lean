import LatticeProb.LQG.ConeSmallMassRadius
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeZero
import Mathlib.MeasureTheory.Integral.Indicator

/-! # Probability tails for small quantum-cone scales -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open MatedCRTHarmonic.CellScaling MatedCRTHarmonic
open scoped NNReal

namespace LatticeProb

/-- Along positive masses tending to zero, the probability that the cone scale
exceeds any fixed positive threshold tends to zero. -/
theorem tendsto_measure_coneScale_gt_zero {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {γ α : ℝ}
    (hγ : 0 < γ) (hα : α < lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝[>] 0)) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => P {ω | a < coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n)})
      atTop (𝓝 0) := by
  obtain ⟨W, hWm, _, _, hW⟩ := IGLaw.exists_radialPath_alpha (γ := γ) (α := α)
    (sub_pos.mpr hα) (X := fun _ => (0 : LQGMetric.DistC))
    (ηL := fun _ => ()) hB hB'
    (indepFun_const_left _ _) (indepFun_const_left _ _)
  have hm (n : ℕ) : AEMeasurable
      (fun ω => coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n)) P := by
    have hmeas : Measurable (fun ω => Real.exp
        (ConeScaling.lastLevel (lqgQ γ) (γ⁻¹ * Real.log (b n)) (W ω))) :=
      Real.measurable_exp.comp ((ConeScaling.measurable_lastLevel _ _).comp hWm)
    apply hmeas.aemeasurable.congr
    filter_upwards [hW] with ω hω
    unfold coneScale ConeScaling.lastLevel coneLogRadial
    simp only [hω]
  let E : ℕ → Set Ω := fun n => {ω | a < coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n)}
  have hE : ∀ n, NullMeasurableSet (E n) P := fun n =>
    nullMeasurableSet_lt measurable_const.aemeasurable (hm n)
  have heq : ∀ᵐ ω ∂P, ∀ n, ω ∈ toMeasurable P (E n) ↔ ω ∈ E n := by
    rw [ae_all_iff]
    intro n
    filter_upwards [(hE n).toMeasurable_ae_eq] with ω heqω
    exact iff_of_eq heqω
  have hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∈ toMeasurable P (E n) ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [ae_tendsto_coneScale_small_mass hγ hα hB hB', heq] with ω hω heqω
    have hn := (hω.comp hb).eventually (eventually_lt_nhds ha)
    filter_upwards [hn] with n hn
    rw [heqω n]
    change (a < coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n)) ↔ False
    exact iff_false_intro (not_lt.mpr hn.le)
  simpa [E] using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := P) atTop (A := ∅) MeasurableSet.empty (fun n => measurableSet_toMeasurable P _) hlim

end LatticeProb
