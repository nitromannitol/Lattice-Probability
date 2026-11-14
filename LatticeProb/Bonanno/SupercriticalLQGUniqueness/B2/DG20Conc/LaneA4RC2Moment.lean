/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RC2Moment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RC2Tail

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA4R_aemeasurable_finset_sup {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (I : Finset ι) {U : ι → Ω → ℝ≥0∞} (hU : ∀ b, AEMeasurable (U b) P) :
    AEMeasurable (fun ω => I.sup fun b => U b ω) P := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sup_empty]; exact aemeasurable_const
  | insert a s _ ih =>
      simp only [Finset.sup_insert]
      exact (hU a).sup ih

theorem laneA4R_recip_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {L : Ω → ℝ} (hLm : Measurable L) (hL : ∀ ω, 0 < L ω)
    {τ c x₀ : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hx₀ : 0 ≤ x₀) {rate : ℝ → ℝ}
    (htail : ∀ v, x₀ < v → P {ω | L ω < (Real.exp v)⁻¹ * c} ≤ ENNReal.ofReal (rate v))
    (hrate : ∀ v, x₀ < v →
      2 * Real.exp (τ * (v + 1)) * rate v ≤ Real.exp (-(τ * (v + 1)) / 2)) :
    ∫⁻ ω, ENNReal.ofReal (L ω)⁻¹ ^ τ ∂P ≤
      ENNReal.ofReal (c⁻¹ ^ τ * (Real.exp (τ * (x₀ + 1)) + 1)) := by
  refine laneA4R_rpow_lintegral_le_of_lt_tail
    (ENNReal.measurable_ofReal.comp hLm.inv).aemeasurable hτ (inv_pos.mpr hc) hx₀
    fun v hv => ?_
  have hsub : {ω | ENNReal.ofReal (c⁻¹ * Real.exp v) < ENNReal.ofReal (L ω)⁻¹} ⊆
      {ω | L ω < (Real.exp v)⁻¹ * c} := by
    intro ω hω
    have h := (ENNReal.ofReal_lt_ofReal_iff'.mp hω).1
    have hLω := hL ω
    have hpos : 0 < c⁻¹ * Real.exp v := by positivity
    have := (lt_inv_comm₀ hpos hLω).mp h
    simpa [mul_inv, mul_comm] using this
  have hfin : 2 * Real.exp (τ * (v + 1)) * (ENNReal.ofReal (rate v)).toReal ≤
      Real.exp (-(τ * (v + 1)) / 2) := by
    rcases le_total 0 (rate v) with h0 | h0
    · rw [ENNReal.toReal_ofReal h0]; exact hrate v hv
    · rw [ENNReal.ofReal_of_nonpos h0, ENNReal.toReal_zero, mul_zero]; positivity
  calc 2 * Real.exp (τ * (v + 1)) *
        (P {ω | ENNReal.ofReal (c⁻¹ * Real.exp v) < ENNReal.ofReal (L ω)⁻¹}).toReal
      ≤ 2 * Real.exp (τ * (v + 1)) * (ENNReal.ofReal (rate v)).toReal := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (P {ω | ENNReal.ofReal (c⁻¹ * Real.exp v) < ENNReal.ofReal (L ω)⁻¹}).toReal
            ≤ (P {ω | L ω < (Real.exp v)⁻¹ * c}).toReal :=
              ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
          _ ≤ (ENNReal.ofReal (rate v)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail v hv)
    _ ≤ Real.exp (-(τ * (v + 1)) / 2) := hfin

theorem laneA4R_sup_moment {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (I : Finset ι) {U : ι → Ω → ℝ≥0∞}
    (hU : ∀ b, AEMeasurable (U b) P)
    {τ s x₀ : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hx₀ : 0 ≤ x₀) {rate : ℝ → ℝ}
    (htail : ∀ v, x₀ < v →
      P {ω | ∃ b ∈ I, ENNReal.ofReal (Real.exp v * s) < U b ω} ≤ ENNReal.ofReal (rate v))
    (hrate : ∀ v, x₀ < v →
      2 * Real.exp (τ * (v + 1)) * rate v ≤ Real.exp (-(τ * (v + 1)) / 2)) :
    ∫⁻ ω, (I.sup fun b => U b ω) ^ τ ∂P ≤
      ENNReal.ofReal (s ^ τ * (Real.exp (τ * (x₀ + 1)) + 1)) := by
  refine laneA4R_rpow_lintegral_le_of_lt_tail (laneA4R_aemeasurable_finset_sup I hU) hτ hs hx₀
    fun v hv => ?_
  have hsub : {ω | ENNReal.ofReal (s * Real.exp v) < I.sup fun b => U b ω} ⊆
      {ω | ∃ b ∈ I, ENNReal.ofReal (Real.exp v * s) < U b ω} := by
    intro ω hω
    obtain ⟨b, hb, hlt⟩ := Finset.lt_sup_iff.mp (show ENNReal.ofReal (s * Real.exp v) <
      I.sup fun b => U b ω from hω)
    exact ⟨b, hb, by rwa [mul_comm]⟩
  have hfin : 2 * Real.exp (τ * (v + 1)) * (ENNReal.ofReal (rate v)).toReal ≤
      Real.exp (-(τ * (v + 1)) / 2) := by
    rcases le_total 0 (rate v) with h0 | h0
    · rw [ENNReal.toReal_ofReal h0]; exact hrate v hv
    · rw [ENNReal.ofReal_of_nonpos h0, ENNReal.toReal_zero, mul_zero]; positivity
  calc 2 * Real.exp (τ * (v + 1)) *
        (P {ω | ENNReal.ofReal (s * Real.exp v) < I.sup fun b => U b ω}).toReal
      ≤ 2 * Real.exp (τ * (v + 1)) * (ENNReal.ofReal (rate v)).toReal := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (P {ω | ENNReal.ofReal (s * Real.exp v) < I.sup fun b => U b ω}).toReal
            ≤ (P {ω | ∃ b ∈ I, ENNReal.ofReal (Real.exp v * s) < U b ω}).toReal :=
              ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
          _ ≤ (ENNReal.ofReal (rate v)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail v hv)
    _ ≤ Real.exp (-(τ * (v + 1)) / 2) := hfin

end SupercriticalLQGUniqueness.B2.DG20Conc
