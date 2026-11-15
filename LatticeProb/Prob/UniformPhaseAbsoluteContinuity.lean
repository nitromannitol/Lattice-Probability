import LatticeProb.Prob.UniformModShift
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! # Absolute continuity for supported phase laws -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A Lebesgue-absolutely-continuous measure supported on a positive mesh
interval is absolutely continuous with respect to the uniform phase law. -/
theorem absolutelyContinuous_uniformIco_of_supported {p : ℝ}
    {Q : Measure ℝ} (hQ : Q ≪ volume)
    (hs : ∀ᵐ x ∂Q, x ∈ Icc (0 : ℝ) p) : Q ≪ uniformIco p := by
  have hne : ∀ᵐ x ∂Q, x ≠ p := hQ.ae_le (Measure.ae_ne volume p)
  have hmem : ∀ᵐ x ∂Q, x ∈ Ico (0 : ℝ) p := by
    filter_upwards [hs, hne] with x hx hn
    exact ⟨hx.1, lt_of_le_of_ne hx.2 hn⟩
  have hr : Q ≪ (volume : Measure ℝ).restrict (Ico 0 p) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hmem]
    exact hQ.restrict _
  have hc : ((volume : Measure ℝ) (Ico 0 p))⁻¹ ≠ 0 := by
    rw [Real.volume_Ico, sub_zero]
    exact ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  exact hr.trans (by
    unfold uniformIco ProbabilityTheory.cond
    exact Measure.absolutelyContinuous_smul hc)

/-- Product domination preserves almost-everywhere measurability of the same
joint map when the phase law is changed. -/
theorem aemeasurable_prod_of_uniformIco {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {P : Measure Ω} {Q : Measure ℝ} [SFinite Q] {p : ℝ}
    (hp : 0 < p) (hQ : Q ≪ volume)
    (hs : ∀ᵐ x ∂Q, x ∈ Icc (0 : ℝ) p) {f : Ω × ℝ → E}
    (hf : AEMeasurable f (P.prod (uniformIco p))) : AEMeasurable f (P.prod Q) := by
  let : IsProbabilityMeasure (uniformIco p) := isProbabilityMeasure_uniformIco hp
  exact hf.mono_ac (Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
    (absolutelyContinuous_uniformIco_of_supported hQ hs))

end LatticeProb
