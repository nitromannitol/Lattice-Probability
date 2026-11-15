import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! # Independent random parameters -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb

/-- A uniform bound on the sections of a jointly measurable event remains valid
when its parameter is chosen independently from the random element. -/
theorem measure_mem_of_indepFun_le
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {R : Ω → α} {Y : Ω → β} (hR : Measurable R) (hY : Measurable Y)
    (hRY : IndepFun R Y P) (E : Set (α × β)) (hE : MeasurableSet E)
    (S : Set α) (hS : MeasurableSet S) (hRS : ∀ᵐ ω ∂P, R ω ∈ S)
    (p : ℝ≥0∞) (hbound : ∀ r ∈ S, P {ω | (r, Y ω) ∈ E} ≤ p) :
    P {ω | (R ω, Y ω) ∈ E} ≤ p := by
  have hjoint := hRY.map_prod_eq_prod_map_map hR.aemeasurable hY.aemeasurable
  have hgood : ∀ᵐ r ∂P.map R, r ∈ S := (ae_map_iff hR.aemeasurable hS).2 hRS
  have hsections : ∀ᵐ r ∂P.map R, (P.map Y) (Prod.mk r ⁻¹' E) ≤ p := by
    filter_upwards [hgood] with r hr
    rw [Measure.map_apply hY (hE.preimage (measurable_prodMk_left))]
    exact hbound r hr
  calc
    P {ω | (R ω, Y ω) ∈ E} = (P.map R).prod (P.map Y) E := by
      rw [← hjoint, Measure.map_apply (hR.prodMk hY) hE]
      rfl
    _ = ∫⁻ r, (P.map Y) (Prod.mk r ⁻¹' E) ∂P.map R := Measure.prod_apply hE
    _ ≤ ∫⁻ _r, p ∂P.map R := lintegral_mono_ae hsections
    _ = p := by simp

end LatticeProb
