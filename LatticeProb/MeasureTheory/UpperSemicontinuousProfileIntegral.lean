import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Basic

/-! # Upper semicontinuous integral comparisons -/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal Topology

namespace LatticeProb

/-- A bounded upper semicontinuous cost, possibly depending on the integration
variable, satisfies a reverse-Fatou bound along almost everywhere convergent
measurable profiles. -/
theorem limsup_lintegral_cost_le_of_ae_tendsto
    {α E : Type*} [MeasurableSpace α] [TopologicalSpace E] [MeasurableSpace E]
    {μ : Measure α} [IsFiniteMeasure μ]
    (c : α × E → ℝ≥0∞) (hc : Measurable c)
    (husc : ∀ x, UpperSemicontinuous (fun z => c (x, z)))
    (hbound : ∀ x z, c (x, z) ≤ 1)
    (f : ℕ → α → E) (g : α → E) (hf : ∀ n, Measurable (f n))
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    limsup (fun n => ∫⁻ x, c (x, f n x) ∂μ) atTop ≤
      ∫⁻ x, c (x, g x) ∂μ := by
  have hmeas : ∀ n, Measurable (fun x => c (x, f n x)) :=
    fun n => hc.comp (measurable_id.prodMk (hf n))
  calc
    _ ≤ ∫⁻ x, limsup (fun n => c (x, f n x)) atTop ∂μ :=
      limsup_lintegral_le 1 hmeas (fun n => ae_of_all _ (fun x => hbound x (f n x)))
        (by simp)
    _ ≤ _ := lintegral_mono_ae (hconv.mono fun x hx =>
      (hx.limsup_comp_le_limsup).trans ((husc x).limsup_le (g x)))

/-- The same bound holds for convergence in measure. -/
theorem limsup_lintegral_cost_le_of_tendstoInMeasure
    {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    {μ : Measure α} [IsFiniteMeasure μ]
    (c : α × E → ℝ≥0∞) (hc : Measurable c)
    (husc : ∀ x, UpperSemicontinuous (fun z => c (x, z)))
    (hbound : ∀ x z, c (x, z) ≤ 1)
    (f : ℕ → α → E) (g : α → E) (hf : ∀ n, Measurable (f n))
    (hconv : TendstoInMeasure μ f atTop g) :
    limsup (fun n => ∫⁻ x, c (x, f n x) ∂μ) atTop ≤
      ∫⁻ x, c (x, g x) ∂μ := by
  by_contra h
  have hlt := lt_of_not_ge h
  obtain ⟨y, hy, hy'⟩ := exists_between hlt
  have hfreq : ∃ᶠ n in atTop, y < ∫⁻ x, c (x, f n x) ∂μ :=
    frequently_lt_of_lt_limsup (h := hy')
  obtain ⟨φ, hφ, hφy⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, _, hψconv⟩ := (hconv.comp hφ.tendsto_atTop).exists_seq_tendsto_ae
  have hle := limsup_lintegral_cost_le_of_ae_tendsto c hc husc hbound
    (fun n => f (φ (ψ n))) g (fun n => hf _) hψconv
  have hy_le : y ≤ limsup (fun n => ∫⁻ x, c (x, f (φ (ψ n)) x) ∂μ) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall (fun n => (hφy (ψ n)).le))
  exact (not_le_of_gt hy) (hy_le.trans hle)

end LatticeProb
