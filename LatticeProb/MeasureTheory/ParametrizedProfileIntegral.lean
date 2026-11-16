import LatticeProb.MeasureTheory.UpperSemicontinuousProfileIntegral
import Mathlib.Topology.Sequences

/-! # Upper semicontinuity of parametrized profile integrals -/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LatticeProb

/-- A bounded upper semicontinuous profile cost has an upper semicontinuous
integral on any sequential space whose convergent sequences give convergence
in measure of the associated measurable profiles. -/
theorem upperSemicontinuous_lintegral_profile_cost
    {α E Z : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [TopologicalSpace Z] [SequentialSpace Z]
    {μ : Measure α} [IsFiniteMeasure μ]
    (c : α × E → ℝ≥0∞) (hc : Measurable c)
    (husc : ∀ x, UpperSemicontinuous (fun e => c (x, e)))
    (hbound : ∀ x e, c (x, e) ≤ 1)
    (f : Z → α → E) (hf : ∀ z, Measurable (f z))
    (hconv : ∀ (u : ℕ → Z) z, Tendsto u atTop (𝓝 z) →
      TendstoInMeasure μ (fun n => f (u n)) atTop (f z)) :
    UpperSemicontinuous (fun z => ∫⁻ x, c (x, f z x) ∂μ) := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  apply IsSeqClosed.isClosed
  intro u z hu huz
  have hlim := limsup_lintegral_cost_le_of_tendstoInMeasure c hc husc hbound
    (fun n => f (u n)) (f z) (fun n => hf (u n)) (hconv u z huz)
  have ha : a ≤ limsup (fun n => ∫⁻ x, c (x, f (u n) x) ∂μ) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall hu)
  exact ha.trans hlim

/-- The parametrized profile cost is measurable for any measurable structure
containing the open sets of the parameter space. -/
theorem measurable_lintegral_profile_cost
    {α E Z : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [TopologicalSpace Z] [SequentialSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    {μ : Measure α} [IsFiniteMeasure μ]
    (c : α × E → ℝ≥0∞) (hc : Measurable c)
    (husc : ∀ x, UpperSemicontinuous (fun e => c (x, e)))
    (hbound : ∀ x e, c (x, e) ≤ 1)
    (f : Z → α → E) (hf : ∀ z, Measurable (f z))
    (hconv : ∀ (u : ℕ → Z) z, Tendsto u atTop (𝓝 z) →
      TendstoInMeasure μ (fun n => f (u n)) atTop (f z)) :
    Measurable (fun z => ∫⁻ x, c (x, f z x) ∂μ) :=
  (upperSemicontinuous_lintegral_profile_cost c hc husc hbound f hf hconv).measurable

end LatticeProb
