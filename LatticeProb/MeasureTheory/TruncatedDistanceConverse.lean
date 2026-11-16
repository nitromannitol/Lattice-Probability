import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Integrated truncated distances under convergence in measure -/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal Topology

namespace LatticeProb

/-- On a finite measure space, convergence in measure forces the integrals of
truncated extended distances to vanish. -/
theorem tendsto_lintegral_min_edist_of_tendstoInMeasure
    {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] (f : ℕ → α → E) (g : α → E)
    (hmeas : ∀ n, AEMeasurable (fun x => min 1 (edist (f n x) (g x))) μ)
    (h : TendstoInMeasure μ f atTop g) :
    Tendsto (fun n => ∫⁻ x, min 1 (edist (f n x) (g x)) ∂μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ks, _, hconv⟩ := (h.comp hns).exists_seq_tendsto_ae
  refine ⟨ks, ?_⟩
  have hi := tendsto_lintegral_of_dominated_convergence' (μ := μ) (f := fun _ => 0) (fun _ => 1)
    (fun n => hmeas (ns (ks n)))
    (fun n => ae_of_all _ fun x => min_le_left _ _)
    (by simp) ?_
  · simpa using hi
  · filter_upwards [hconv] with x hx
    have hd := hx.edist (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => g x) atTop (𝓝 (g x)))
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞))
      atTop (𝓝 1)).min hd

end LatticeProb
