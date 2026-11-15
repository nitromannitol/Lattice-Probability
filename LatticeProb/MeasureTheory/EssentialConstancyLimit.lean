import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Essential constancy and convergence in measure -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace LatticeProb

/-- A limit in measure of almost everywhere constant functions is almost everywhere constant. -/
theorem ae_constant_of_tendstoInMeasure
    {α E : Type*} [MeasurableSpace α] [MetricSpace E]
    (μ : Measure α) (hμ : μ ≠ 0) (f : ℕ → α → E) (g : α → E)
    (hfg : TendstoInMeasure μ f atTop g)
    (hf : ∀ n, ∃ c : E, ∀ᵐ x ∂μ, f n x = c) :
    ∃ c : E, ∀ᵐ x ∂μ, g x = c := by
  classical
  choose c hc using hf
  obtain ⟨ns, -, hlim⟩ := hfg.exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, f (ns n) x = c (ns n) :=
    ae_all_iff.mpr fun n => hc (ns n)
  have hgood : ∀ᵐ x ∂μ, Tendsto (fun n => f (ns n) x) atTop (𝓝 (g x)) ∧
      ∀ n, f (ns n) x = c (ns n) := hlim.and hall
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  obtain ⟨x, hx⟩ := hgood.exists
  refine ⟨g x, hgood.mono ?_⟩
  intro y hy
  apply tendsto_nhds_unique hy.1
  convert hx.1 using 1
  ext n
  exact (hy.2 n).trans (hx.2 n).symm

end LatticeProb
