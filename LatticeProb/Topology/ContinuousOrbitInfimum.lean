import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Semicontinuity.Basic

/-! # Infima of continuous parametrized comparisons -/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace LatticeProb

/-- A continuous two-sided comparison has the same infimum when both parameters
    range over a fixed dense sequence. -/
theorem iInf_comparison_eq_iInf_dense
    {Z P X : Type*} [TopologicalSpace Z] [TopologicalSpace P] [TopologicalSpace X]
    (u : ℕ → P) (hu : DenseRange u) (A B : Z × P → X)
    (c : X × X → ℝ≥0∞) (hA : Continuous A) (hB : Continuous B)
    (hc : Continuous c) (z : Z) :
    (⨅ p, ⨅ q, c (A (z, p), B (z, q))) =
      ⨅ n, ⨅ m, c (A (z, u n), B (z, u m)) := by
  let f : P × P → ℝ≥0∞ := fun v => c (A (z, v.1), B (z, v.2))
  have hf : Continuous f := hc.comp
    ((hA.comp (continuous_const.prodMk continuous_fst)).prodMk
      (hB.comp (continuous_const.prodMk continuous_snd)))
  have h := (hu.prodMap hu).ciInf hf
    (show BddBelow (Set.range f) from ⟨⊥, fun _ _ => bot_le⟩)
  rw [iInf_subtype'', iInf_range] at h
  simpa only [f, Prod.map_apply, iInf_prod] using h.symm

/-- The infimum over both parameter choices is upper semicontinuous. -/
theorem upperSemicontinuous_iInf_comparison
    {Z P X : Type*} [TopologicalSpace Z] [TopologicalSpace P] [TopologicalSpace X]
    (A B : Z × P → X) (c : X × X → ℝ≥0∞)
    (hA : Continuous A) (hB : Continuous B) (hc : Continuous c) :
    UpperSemicontinuous (fun z => ⨅ p, ⨅ q, c (A (z, p), B (z, q))) := by
  apply upperSemicontinuous_iInf
  intro p
  apply upperSemicontinuous_iInf
  intro q
  exact (hc.comp ((hA.comp (continuous_id.prodMk continuous_const)).prodMk
    (hB.comp (continuous_id.prodMk continuous_const)))).upperSemicontinuous

/-- The infimum over both parameter choices is measurable on a second-countable
    nonempty parameter space. -/
theorem measurable_iInf_comparison
    {Z P X : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace P] [SecondCountableTopology P] [Nonempty P] [TopologicalSpace X]
    (A B : Z × P → X) (c : X × X → ℝ≥0∞)
    (hA : Continuous A) (hB : Continuous B) (hc : Continuous c) :
    Measurable (fun z => ⨅ p, ⨅ q, c (A (z, p), B (z, q))) := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq P
  have heq : (fun z => ⨅ p, ⨅ q, c (A (z, p), B (z, q))) =
      fun z => ⨅ n, ⨅ m, c (A (z, u n), B (z, u m)) := by
    funext z
    exact iInf_comparison_eq_iInf_dense u hu A B c hA hB hc z
  rw [heq]
  refine Measurable.iInf fun n => Measurable.iInf fun m => ?_
  exact (hc.comp ((hA.comp (continuous_id.prodMk continuous_const)).prodMk
    (hB.comp (continuous_id.prodMk continuous_const)))).measurable

end LatticeProb
